#!/usr/bin/env python
"""
    Wrapper script for VAC

ChangeLog:
    2016.11.21   Based on old script vac.sh

"""
import argparse
import atexit
import re
import sys
import os
from os import path
import signal
import subprocess
import tempfile
import shutil
import time
from functools import reduce
import logging

ENCODING = "ISO-8859-1"

VACDESCRIPTION = '''\
* *               VAC 2.0 - Verifier of Access Control                * *

'''

# * *                                                                   * *
# * *            Anna Lisa Ferrara (1), P. Madhusudan (2),              * *
# * *           Truc L. Nguyen (3), and Gennaro Parlato (3).            * *
# * *                                                                   * *
# * * (1) University of Bristol (UK), (2) University of Illinois (USA), * *
# * *               and (3) University of Southampton (UK)              * *

EPILOG = '''
VAC without any option runs the default option:
it first performs the over-approximated analysis using {overapprox};
if a proof cannot be provided, VAC runs the under-approximated analysis using {underapprox};
if no proof is found then VAC runs the precise analysis using {precise}.
Finally if the target role is reachable and the user required it, CBMC (unwind set to {counter_unwind})
is used to find a counterexample.
'''


class Log(object):
    def __init__(self):
        # configure how logging should be done
        logging.addLevelName(self.EXACT_RESULT, "EXACT_RESULT")
        logging.addLevelName(self.RESULT, "RESULT")
        logging.addLevelName(self.PROFILE, "PROFILE")
        pass
    CRITICAL = 50
    ERROR = 40
    EXACT_RESULT = 39
    RESULT = 38
    WARNING = 30
    INFO = 20
    PROFILE = 15
    DEBUG = 10

    colors = {
        'white': '\x1b[0m',
        'red': '\x1b[91m',
        'green': '\x1b[92m',
        'yellow': '\x1b[93m',
        'blue': '\x1b[94m',
        'purple': '\x1b[95m',
        'cyan': '\x1b[96m'
    }

    colorize = False

    def log(self, level, msg):
        if not self.colorize:
            logging.log(level, msg)
        else:
            color = None
            if level == self.CRITICAL:
                color = self.colors['red']
            elif level == self.ERROR:
                color = self.colors['red']
            elif level == self.EXACT_RESULT:
                color = self.colors['green']
            elif level == self.WARNING:
                color = self.colors['yellow']
            # elif level == self.INFO:
            #     color = self.colors['white']
            elif level == self.PROFILE:
                color = self.colors['cyan']
            # elif level == self.DEBUG:
            #     color = self.colors['white']
            if color is None:
                logging.log(level, msg)
            else:
                logging.log(level, "{}{}{}".format(color, msg, self.colors['white']))

    def critical(self, msg):  # , *args, **kwargs):
        self.log(self.CRITICAL, msg)  # , args, kwargs)

    def error(self, msg):  # , *args, **kwargs):
        self.log(self.ERROR, msg)  # , args, kwargs)

    def exact_result(self, msg):
        self.log(self.EXACT_RESULT, msg)

    def result(self, msg):
        self.log(self.RESULT, msg)

    def warning(self, msg):  # , *args, **kwargs):
        self.log(self.WARNING, msg)  # , args, kwargs)

    def info(self, msg):  # , *args, **kwargs):
        self.log(self.INFO, msg)  # , args, kwargs)

    def profile(self, msg):  # , *args, **kwargs):
        self.log(self.PROFILE, msg)  # , args, kwargs)

    def debug(self, msg):  # , *args, **kwargs):
        self.log(self.DEBUG, msg)  # , args, kwargs)

    def exception(self, msg):  # , *args, **kwargs):
        # kwargs['exc_info'] = 1
        self.error(msg)  # , *args, **kwargs)
        # L.exception(msg, args, kwargs)

l = Log()


def exists(f, xs): return reduce(lambda s, x: s if s else f(x), xs, False)


def first(f, xs): return reduce(lambda s, x: x if s is None and f(x) else s, xs, None)


class UnexpectedError(Exception):
    msg = ""

    def __init__(self, msg):
        self.msg = msg


class MessageError(RuntimeError):
    message = None

    def __init__(self, message):
        self.message = message


def basename_wo_extension(fname):
    return '.'.join(os.path.basename(os.path.realpath(fname)).split('.')[:-1])


def file_name_wo_extension(fname):
    return '.'.join(os.path.realpath(fname).split('.')[:-1])


class Result:
    def __init__(self): pass

    class Safe:
        def __init__(self): pass

    class Unsafe:
        def __init__(self): pass

    class MaybeSafe:
        def __init__(self): pass

    class MaybeUnsafe:
        def __init__(self): pass

    class Error:
        def __init__(self): pass


def print_result(result):
    if result is Result.Safe:
        l.exact_result("The ARBAC policy is safe")
    elif result is Result.Unsafe:
        l.exact_result("The ARBAC policy is not safe")
    elif result is Result.MaybeSafe:
        l.result("The ARBAC policy may be safe")
    elif result is Result.MaybeUnsafe:
        l.result("The ARBAC policy may be unsafe")
    elif result is Result.Error:
        l.result("Error in translation or in this script :)")
    else:
        l.critical("Analysis returned unexpected value {}".format(result))


class Precision:
    def __init__(self): pass

    class Exact:
        def __init__(self): pass

    class OverApprox:
        def __init__(self): pass

    class UnderApprox:
        def __init__(self): pass


class Solver(object):
    name = None  # str
    tool_name = None  # str
    in_suffix = None  # str
    precision = None  # Precision For checking, but not required
    arguments = None  # str
    res_interp = None  # [(Result, [regex])]
    cmd_format = None  # format str
    runtime_arguments = None  # lambda :: () -> str
    translation_format = None  # str
    accepted_retcodes = None

    def __init__(self,
                 name,
                 tool_name,
                 in_suffix,
                 precision,
                 arguments,
                 res_interp,
                 translation_format,
                 runtime_arguments=None,
                 cmd_format="{tool_path}/{tool_name} {arguments} {in_file}",
                 accepted_retcodes={0}):
        self.name = name
        self.tool_name = tool_name
        self.in_suffix = in_suffix
        self.precision = precision
        self.arguments = arguments
        self.res_interp = res_interp
        self.cmd_format = cmd_format
        self.runtime_arguments = runtime_arguments
        self.translation_format = translation_format
        self.accepted_retcodes = accepted_retcodes
        
    def _get_command(self, input_file):
        cmd = self.cmd_format.format(
                tool_path=config.tool_dir,
                tool_name=self.tool_name,
                arguments="{} {}".format(
                    self.arguments,
                    self.runtime_arguments() if self.runtime_arguments is not None else ""),
                in_file=input_file)
        l.debug("Got command: {}".format(cmd))
        return cmd

    def _find_result(self, str_res):
        res_p = filter(lambda r_regex: exists(lambda reg: reg.search(str_res) is not None, r_regex[1]), self.res_interp)
        res = list(map(lambda r_regex: r_regex[0], res_p))
        if len(res) != 1:
            l.error("Got zero o more than one possible results:\n\t{}".format(str(res)))
            raise MessageError("Got zero o more than one possible results:\n\t{}".format(str(res)))
        else:
            # Paranoid checks
            ret = res[0]
            if self.precision is Precision.Exact and ret not in [Result.Safe, Result.Unsafe]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))
            if self.precision is Precision.OverApprox and ret not in [Result.Safe, Result.MaybeUnsafe]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))
            if self.precision is Precision.UnderApprox and ret not in [Result.MaybeSafe, Result.Unsafe]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))

            if ret is Result.Error:
                raise MessageError("Got result: {}.".format(ret))

            return ret

    def in_file_name(self):
        fname = "{}.{}".format(config.file_prefix, self.in_suffix)
        return fname

    def _execute(self, input_file):
        cmd = self._get_command(input_file)

        retcode, out, err = execute_cmd(cmd, self.name, self.accepted_retcodes)  # , input_file)

        # Check result
        result = self._find_result(out)

        return result

    def run(self):
        mucke = self.translation_format.lower() == "mucke"
        translate(config.simplified_file, self.translation_format, self.in_file_name(), mucke)
        return self._execute(self.in_file_name())


def execute_cmd(cmd, name=None, accepted_retcodes={0}):
    can_save = name is not None
    if name is None:
        name = cmd
    l.debug("Running {}".format(cmd))
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    out, err = out.decode(ENCODING), err.decode(ENCODING)
    retcode = p.wait()
    if retcode not in accepted_retcodes:
        l.warning("{} got return code {}".format(name, retcode))
    if err != u'':
        l.warning("{} got {}".format(name, err))
    if config.preserve_tool_answer and can_save:  # and input_file is not None:
        out_log = "{}_{}.log".format(config.file_prefix, name)
        out_err = "{}_{}.err".format(config.file_prefix, name)
        with open(out_log, 'w') as log_f:
            log_f.write("{}\n".format(cmd))
            log_f.write(out if out != u'' else "--- No output produced ---\n")
        with open(out_err, 'w') as err_f:
            err_f.write("{}\n".format(cmd))
            err_f.write(err if err != u'' else "--- No error produced ---\n")
    return retcode, out, err


def translate(in_file, translator_format, out_file, mucke=False):
    args = "--format {fmt} --out {out} {other}".format(
        fmt=translator_format,
        out=out_file,
        other="--formula {} --rounds {}".format(config.mucke_formula, config.mucke_rounds) if mucke else "")
    cmd = "{cmd_path}/translate {arguments} {in_file}".format(
        cmd_path=config.tool_dir,
        arguments="{}".format(args),
        in_file=in_file)
    l.debug("Got command: {}".format(cmd))
    retval, stdout, stderr = execute_cmd(cmd)
    if retval != 0 or stderr != u'':
        raise MessageError(
            "Translation went wrong. Error in file{f}:\n\tCmd: {c}\n\tReturn value: {r}\n\tStdout: {o}\n\tStderr: {e}".
            format(f=in_file,
                   r=retval,
                   o=stdout,
                   e=stderr,
                   c=cmd))
    return True


def simplify():
    if config.no_pruning:
        raise MessageError("Should not simplify if --no-pruning")
    else:
        l.info("=====> Simplification of the ARBAC policy =====>")
        args = "--debug {debug} --logfile {log} --out {out}".format(
            debug=config.simplified_debug,
            log=config.simplified_log,
            out=config.simplified_file)
        cmd = "{cmd_path}/simplify {arguments} {in_file}".format(
            cmd_path=config.tool_dir,
            arguments=args,
            in_file=config.infile)
        l.debug("Got command: {}".format(cmd))
        retval, stdout, stderr = execute_cmd(cmd)
        if retval != 0 or stderr != u'':
            raise MessageError(
                "Pruning went wrong. Error in file{f}:\n\tReturn value: {r}\n\tStdout: {o}\n\tStderr: {e}\n\tCmd: {c}".
                format(f=config.infile,
                       r=retval,
                       o=stdout,
                       e=stderr,
                       c=cmd))
        return True


# This should be enhanced
def build_counterexample():
    cbmc_in = "{}_counterExample.c".format(config.file_prefix)
    translate(config.simplified_file, "cbmc", cbmc_in)
    cbmc_cmd = "{}/cbmc --unwind {} --no-unwinding-assertions --xml-ui {}".format(
        config.tool_dir,
        config.counterexample_unwind,
        config.simplified_file)
    retval, out, err = execute_cmd(cbmc_cmd, "cbmc_counterexample")

    cbmc_xml = "{}_counterExample.xml".format(config.file_prefix)

    if False:  # check cbmc result
        pass

    with open(cbmc_xml, 'w') as f:
        f.write(out)

    counterexample_cmd = \
        "{dir}/counterexample --cbmc-xml {xml} --cbmc-input {cbmc_in} {other} {orig_input}".format(
            dir=config.tool_dir,
            xml=cbmc_xml,
            cbmc_in=cbmc_in,
            other="--simplified-policy {} --simplified-debug {}".
                  format(config.simplified_file, config.simplified_debug) if config.no_pruning else "",
            orig_input=config.infile)

    _, out, _ = execute_cmd(counterexample_cmd, "counter_example_generation")
    if out == u'':  # check better for counterexample
        l.warning("Could not find a counterexample")
        return None
    # l.info(out)
    return out


class Config(object):
    MUCKE_BDD_LIBS = ["abcd.so", "longbman.so", "cudd.a"]
    base_dir = None
    tool_dir = None
    preserve_tool_answer = None
    infile = None
    simplified_file = None
    simplified_log = None
    simplified_debug = None
    file_prefix = None
    working_dir = None
    preserve_artifacts = None
    no_pruning = None
    overapprox_backend = None
    underapprox_backend = None
    precise_backend = None
    backend = None
    unwind = None
    interproc_w_delay = None
    interproc_w_steps = None
    mucke_bddlib = None
    mucke_rounds = None
    mucke_formula = None
    show_counterexample = None
    counterexample_unwind = None
    print_pruned = None
    print_translated = None
    mohawk = None
    profile = None
    debug = None
    no_color = None
    verbose = None
    version = None
    args = None

    def __init__(self): pass

    def __prepare_parser(self):
        default_over_approx_backend = Backends.over_approx_backends_names[0]
        default_under_approx_backend = Backends.under_approx_backends_names[0]
        default_precise_backend = Backends.precise_backends_names[0]
        default_unwind = 15
        def_mucke_bdd = self.MUCKE_BDD_LIBS[0]
        default_mucke_rounds = 4
        default_interproc_w_delay = 1
        default_interproc_w_steps = 2

        parser = argparse.ArgumentParser(description=VACDESCRIPTION,
                                         epilog=EPILOG.format(overapprox=default_over_approx_backend,
                                                              underapprox=default_under_approx_backend,
                                                              precise=default_precise_backend,
                                                              counter_unwind=default_unwind),
                                         formatter_class=argparse.RawTextHelpFormatter,
                                         usage='./%(prog)s [options] input')
        parser.add_argument('infile', type=str, help='input policy')
        parser.add_argument('-d', '--working-dir',
                            metavar='X', dest='working_dir', type=str,
                            help="Works in X and do not remove intermediate artifact of the analysis")
        parser.add_argument('-g', '--preserve-tool-answer',
                            metavar='X', dest='preserve_tool_answer', default=False,
                            help="Preserve all tool answer saving to log files (requires --working-dir)")
        parser.add_argument('-n', '--no-pruning',
                            action='store_true', default=False, dest='no_pruning',
                            help='no simplification procedure (default No)')
        parser.add_argument('-o', '--overapprox-backend',
                            metavar='X', type=str, dest='overapprox_backend', default=default_over_approx_backend,
                            help='backend for the over-approximate analysis if required {list} (default: {default})'.
                                 format(list=Backends.over_approx_backends_names,
                                        default=default_over_approx_backend))
        parser.add_argument('-u', '--underapprox-backend',
                            metavar='X', type=str, dest='underapprox_backend', default=default_under_approx_backend,
                            help='backend for the under-approximate analysis if required {list} (default: {default})'.
                                 format(list=Backends.under_approx_backends_names,
                                        default=default_under_approx_backend))
        parser.add_argument('-p', '--precise-backend',
                            metavar='X', type=str, dest='precise_backend', default=default_precise_backend,
                            help='Backend for the precise analysis if required {list} (default: {default})'.
                                 format(list=Backends.precise_backends_names,
                                        default=default_precise_backend))
        parser.add_argument('-b', '--backend',
                            metavar='X', type=str, dest='backend', default=None,
                            help='Use only backend X {}'.format(Backends.all_backends_names))

        parser.add_argument('--unwind',
                            metavar='X', type=int, dest='unwind', default=default_unwind,
                            help='unwind X times (CBMC only)')

        parser.add_argument('--interproc-widening-delay',
                            metavar='X', type=int, dest='interproc_w_delay', default=default_interproc_w_delay,
                            help='INTERPROC widening delay (INTERPROC only) (default: {})'.
                                 format(default_interproc_w_delay))
        parser.add_argument('--interproc-widening-steps',
                            metavar='X', type=int, dest='interproc_w_steps', default=default_interproc_w_steps,
                            help='INTERPROC widening descending step number (INTERPROC only) (default: {})'.
                                 format(default_interproc_w_steps))

        parser.add_argument('--mucke-bddlib',
                            metavar='X', type=str, dest='mucke_bddlib', default=def_mucke_bdd,
                            help='Use X as MUCKE bdd library {list} (MUCKE only) (default: {default})'.
                                 format(list=self.MUCKE_BDD_LIBS,
                                        default=def_mucke_bdd))
        parser.add_argument('--mucke-rounds',
                            metavar='X', type=int, dest='mucke_rounds', default=default_mucke_rounds,
                            help='Simulate X rounds with MUCKE (MUCKE only) (default: {})'.format(default_mucke_rounds))

        parser.add_argument('--mucke-formula',
                            metavar='X', type=str, dest='mucke_formula',  # default="super formula path"
                            help='Use X as MUCKE formula (MUCKE only)')

        parser.add_argument('-c', '--show-counterexample',
                            dest='show_counterexample', default=False, action='store_true',
                            help='Show counterexample')
        parser.add_argument('--counterexample-unwind',
                            dest='counterexample_unwind', default=default_unwind,
                            help='CBMC counterexample unwind (default {})'.format(default_unwind))
        parser.add_argument('-s', '--print-pruned-policy',
                            dest='print_pruned', default=False, action='store_true',
                            help='print simplified policy only')
        parser.add_argument('-t', '--print-translated-policy',
                            metavar='X', dest='print_translated', type=str,
                            help='print the translated program in the format X only {}'.
                                 format(Backends.all_backends_names))
        parser.add_argument('--mohawk',
                            dest='mohawk', default=False, action='store_true',
                            help='print equivalent Mohawk benchmark')
        parser.add_argument('-P', '--profile',
                            dest='profile', default=False, action='store_true',
                            help='Shows the times of each step')
        parser.add_argument('--no-color',
                            dest='no_color', default=False, action='store_true',
                            help='Do not color output (default false)')
        parser.add_argument('-D', '--debug',
                            dest='debug', default=False, action='store_true',
                            help='Set the verbosity as high and preserve everything')
        parser.add_argument('-V', '--verbose',
                            dest='verbose', default=False, action='store_true',
                            help='Set the verbosity as high')
        parser.add_argument('-v', '--version',
                            dest='version', default=False, action='store_true',
                            help='Prints the version and exit')
        # Parse the option
        self.args = parser.parse_args()

    def __select_backends(self):
        ret = first(lambda b: b.name.lower() == self.args.overapprox_backend.lower(), Backends.over_approx_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong over-approximate backend. {} not in list {}".
                               format(self.overapprox_backend, Backends.over_approx_backends_names))
        self.overapprox_backend = ret

        ret = first(lambda b: b.name.lower() == self.args.underapprox_backend.lower(), Backends.under_approx_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong under-approximate backend. {} not in list {}".
                               format(self.underapprox_backend, Backends.under_approx_backends_names))
        self.underapprox_backend = ret

        ret = first(lambda b: b.name.lower() == self.args.precise_backend.lower(), Backends.precise_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong precise backend. {} not in list {}".
                               format(self.precise_backend, Backends.precise_backends_names))
        self.precise_backend = ret

        if self.args.backend is not None:
            ret = first(lambda b: b.name.lower() == self.args.backend.lower(), Backends.all_backends)
            # check is redundant, but anyway
            if ret is None:
                raise MessageError("Wrong backend. {} not in list {}".
                                   format(self.backend, Backends.all_backends))
            self.backend = ret

    def set_prepare(self):
        self.__prepare_parser()

        # I'm setting the log before checking args because otherwise errors in checking are badly formatted
        logging.basicConfig(level=l.DEBUG if self.args.verbose or self.args.debug else
                                                                            l.PROFILE if self.args.profile else l.INFO,
                            format='%(message)s')  # format='[%(levelname)s] %(message)s')
        l.colorize = not self.args.no_color

        self.check_args()

        # self.__dict__.update(self.args.__dict__)

        self.working_dir = self.args.working_dir
        self.preserve_tool_answer = self.args.preserve_tool_answer
        self.no_pruning = self.args.no_pruning
        self.overapprox_backend = self.args.overapprox_backend
        self.underapprox_backend = self.args.underapprox_backend
        self.precise_backend = self.args.precise_backend
        self.backend = self.args.backend
        self.unwind = self.args.unwind
        self.interproc_w_delay = self.args.interproc_w_delay
        self.interproc_w_steps = self.args.interproc_w_steps
        self.mucke_bddlib = self.args.mucke_bddlib
        self.mucke_rounds = self.args.mucke_rounds
        self.mucke_formula = self.args.mucke_formula
        self.print_pruned = self.args.print_pruned
        self.print_translated = self.args.print_translated
        self.mohawk = self.args.mohawk
        self.profile = self.args.profile
        self.debug = self.args.debug
        self.verbose = self.args.verbose
        self.version = self.args.version
        self.no_color = self.args.no_color
        self.show_counterexample = self.args.show_counterexample
        self.counterexample_unwind = self.args.counterexample_unwind

        if self.debug:
            self.preserve_tool_answer = True
            self.preserve_artifacts = True
            self.verbose = True

        if not self.version:
            self.__select_backends()

            self.base_dir = os.path.dirname(sys.argv[0])
            self.tool_dir = path.join(self.base_dir, "bin")

            if self.working_dir is None:
                # In this way is not possible to preserve output if in /tmp
                if not self.debug:
                    self.preserve_artifacts = False
                self.working_dir = tempfile.mkdtemp(prefix="vac_")
                l.debug("Working in {}".format(self.working_dir))
            else:
                self.preserve_artifacts = True

            fname = path.basename(self.args.infile)
            self.infile = path.join(self.working_dir, fname)
            shutil.copy(path.join(os.getcwd(), self.args.infile), self.infile)
            if self.no_pruning:
                self.simplified_file = self.infile
                self.simplified_log = None
                self.simplified_debug = None
            else:
                self.simplified_file = "{}_simpl.arbac".format(file_name_wo_extension(self.infile))
                self.simplified_log = "{}_simpl.log".format(file_name_wo_extension(self.infile))
                self.simplified_debug = "{}_simpl.debug".format(file_name_wo_extension(self.infile))
            self.file_prefix = file_name_wo_extension(self.simplified_file)

    def check_args(self):
        if self.args.infile is None:
            raise MessageError("Input argument is missing. (try ./vac.py -h)")
        if not os.path.isfile(self.args.infile):
            raise MessageError("Input file does not exists")
        # WARNING: Quite restrictive. We can try to create the folder
        if self.args.working_dir is not None and not os.path.isdir(path.join(os.getcwd(), self.args.working_dir)):
            raise MessageError("Working directory {} does not exists.".
                               format(path.join(os.getcwd(), self.args.working_dir)))
        # WARNING: maybe not needed if you consider searching in /tmp
        if self.args.preserve_tool_answer and self.args.working_dir is None:
            raise MessageError("Cannot save tool answer in /tmp.")

        if self.args.overapprox_backend not in Backends.over_approx_backends_names:
            raise MessageError("The selected over-approximate backend must be in {}".
                               format(Backends.over_approx_backends_names))
        if self.args.underapprox_backend not in Backends.under_approx_backends_names:
            raise MessageError("The selected under-approximate backend must be in {}".
                               format(Backends.under_approx_backends_names))
        if self.args.precise_backend not in Backends.precise_backends_names:
            raise MessageError("The precise backend backend must be in {}".
                               format(Backends.precise_backends_names))
        if self.args.backend is not None and self.args.backend not in Backends.all_backends_names:
            raise MessageError("The selected backend must be in {}".format(Backends.all_backends_names))

        if (self.args.underapprox_backend == "cbmc" or self.args.backend == "cbmc") and \
           (self.args.unwind is None or self.args.unwind < 1):
            raise MessageError("CBMC backend requires the unwind option to be greater than 0")

        if (self.args.overapprox_backend == "interproc" or self.args.backend == "interproc") and \
                (self.args.interproc_w_delay is None or self.args.interproc_w_delay < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_delay option to be greater than 0")
        if (self.args.overapprox_backend == "interproc" or self.args.backend == "interproc") and \
                (self.args.interproc_w_steps is None or self.args.interproc_w_steps < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_steps option to be greater than 0")

        if (self.args.underapprox_backend == "mucke" or
           (self.args.backend is not None and self.args.backend == "mucke")):
            if self.args.mucke_bddlib is None or self.args.mucke_bddlib not in self.MUCKE_BDD_LIBS:
                raise MessageError("MUCKE backend requires the mucke_bddlib option to be set and in choiches")
            if self.args.mucke_rounds is None or self.args.mucke_rounds < 1:
                raise MessageError("MUCKE backend requires the mucke_rounds option to be set and greater than 0")
            if self.args.mucke_formula is None or not os.path.isfile(self.args.mucke_formula):
                raise MessageError("MUCKE backend requires the mucke_formula option to be a valid file")

        if self.args.print_translated is not None and self.args.print_translated not in Backends.all_backends_names:
            raise MessageError("The selected format must be in {}".format(Backends.all_backends_names))

        if self.args.print_translated and self.args.no_pruning:
            raise MessageError("Cannot print a not pruned policy. Consider cat {}".format(self.args.infile))

        if self.args.show_counterexample and \
                (self.args.counterexample_unwind is None or self.args.counterexample_unwind < 1):
            raise MessageError(
                "Counterexample CBMC backend requires the counterexample-unwind option to be greater than 0")


config = Config()


def str_time(timespan):
    hours, rem = divmod(timespan, 3600)
    minutes, seconds = divmod(rem, 60)
    return "{:0>2}:{:0>2}:{:06.3f}".format(int(hours), int(minutes), seconds)


def execute_get_time(f, args=None):
    start = time.time()
    res = f() if args is None else f(args)
    elapsed = time.time() - start
    return res, elapsed


def execute_print_time(f, args=None, fmt="Operation executed in {}"):
    res, elapsed = execute_get_time(f, args)
    l.profile(fmt.format(str_time(elapsed)))
    return res


class Backends:
    def __init__(self): pass
    over_approx_backends = [
        Solver(name="interproc",
               tool_name="interproc",
               in_suffix="simpl",
               precision=Precision.OverApprox,
               arguments="-domain box",
               res_interp=[(Result.MaybeUnsafe, [re.compile("The query is not safe")]),
                           (Result.Safe, [re.compile("The query is safe")])],
               translation_format="interproc",
               runtime_arguments=lambda: "-widening {} {}".format(config.interproc_w_delay, config.interproc_w_steps))
    ]
    under_approx_backends = [
        Solver(name="cbmc",
               tool_name="cbmc",
               in_suffix="c",
               precision=Precision.UnderApprox,
               arguments="--no-unwinding-assertions --xml-ui",
               res_interp=[(Result.MaybeSafe, [re.compile("VERIFICATION SUCCESSFUL")]),
                           (Result.Unsafe, [re.compile("VERIFICATION FAILED")])],
               translation_format="cbmc",
               runtime_arguments=lambda: "--unwind {}".format(config.unwind),
               accepted_retcodes={0, 10}),
        Solver(name="mucke",
               tool_name="mucke",
               in_suffix="mu",
               precision=Precision.UnderApprox,
               arguments="-ws",
               runtime_arguments=lambda: "-bman {}".format(config.mucke_bddlib),
               res_interp=[(Result.MaybeSafe, [re.compile(":   false"),  # enhance
                                                re.compile("\*\*\* Can't build witness: term not true")]),
                           (Result.Unsafe, [re.compile(":   true"),  # enhance
                                            re.compile(":[^=]*= \{")])],
               translation_format="mucke")
    ]

    precise_backends = [
        Solver(name="z3",
               tool_name="z3",
               in_suffix="smt2",
               precision=Precision.Exact,
               arguments="-smt2",
               res_interp=[(Result.Safe, [re.compile("\bsat")]),
                           (Result.Unsafe, [re.compile("unsat")])],
               translation_format="smt"),
        Solver(name="hsf",
               tool_name="qarmc",
               in_suffix="hsf",
               precision=Precision.Exact,
               arguments="",
               res_interp=[(Result.Safe, [re.compile("program is correct")]),
                           (Result.Unsafe, [re.compile("program is not correct")])],
               translation_format="hsf"),
        Solver(name="eldarica",
               tool_name="eldarica-2063.jar",
               in_suffix="horn",
               precision=Precision.Exact,
               arguments="-horn -hin -princess -bup -n",
               res_interp=[(Result.Safe, [re.compile("\nSOLVABLE")]),
                           (Result.Unsafe, [re.compile("NOT SOLVABLE")])],
               translation_format="eldarica",
               cmd_format="java -jar {tool_path}/{tool_name} {arguments} {in_file}"),
        Solver(name="nusmv",
               tool_name="NuSMV",
               in_suffix="nusmv",
               precision=Precision.Exact,
               arguments="",
               res_interp=[(Result.Safe, [re.compile("-- specification.*is true")]),
                           (Result.Unsafe, [re.compile("-- specification.*is false")])],
               translation_format="smv"),
        Solver(name="moped",
               tool_name="moped",
               in_suffix="bp",
               precision=Precision.Exact,
               arguments="-b",
               res_interp=[(Result.Safe, [re.compile("Reachable.")]),
                           (Result.Unsafe, [re.compile("Not reachable.")])],
               translation_format="moped")
    ]  # ["z3", "hsf", "eldarica", "nusmv", "moped", "seahorn"]

    all_backends = over_approx_backends + under_approx_backends + precise_backends

    over_approx_backends_names = list(map(lambda b: b.name, over_approx_backends))
    under_approx_backends_names = list(map(lambda b: b.name, under_approx_backends))
    precise_backends_names = list(map(lambda b: b.name, precise_backends))
    all_backends_names = list(map(lambda b: b.name, all_backends))


def full_analysis():
    l.info("=====> Over approximate analysis of ARBAC policy using {} =====>".format(config.overapprox_backend.name))
    overapprox_res = config.overapprox_backend.run()
    print_result(overapprox_res)
    if overapprox_res is Result.Safe:
        return False

    l.info("=====> Under approximate analysis of ARBAC policy using {} =====>".format(config.underapprox_backend.name))
    underapprox_res = config.underapprox_backend.run()
    print_result(underapprox_res)
    if underapprox_res is Result.Unsafe:
        return True

    l.info("=====> Precise analysis of ARBAC policy using {} =====>".format(config.precise_backend.name))
    precise_res = config.precise_backend.run()
    print_result(precise_res)
    if precise_res is Result.Safe:
        return False
    elif precise_res is Result.Unsafe:
        return True

    raise UnexpectedError("Should be exited before...")


def produce_counterexample():
    l.info("=====> Generating counter example.. =====>")
    counter_example = build_counterexample()
    if counter_example is None:
        l.info("Cannot find the counter example. ")
    else:
        l.info("=====> Produce Counter Example ====>")
        l.info(counter_example)


def single_analysis():
    l.info("=====> Running analysis of ARBAC policy using {} =====>".format(config.backend.name))
    backend_res = config.backend.run()
    print_result(backend_res)
    return backend_res


def analyze():
    if not config.no_pruning:
        simplify()

    if config.backend is None:
        analysis_result = full_analysis()
    else:
        analysis_result = single_analysis()

    if config.show_counterexample:
        if analysis_result is Result.Unsafe or analysis_result is Result.MaybeUnsafe:
            produce_counterexample()
        else:
            l.warning("The ARBAC policy is safe. There is no counterexample.")


def at_sig_halt(_signal=None, _frame=None):
    def ignore(_): return
    ignore((_signal, _frame))
    sys.stderr.write("\nKilled by the user.\n")
    clean()
    exit(3)


def clean():
    if not config.preserve_artifacts:
        try:
            shutil.rmtree(config.working_dir)
        except:
            l.warning("Not able to delete temporary folder: {}".format(config.working_dir))
            pass


def main():
    try:
        logging.basicConfig(level=l.RESULT, format='%(message)s')  # Will be reset during argparsing
        # global config
        config.set_prepare()

        if config.version:
            print(VACDESCRIPTION)
            sys.exit(0)

        # register anti-panic handlers
        signal.signal(signal.SIGINT, at_sig_halt)
        atexit.register(clean)

        execute_print_time(analyze, fmt="Analysis executed in {}")

        l.result("")

        exit(0)
    except MessageError as me:
        l.critical("{}\n".format(me.message))
        exit(1)
    except Exception as e:
        l.critical("OtherException:\n{}".format(str(e)))
        exit(2)


if __name__ == '__main__':
    main()

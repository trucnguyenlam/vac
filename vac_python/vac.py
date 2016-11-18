#!/usr/bin/env python
"""
    Wrapper script for VAC

ChangeLog:
    2016.05.19   Initial version based on old script vac.sh

"""
import argparse
import atexit
import logging
import re
import sys
import os
from os import path
import signal
import subprocess
import tempfile
import shutil
import time
import functools
import logging as L


VACDESCRIPTION = '''\
* *               VAC 2.0 - Verifier of Access Control                * *
* *                                                                   * *
* *            Anna Lisa Ferrara (1), P. Madhusudan (2),              * *
* *           Truc L. Nguyen (3), and Gennaro Parlato (3).            * *
* *                                                                   * *
* * (1) University of Bristol (UK), (2) University of Illinois (USA), * *
* *               and (3) University of Southampton (UK)              * *

'''

EPILOG = '''
VAC without any option runs the default option:
it first runs the abstract transformer followed by Interproc;
if a proof cannot be provided, VAC runs the precise transformer
followed by CBMC (unwind set to 2) to look for a counterexample.
Otherwise, it executes SeaHorn for complete analysis.
'''


class Log(object):
    def __init__(self): pass
    CRITICAL = 50
    ERROR = 40
    WARNING = 30
    INFO = 20
    PROFILE = 15
    DEBUG = 10

    def critical(self, msg):  # , *args, **kwargs):
        L.log(self.CRITICAL, msg)  # , args, kwargs)

    def error(self, msg):  # , *args, **kwargs):
        L.log(self.ERROR, msg)  # , args, kwargs)

    def warning(self, msg):  # , *args, **kwargs):
        L.log(self.WARNING, msg)  # , args, kwargs)

    def info(self, msg):  # , *args, **kwargs):
        L.log(self.INFO, msg)  # , args, kwargs)

    def profile(self, msg):  # , *args, **kwargs):
        L.log(self.PROFILE, msg)  # , args, kwargs)

    def debug(self, msg):  # , *args, **kwargs):
        L.log(self.DEBUG, msg)  # , args, kwargs)

    def exception(self, msg):  # , *args, **kwargs):
        kwargs['exc_info'] = 1
        self.error(msg)  # , *args, **kwargs)
        # L.exception(msg, args, kwargs)

l = Log()


def exists(f, xs): return reduce(lambda s, x: s if s else f(x), xs, False)


def first(f, xs): return reduce(lambda s, x: x if s is None and f(x) else s, xs, None)

# def merge_dict(a, b):
#     z = a.copy()
#     z.update(b)
#     return z


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
    SAFE = 1
    UNSAFE = 2
    MAYBE_SAFE = 3
    MAYBE_UNSAFE = 4
    ERROR = 5


def print_result(result):
    if result is Result.SAFE:
        l.info("The ARBAC policy is safe")
    elif result is Result.UNSAFE:
        l.info("The ARBAC policy is not safe")
    elif result is Result.MAYBE_SAFE:
        l.info("The ARBAC policy may be safe")
    elif result is Result.MAYBE_UNSAFE:
        l.info("The ARBAC policy may be unsafe")
    elif result is Result.ERROR:
        l.info("Error in translation or in this script :)")
    else:
        l.critical("Analysis returned unexpected value {}".format(result))


class Precision:
    def __init__(self): pass
    EXACT = 1
    OVER_APPROX = 2
    UNDER_APPROX = 3


class Solver(object):
    name = None  # str
    tool_name = None  # str
    in_suffix = None  # str
    precision = None  # Precision For checking, but not required
    arguments = None  # format str
    res_interp = None  # [(Result, [regex])]
    cmd_format = None  # format str
    translation_format = None  # str

    def __init__(self,
                 name,
                 tool_name,
                 in_suffix,
                 precision,
                 arguments,
                 res_interp,
                 translation_format,
                 cmd_format="{cmd_path}/{cmd_name} {arguments} {in_file}"):
        self.name = name
        self.tool_name = tool_name
        self.in_suffix = in_suffix
        self.precision = precision
        self.arguments = arguments
        self.res_interp = res_interp
        self.cmd_format = cmd_format
        self.translation_format = translation_format
        
    def _get_command(self, input_file, other_options=""):
        cmd = self.cmd_format.format(
                cmd_path=config.tool_dir,
                cmd_name=self.tool_name,
                arguments="{} {}".format(self.arguments, other_options),
                in_file=input_file)
        l.warning("Got command: {}".format(cmd))
        return cmd

    def _find_result(self, str_res):
        res_p = filter(lambda _, regexs: exists(lambda reg: reg.match(str_res) is not None, regexs), self.res_interp)
        res = map(lambda r, _: r, res_p)
        if len(res) != 1:
            l.error("Got zero o more than one possible results:\n\t{}".format(str(res)))
            raise MessageError("Got zero o more than one possible results:\n\t{}".format(str(res)))
        else:
            # Paranoid checks
            ret = res[0]
            if self.precision is Precision.EXACT and ret not in [Result.SAFE, Result.UNSAFE]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))
            if self.precision is Precision.OVER_APPROX and ret not in [Result.SAFE, Result.MAYBE_UNSAFE]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))
            if self.precision is Precision.UNDER_APPROX and ret not in [Result.MAYBE_SAFE, Result.UNSAFE]:
                raise MessageError("Got result: {}, but tool precision is {}.".format(ret, self.precision))

            if ret == Result.ERROR:
                raise MessageError("Got result: {}.".format(ret))

            return ret

    def in_file_name(self):
        fname = "{}.{}".format(config.file_prefix, self.in_suffix)
        return fname

    def _execute(self, input_file, other_options=""):
        cmd = self._get_command(input_file, other_options)

        retcode, out, err = execute_cmd(cmd, self.name)  # , input_file)

        # Check result
        result = self._find_result(out)

        return result

    def run(self, other_options=""):
        mucke = self.translation_format.lower() == "mucke"
        options = other_options
        if self.name == "cbmc":
            options = "--unwind {}".format(config.unwind)
        elif self.name == "interproc":
            options = "-widening {} {}".format(config.interproc_w_delay, config.interproc_w_steps)
        translate(config.simplified_file, self.translation_format, self.in_file_name(), mucke)
        return self._execute(self.in_file_name(), options)


def execute_cmd(cmd, name=None):  # , input_file=None):
    can_save = name is None
    if name is None:
        name = cmd
    l.debug("Running {}".format(cmd))
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    retcode = p.wait()
    out = p.stdout
    err = p.stderr
    if retcode != 0:
        l.warning("{} got return code {}".format(name, retcode))
    if err is not "":
        l.warning("{} got {}".format(name, err))
    if config.preserve_tool_answer and can_save:  # and input_file is not None:
        out_log = "{}_{}.log".format(config.file_prefix, name)
        out_err = "{}_{}.err".format(config.file_prefix, name)
        with open(out_log, 'w') as log_f:
            log_f.write(cmd)
            log_f.write(out)
        with open(out_err, 'w') as err_f:
            err_f.write(cmd)
            err_f.write(err)
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
    l.warning("Got command: {}".format(cmd))
    retval, stdout, stderr = execute_cmd(cmd)
    if retval != 0 and stdout is not "" and stderr is not "":
        raise MessageError(
            "Translation went wrong. Error in file{f}:\n\tReturn value: {r}\n\tStdout: {o}\n\tStderr: {e}\n\tCmd: {c}".
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
        args = "--debug {debug} --logfile {log} --out {out}".format(
            debug=config.simplified_debug,
            log=config.simplified_log,
            out=config.simplified_file)
        cmd = "{cmd_path}/simplify {arguments} {in_file}".format(
            cmd_path=config.tool_dir,
            arguments=args,
            in_file=config.infile)
        l.warning("Got command: {}".format(cmd))
        retval, stdout, stderr = execute_cmd(cmd)
        if retval != 0 and stdout is not "" and stderr is not "":
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
    if out == "":  # check better for counterexample
        l.warning("Could not find a counterexample")
        return None
    # l.info(out)
    return out

# '''
#     Backend definitions
# '''
# backendExec = {
#     "cbmc":
#         Solver("cbmc",
#                "--no-unwinding-assertions --xml-ui",
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                "{cmd_path}/{cmd_name} {arguments} --unwind {other_options} {in_file}" #
#                ),
#     "eldarica":
#         Solver("eldarica-2305.jar",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "interproc":
#         Solver("interproc",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "moped":
#         Solver("moped",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "mucke":
#         Solver("mucke",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "NuSMV":
#         Solver("NuSMV",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "qarmc":
#         Solver("qarmc",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                ),
#     "z3":
#         Solver("z3",
#                args,
#                [ok],
#                [fail],
#                [err],
#                error_msg,
#                invocation
#                )
#     }

# "simplify":
# # if wrong it writes to stderr
# # does nothing
# Solver("simplify",
#        "-g"),
# "translate":
# Solver("translate",
#        args,
#        [ok],
#        [fail],
#        [err],
#        error_msg,
#        invocation
#        ),
# "cex":
# Solver(      "cex",
#              args,
#              [ok],
#              [fail],
#              [err],
#              error_msg,
#              invocation
#              )
# cbmc eldarica-2305.jar interproc moped mucke NuSMV qarmc z3


backendOptions = {
    'interproc': ' -domain box ',
    'cbmc': ' --no-unwinding-assertions --unwind ',
    'z3': ' -smt2 '
    }

backendAnswerOK = {
    'interproc': 'not safe',
    'cbmc': 'VERIFICATION SUCCESSFUL',
    'z3': 'sat'
    }

backendAnswerFAIL = {
    'interproc': 'safe',
    'cbmc': 'VERIFICATION FAILED',
    'z3': 'unsat'
    }

vacexec = {
    "simplify":   './bin/simplify',
    "translate":  './bin/translate',
    "cex":        './bin/counterexample'
    }


mucke_bddlibs = ["abcd.so", "longbman.so", "cudd.a"]


class Config(object):
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
    verbose = None
    version = None
    args = None

    def __init__(self): pass

    def __prepare_parser(self):
        parser = argparse.ArgumentParser(description=VACDESCRIPTION,
                                         epilog=EPILOG,
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
                            metavar='X', type=str, dest='overapprox_backend', default='interproc',
                            help='backend for the over-approximate analysis if required {} (default: interproc)'.
                                 format(Backends.over_approx_backends_names))
        parser.add_argument('-u', '--underapprox-backend',
                            metavar='X', type=str, dest='underapprox_backend', default='cbmc',
                            help='backend for the under-approximate analysis if required {} (default: cbmc)'.
                                 format(Backends.under_approx_backends_names))
        parser.add_argument('-p', '--precise-backend',
                            metavar='X', type=str, dest='precise_backend', default='z3',
                            help='Backend for the precise analysis if required {} (default: z3)'.
                                 format(Backends.precise_backends_names))
        parser.add_argument('-b', '--backend',
                            metavar='X', type=str, dest='backend', default=None,
                            help='Use only backend X {}'.format(Backends.all_backends_names))

        parser.add_argument('--unwind',
                            metavar='X', type=int, dest='unwind', default=2,
                            help='unwind X times (CBMC only)')

        parser.add_argument('--interproc-widening-delay',
                            metavar='X', type=int, dest='interproc_w_delay', default=1,
                            help='INTERPROC widening delay (INTERPROC only) (default: 1)')
        parser.add_argument('--interproc-widening-steps',
                            metavar='X', type=int, dest='interproc_w_steps', default=2,
                            help='INTERPROC widening descending step number (INTERPROC only) (default: 2)')

        parser.add_argument('--mucke-bddlib',
                            metavar='X', type=str, dest='mucke_bddlib', default=mucke_bddlibs[0],
                            help='Use X as MUCKE bdd library {} (MUCKE only)'.format(mucke_bddlibs))
        parser.add_argument('--mucke-rounds',
                            metavar='X', type=int, dest='mucke_rounds', default=4,
                            help='Simulate X rounds with MUCKE (MUCKE only) (default: 4)')
        # TODO: set the correct defaults and show all choices
        parser.add_argument('--mucke-formula',
                            metavar='X', type=str, dest='mucke_formula', default='super formula',
                            help='Use X as MUCKE formula (MUCKE only)')

        parser.add_argument('-c', '--show-counterexample',
                            dest='show_counterexample', default=False, action='store_true',
                            help='Show counterexample')
        parser.add_argument('--counterexample-unwind',
                            dest='counterexample_unwind', default=15,
                            help='CBMC counterexample unwind (default 15)')
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
        parser.add_argument('--profile',
                            dest='profile', default=False, action='store_true',
                            help='Shows the times of each step')
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

        self.check_args()

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
        self.verbose = self.args.verbose
        self.version = self.args.version
        self.show_counterexample = self.args.show_counterexample
        self.counterexample_unwind = self.args.counterexample_unwind

        logging.basicConfig(level=l.DEBUG if self.verbose else l.PROFILE if self.profile else l.INFO,
                            format='[%(levelname)s] %(message)s')

        if not self.version:
            self.__select_backends()

            self.base_dir = os.path.dirname(sys.argv[0])
            self.tool_dir = path.join(self.base_dir, "bin")

            if self.working_dir is None:
                # In this way is not possible to preserve output if in /tmp 
                self.preserve_artifacts = False
                self.working_dir = tempfile.mkdtemp(prefix="vac_")
                l.debug("Working in {}".format(self.working_dir))
            else:
                self.preserve_artifacts = True

            # FIXME: tutto rotto...
            fname = path.basename(self.args.infile)
            self.infile = path.join(self.working_dir, fname)
            shutil.copy(self.args.infile, self.infile)
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

        if (self.args.underapprox_backend is "cbmc" or self.args.backend is "cbmc") and \
           (self.args.unwind is None or self.args.unwind < 1):
            raise MessageError("CBMC backend requires the unwind option to be greater than 0")

        if (self.args.overapprox_backend is "interproc" or self.args.backend is "interproc") and \
                (self.args.interproc_w_delay is None or self.args.interproc_w_delay < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_delay option to be greater than 0")
        if (self.args.overapprox_backend is "interproc" or self.args.backend is "interproc") and \
                (self.args.interproc_w_steps is None or self.args.interproc_w_steps < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_steps option to be greater than 0")

        if (self.args.underapprox_backend is "mucke" or
           (self.args.backend is not None and self.args.backend is "mucke")):
            if self.args.mucke_bddlib is None or self.args.mucke_bddlib not in mucke_bddlibs:
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


def execute_print_time(f, args, fmt="Operation executed in {}"):
    res, elapsed = execute_get_time(f, args)
    print(fmt.format(str_time(elapsed)))
    return res


class Backends:
    def __init__(self): pass
    over_approx_backends = [
        Solver(name="interproc",
               tool_name="interproc",
               in_suffix="simpl",
               precision=Precision.OVER_APPROX,
               arguments="-domain box",
               res_interp=[Result.MAYBE_UNSAFE, [re.compile("The query is not safe")],
                           Result.SAFE, [re.compile("The query is safe")]],
               translation_format="interproc")
    ]
    under_approx_backends = [
        Solver(name="cbmc",
               tool_name="cbmc",
               in_suffix="c",
               precision=Precision.UNDER_APPROX,
               arguments="--no-unwinding-assertions --xml-ui",
               res_interp=[Result.MAYBE_SAFE, [re.compile("VERIFICATION SUCCESSFUL")],
                           Result.UNSAFE, [re.compile("VERIFICATION FAILED")]],
               translation_format="cbmc"),
        Solver(name="mucke",
               tool_name="mucke",
               in_suffix="mu",
               precision=Precision.UNDER_APPROX,
               arguments="-ws",
               res_interp=[Result.MAYBE_SAFE, [re.compile(":   false"),  # enhance
                                               re.compile("\*\*\* Can't build witness: term not true")],
                           Result.UNSAFE, [re.compile(":   true"),  # enhance
                                           re.compile(":[^=]*= \{")]],
               translation_format="mucke")
    ]
    precise_backends = [
        Solver(name="z3",
               tool_name="z3",
               in_suffix="smt2",
               precision=Precision.EXACT,
               arguments="-smt2",
               res_interp=[Result.SAFE, [re.compile("\bsat")],
                           Result.UNSAFE, [re.compile("unsat")]],
               translation_format="smt")
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
    if overapprox_res == Result.SAFE:
        return False

    l.info("=====> Under approximate analysis of ARBAC policy using {} =====>".format(config.underapprox_backend.name))
    underapprox_res = config.underapprox_backend.run()
    print_result(underapprox_res)
    if underapprox_res == Result.UNSAFE:
        return True

    l.info("=====> Precise analysis of ARBAC policy using {} =====>".format(config.precise_backend.name))
    precise_res = config.precise_backend.run()
    print_result(precise_res)
    if precise_res == Result.SAFE:
        return False
    elif precise_res == Result.UNSAFE:
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

    if config.show_counterexample and (analysis_result == Result.UNSAFE or analysis_result == Result.MAYBE_UNSAFE):
        produce_counterexample()
    else:
        l.warning("The ARBAC policy is safe. There is no counterexample.")


def at_sig_halt(_signal=None, _frame=None):
    def ignore(_): pass
    ignore((_signal, _frame))
    sys.stderr.write("\nKilled by the user.\n")
    clean()


def clean():
    if not config.preserve_artifacts:
        shutil.rmtree(config.working_dir)


def main():
    try:
        # global config
        config.set_prepare()

        if config.version:
            print(VACDESCRIPTION)
            sys.exit(0)

        # register anti-panic handlers
        signal.signal(signal.SIGINT, at_sig_halt)
        atexit.register(clean)

        # configure how logging should be done

        starttime = time.time()

        analyze()

        print("Elapse time: %0.2f" % (time.time() - starttime))

        exit(0)
    except MessageError as me:
        l.critical("{}:\n{}".format(me.message, str(me)))
        exit(1)


if __name__ == '__main__':
    main()

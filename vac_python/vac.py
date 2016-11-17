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
import threading
import shutil
import time
import functools
import logging as l


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

def exists(f, xs): return reduce (lambda s, x: s if s else f(x), xs, False)

def first(f, xs): return reduce (lambda s, x: x if s is None and f(x) else s, xs, None)

# def merge_dict(a, b):
#     z = a.copy()
#     z.update(b)
#     return z

class UnexpectedError(Exception):
    msg = ""
    def __init__(self, msg):
        self.msg = msg


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
    name               = None  # str
    tool_name          = None  # str
    in_suffix          = None  # str
    precision          = None  # Precision For checking, but not required
    arguments          = None  # format str
    res_interp         = None  # [(Result, [str])] # TODO: consider regex
    cmd_format         = None  # format str
    translation_format = None # str
    def __init__(self,
                 name,
                 tool_name,
                 in_suffix,
                 precision,
                 arguments,
                 res_interp,
                 translation_format,
                 cmd_format="{cmd_path}/{cmd_name} {arguments} {in_file}"):
        self.name       = name
        self.tool_name  = tool_name
        self.in_suffix  = in_suffix
        self.precision  = precision
        self.arguments  = arguments
        self.res_interp = res_interp
        self.cmd_format = cmd_format
        self.translation_format = translation_format
        
    def _get_command(self, input_file, other_options=""):
        cmd = self.cmd_format.format(
                cmd_path=Config.tool_dir,
                cmd_name=self.tool_name,
                arguments="{} {}".format(self.arguments, other_options),
                in_file=input_file)
        l.warning("Got command: {}".format(cmd))
        return cmd

    def _find_result(self, str_res):
        res_p = filter(lambda (_, regexs): exists(lambda reg: reg.match(str_res) is not None, regexs), self.res_interp)
        res = map(lambda (r, _): r, res_p)
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
        fname = "{}.{}".format(Config.file_prefix, self.in_suffix)
        return fname


    def _execute(self, input_file, other_options=""):
        cmd = self._get_command(input_file, other_options)

        retcode, out, err = execute_cmd(cmd, self.name, input_file)

        # Check result
        result = self._find_result(out)

        return result

    def run(self, other_options = ""):
        mucke = self.translation_format.lower() == "mucke"
        options = other_options
        if self.name == "cbmc":
            options = "--unwind {}".format(Config.unwind)
        elif self.name == "interproc":
            options = "-widening {} {}".format(Config.interproc_w_delay, Config.interproc_w_steps)
        translate(Config.simplified_file, self.translation_format, self.in_file_name(), mucke)
        return self._execute(self.in_file_name(), options)


def execute_cmd(cmd, name=None, input_file=None):
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
    if Config.preserve_tool_answer and can_save and input_file is not None:
        out_log = "{}_{}.log".format(Config.file_prefix, name)
        out_err = "{}_{}.err".format(Config.file_prefix, name)
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
        other="--formula {} --rounds {}".format(Config.mucke_formula, Config.mucke_rounds) if mucke else "")
    cmd = "{cmd_path}/translate {arguments} {in_file}".format(
        cmd_path=Config.tool_dir,
        arguments="{} {}".format(args),
        in_file=in_file)
    l.warning("Got command: {}".format(cmd))
    retval, stdout, stderr = execute_cmd(cmd)
    if  retval != 0 and \
        stdout is not "" and \
        stderr is not "":
        raise MessageError(
            "Translation went wrong... Error in file{f}:\n\tReturn value: {r}\n\tStdout: {o}\n\tStderr: {e}\n\tCmd: {c}".format(
                f=in_file,
                r=retval,
                o=stdout,
                e=stderr,
                c=cmd))
    return True


def simplify():
    if Config.no_pruning:
        raise MessageError("Should not simplify if --no-pruning")
    else:
        args = "--debug {debug} --logfile {log} --out {out}".format(
            debug=Config.simplified_debug,
            log=Config.simplified_log,
            out=Config.infile)
        cmd = "{cmd_path}/simplify {arguments} {in_file}".format(
            cmd_path=Config.tool_dir,
            arguments=args,
            in_file=Config.simplified_file)
        l.warning("Got command: {}".format(cmd))
        retval, stdout, stderr = execute_cmd(cmd)
        if  retval != 0 and \
                        stdout is not "" and \
                        stderr is not "":
            raise MessageError(
                "Pruning went wrong... Error in file{f}:\n\tReturn value: {r}\n\tStdout: {o}\n\tStderr: {e}\n\tCmd: {c}".format(
                    f=Config.infile,
                    r=retval,
                    o=stdout,
                    e=stderr,
                    c=cmd))
        return True

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
#cbmc eldarica-2305.jar interproc moped mucke NuSMV qarmc z3


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


'''
    Process Class
'''


class Command(object):
    status = None
    output = stderr = ''

    def __init__(self, cmdline):
        self.cmd = cmdline
        self.process = None

    def run(self, timeout):
        def target():
            # Thread started
            self.process = subprocess.Popen(self.cmd, shell=True, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.output, self.stderr = self.process.communicate()
            # Thread finished

        thread = threading.Thread(target=target)

        try:
            thread.start()
            thread.join(timeout)
            if thread.is_alive():
                # Terminating process
                # self.process.terminate()
                os.killpg(self.process.pid, signal.SIGKILL)
                thread.join()
        except KeyboardInterrupt:
            os.killpg(self.process.pid, signal.SIGKILL)
            # self.process.kill()

        return self.output, self.stderr, self.process.returncode


def saveFile(filename, string):
    with open(filename, "w") as outfile:
        outfile.write(string)


def checkVACComponent():
    for f in vacexec:
        if not os.path.isfile(vacexec[f]):
            return False
    return True


def defaultAlgorithm(inputfile):
    print "=====> Simplification ARBAC policy =====>"
    simplifyCMD = vacexec['simplify'] + ' -g ' + inputfile
    prunedfile = inputfile + '_reduceAdmin.arbac'
    debugfile = inputfile + '_debug'
    cmd = Command(simplifyCMD)
    out, err, code = cmd.run(86400)
    if 'error' in (out + err):
        print out + err
        print "Error: please input correct ARBAC policy."
        shutil.rmtree(prunedfile, ignore_errors=True)
        shutil.rmtree(debugfile, ignore_errors=True)

    print "=====> Translation ARBAC policy =====>"
    translateCMD = vacexec['translate'] + ' -f interproc -a abstract ' + prunedfile
    translatedfile = prunedfile + '_OverApx_INTERPROC.cpp'
    cmd = Command(translateCMD)
    out, err, code = cmd.run(86400)

    print "=====> Analysis of translated ARBAC policy =====>"
    verifyCMD = backendExec['interproc'] + backendOptions['interproc'] + translatedfile
    cmd = Command(verifyCMD)
    out, err, code = cmd.run(86400)
    if backendAnswerFAIL['interproc'] in out:
        print "The ARBAC policy may not be safe."
        print "===> Under approximate analysis ===>"
        translateCMD = vacexec['translate'] + ' -f cbmc -a precise ' + prunedfile
        translatedfile = prunedfile + '_ExactAlg_CBMC.c'
        cmd = Command(translateCMD)
        out, err, code = cmd.run(86400)

        verifyCMD = backendExec['cbmc'] + backendOptions['cbmc'] + " 2 --xml-ui " + translatedfile
        xmllogfile = inputfile + '_log.xml'
        cmd = Command(verifyCMD)
        out, err, code = cmd.run(86400)
        saveFile(xmllogfile, out + err)

        cexCMD = vacexec['cex'] + ' '.join([xmllogfile, translatedfile, prunedfile, debugfile, inputfile])
        cmd = Command(cexCMD)
        out, err, code = cmd.run(86400)
        if 'no Counter Example' in out:
            print "===> Complete Analysis ===>"
            translateCMD = vacexec['translate'] + ' -f smt -a precise ' + prunedfile
            translatedfile = prunedfile + '_ExactAlg_SMT.smt2'
            cmd = Command(translateCMD)
            out, err, code = cmd.run(86400)
            verifyCMD = backendExec['z3'] + backendOptions['z3'] + translatedfile
            cmd = Command(verifyCMD)
            out, err, code = cmd.run(86400)
            if backendAnswerFAIL['z3'] in out:
                # TODO


    elif backendAnswerOK['interproc'] in out:
        pass
    else:
        pass


def customAlgorithm(inputfile, args):
    pass

class Backend():
    def __init__(self):


mucke_bddlibs = ["abcd.so", "longbman.so", "cudd.a"]

class MessageError(RuntimeError):
    message = None
    def __init__(self, message):
        self.message = message


class Config:
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
    print_pruned = None
    print_translated = None
    mohawk = None
    profile = None
    verbose = None
    version = None
    def __init__(self): pass
    def __prepare_parser(self):
        parser = argparse.ArgumentParser(description=VACDESCRIPTION,
                                         epilog=EPILOG,
                                         formatter_class=argparse.RawDescriptionHelpFormatter,
                                         usage=argparse.SUPPRESS)
        parser.add_argument('infile', type=str, help='input policy')
        parser.add_argument('-d', '--working-dir',
                            metavar='X', action='store_true', dest='working_dir', type=str,
                            help="Works in X and do not remove intermediate artifact of the analysis")
        parser.add_argument('-p', '--preserve-tool-answer',
                            metavar='X', action='store_true', dest='preserve_tool_answer', default=False,
                            help="Preserve all tool answer saving to log files (requires --working-dir)")
        parser.add_argument('-n', '--no-pruning',
                            action='store_true', default=False, dest='no_pruning',
                            help='no simplification procedure (default No)')
        parser.add_argument('-o', '--overapprox-backend',
                            metavar='X', type=str, dest='overapprox_backend', default='interproc',
                            help='backend for the over-approximate analysis if required {} (default: interproc)'.format(Backends.over_approx_backends_names))
        parser.add_argument('-u', '--underapprox-backend',
                            metavar='X', type=str, dest='underapprox_backend', default='cbmc',
                            help='backend for the under-approximate analysis if required {} (default: cbmc)'.format(Backends.under_approx_backends_names))
        parser.add_argument('-c', '--precise-backend',
                            metavar='X', type=str, dest='precise_backend', default='z3',
                            help='Backend for the precise analysis if required {} (default: z3)'.format(Backends.precise_backends_names))
        parser.add_argument('-b', '--backend',
                            metavar='X', type=str, dest='backend', default='',
                            help='Use only backend {}'.format(Backends.all_backends_names))

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

        parser.add_argument('-p', '--print-pruned-policy',
                            dest='print_pruned', default=False, action='store_true',
                            help='print simplified policy only')
        parser.add_argument('-t', '--print-translated-policy',
                            metavar='X', dest='print_translated', type=str, action='store_true',
                            help='print the translated program in the format X only {}'.format(backends))
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
        return parser.parse_args()

    def __select_backends(self, args):
        ret = first(lambda b: b.name.lower() == args.underapprox_backend.lower(), self.over_approx_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong over-approximate backend. {} not in list {}".format(Config.underapprox_backend, Backends.over_approx_backends))
        self.overapprox_backend = ret

        ret = first(lambda b: b.name.lower() == args.overapprox_backend.lower(), self.under_approx_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong under-approximate backend. {} not in list {}".format(Config.overapprox_backend, Backends.under_approx_backends))
        self.underapprox_backend = ret

        ret = first(lambda b: b.name.lower() == args.precise_backend.lower(), self.precise_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong precise backend. {} not in list {}".format(Config.precise_backend, Backends.precise_backends))
        self.precise_backend = ret

        ret = first(lambda b: b.name.lower() == args.backend.lower(), self.all_backends)
        # check is redundant, but anyway
        if ret is None:
            raise MessageError("Wrong backend. {} not in list {}".format(Config.backend, Backends.all_backends))
        self.backend = ret

    def set_prepare(self):

        args = self.__prepare_parser()

        self.check_args(args)

        self.working_dir            = args.working_dir
        self.preserve_tool_answer   = args.preserve_tool_answer
        self.no_pruning             = args.no_pruning
        self.overapprox_backend     = args.overapprox_backend
        self.underapprox_backend    = args.underapprox_backend
        self.precise_backend       = args.complete_backend
        self.backend                = args.backend
        self.unwind                 = args.unwind
        self.interproc_w_delay      = args.interproc_w_delay
        self.interproc_w_steps      = args.interproc_w_steps
        self.mucke_bddlib           = args.mucke_bddlib
        self.mucke_rounds           = args.mucke_rounds
        self.mucke_formula          = args.mucke_formula
        self.print_pruned           = args.print_pruned
        self.print_translated       = args.print_translated
        self.mohawk                 = args.mohawk
        self.profile                = args.profile
        self.verbose                = args.verbose
        self.version                = args.version

        logging.basicConfig(level=logging.DEBUG if self.verbose else logging.INFO,
                            format='[%(levelname)s] %(message)s')

        if not self.version:
            self.__select_backends(args)

            self.base_dir = os.path.dirname(sys.argv[0])
            self.tool_dir = path.join(self.base_dir, "bin")

            if self.working_dir is None:
                self.preserve_artifacts = False
                self.working_dir = tempfile.mkdtemp(prefix="vac_")
                l.debug("Working in {}".format(self.working_dir))
            else:
                self.preserve_artifacts = True

            fname = path.basename(args.infile)
            self.infile = path.join(self.working_dir, fname)
            shutil.copy(args.infile, self.infile)
            self.simplified_file = "{}_simpl.arbac".format(file_name_wo_extension(self.infile))
            self.simplified_log = "{}_simpl.log".format(file_name_wo_extension(self.infile))
            self.simplified_debug = "{}_simpl.debug".format(file_name_wo_extension(self.infile))
            self.file_prefix = file_name_wo_extension(self.simplified_file)

    def check_args(self, args):
        if args.infile is None:
            raise MessageError("Input argument is missing. (try ./vac.py -h)")
        if not os.path.isfile(args.infile):
            raise MessageError("Input file does not exists")
        # WARNING: Quite restrictive. We can try to create the folder
        if args.working_dir is not None and os.path.isdir(args.working_dir):
            raise MessageError("Working directory does not exists.")
        # WARNING: maybe not needed if you consider searching in /tmp
        if args.preserve_tool_answer and args.working_dir is None:
            raise MessageError("Cannot save tool answer in /tmp.")

        if args.overapprox_backend not in overapprox_backends:
            raise MessageError("The selected over-approximate backend must be in {}".format(overapprox_backends))
        if args.underapprox_backend not in underapprox_backends:
            raise MessageError("The selected under-approximate backend must be in {}".format(underapprox_backends))
        if args.complete_backend not in complete_backends:
            raise MessageError("The precise backend backend must be in {}".format(complete_backends))
        if args.backend is not None and args.backend not in backends:
            raise MessageError("The selected backend must be in {}".format(backends))

        if (args.underapprox_backend is "cbmc" or args.backend is "cbmc") and \
            (args.unwind is None or args.unwind < 1):
            raise MessageError("CBMC backend requires the unwind option to be greater than 0")


        if (args.overapprox_backend is "interproc" or args.backend is "interproc") and \
                (args.interproc_w_delay is None or args.interproc_w_delay < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_delay option to be greater than 0")
        if (args.overapprox_backend is "interproc" or args.backend is "interproc") and \
                (args.interproc_w_steps is None or args.interproc_w_steps < 1):
            raise MessageError("INTERPROC backend requires the interproc_w_steps option to be greater than 0")

        if (args.underapprox_backend is "mucke" or
            (args.backend is not None and args.backend is "mucke")):
            if args.mucke_bddlib is None or args.mucke_bddlib not in mucke_bddlibs:
                raise MessageError("MUCKE backend requires the mucke_bddlib option to be set and in choiches")
            if args.mucke_rounds is None or args.mucke_rounds < 1:
                raise MessageError("MUCKE backend requires the mucke_rounds option to be set and greater than 0")
            if args.mucke_formula is None or not os.path.isfile(args.mucke_formula):
                raise MessageError("MUCKE backend requires the mucke_formula option to be a valid file")

        if args.print_translated is not None and args.print_translated not in backends:
            raise MessageError("The selected format must be in {}".format(backends))

        if args.print_translated and args.no_pruning:
            raise MessageError("Cannot print a not pruned policy. Consider cat {}".format(args.infile))


def str_time(timespan):
    hours, rem = divmod(timespan, 3600)
    minutes, seconds = divmod(rem, 60)
    return "{:0>2}:{:0>2}:{:06.3f}".format(int(hours),int(minutes),seconds)


def execute_get_time(f, args=None):
    start = time.time()
    res = f() if args is None else f(args)
    elapsed = time.time() - start
    return res, elapsed


def execute_print_time(f, args, fmt="Operation executed in {}"):
    res, elapsed = execute_get_time(f, args)
    print(fmt.format(str_time(elapsed)))
    return res

def defaultAlgorithm(inputfile):
    print "=====> Simplification ARBAC policy =====>"
    simplifyCMD = vacexec['simplify'] + ' -g ' + inputfile
    prunedfile = inputfile + '_reduceAdmin.arbac'
    debugfile = inputfile + '_debug'
    cmd = Command(simplifyCMD)
    out, err, code = cmd.run(86400)
    if 'error' in (out + err):
        print out + err
        print "Error: please input correct ARBAC policy."
        shutil.rmtree(prunedfile, ignore_errors=True)
        shutil.rmtree(debugfile, ignore_errors=True)

    print "=====> Translation ARBAC policy =====>"
    translateCMD = vacexec['translate'] + ' -f interproc -a abstract ' + prunedfile
    translatedfile = prunedfile + '_OverApx_INTERPROC.cpp'
    cmd = Command(translateCMD)
    out, err, code = cmd.run(86400)

    print "=====> Analysis of translated ARBAC policy =====>"
    verifyCMD = backendExec['interproc'] + backendOptions['interproc'] + translatedfile
    cmd = Command(verifyCMD)
    out, err, code = cmd.run(86400)
    if backendAnswerFAIL['interproc'] in out:
        print "The ARBAC policy may not be safe."
        print "===> Under approximate analysis ===>"
        translateCMD = vacexec['translate'] + ' -f cbmc -a precise ' + prunedfile
        translatedfile = prunedfile + '_ExactAlg_CBMC.c'
        cmd = Command(translateCMD)
        out, err, code = cmd.run(86400)

        verifyCMD = backendExec['cbmc'] + backendOptions['cbmc'] + " 2 --xml-ui " + translatedfile
        xmllogfile = inputfile + '_log.xml'
        cmd = Command(verifyCMD)
        out, err, code = cmd.run(86400)
        saveFile(xmllogfile, out + err)

        cexCMD = vacexec['cex'] + ' '.join([xmllogfile, translatedfile, prunedfile, debugfile, inputfile])
        cmd = Command(cexCMD)
        out, err, code = cmd.run(86400)
        if 'no Counter Example' in out:
            print "===> Complete Analysis ===>"
            translateCMD = vacexec['translate'] + ' -f smt -a precise ' + prunedfile
            translatedfile = prunedfile + '_ExactAlg_SMT.smt2'
            cmd = Command(translateCMD)
            out, err, code = cmd.run(86400)
            verifyCMD = backendExec['z3'] + backendOptions['z3'] + translatedfile
            cmd = Command(verifyCMD)
            out, err, code = cmd.run(86400)
            if backendAnswerFAIL['z3'] in out:
        # TODO


class Backends:
    def __init__(self): pass
    over_approx_backends = [] # ["interproc"]
    under_approx_backends = [] # ["cbmc", "mucke"]
    precise_backends = [] # ["z3", "hsf", "eldarica", "nusmv", "moped", "seahorn"]
    all_backends = over_approx_backends + under_approx_backends + precise_backends

    def over_approx_backends_names(self):
        return map(lambda b: b.name, self.over_approx_backends)
    def under_approx_backends_names(self):
        return map(lambda b: b.name, self.under_approx_backends)
    def precise_backends_names(self):
        return map(lambda b: b.name, self.precise_backends)
    def all_backends_names(self):
        return map(lambda b: b.name, self.all_backends)


def full_check_simpl():
    if not Config.no_pruning:
        l.info("=====> Simplification ARBAC policy =====>")
        simplify()
    else:
        shutil.copy(Config.infile, Config.simplified_file)

def full_check_analysis():
    l.info("=====> Over approximate analysis of ARBAC policy using {} =====>".format(Config.overapprox_backend.name))
    overapprox_res = Config.overapprox_backend.run()
    print_result(overapprox_res)
    if overapprox_res == Result.SAFE:
        return False

    l.info("=====> Under approximate analysis of ARBAC policy using {} =====>".format(Config.underapprox_backend.name))
    underapprox_res = Config.underapprox_backend.run()
    print_result(underapprox_res)
    if underapprox_res == Result.UNSAFE:
        return True

    l.info("=====> Precise analysis of ARBAC policy using {} =====>".format(Config.precise_backend.name))
    precise_res = Config.precise_backend.run()
    print_result(precise_res)
    if precise_res == Result.SAFE:
        return False
    elif precise_res == Result.UNSAFE:
        return True

    raise UnexpectedError("Should be exited before...")

def full_check_counterexample():
    l.info("=====> Generating counter example.. =====>")
    if :
        #TODO: Continue counterexample

def single_check():
    if not Config.no_pruning:
        l.info("=====> Simplification ARBAC policy =====>")
        simplify()
    else:
        shutil.copy(Config.infile, Config.simplified_file)

    l.info("=====> Running analysis of ARBAC policy using {} =====>".format(Config.backend.name))
    backend_res = Config.backend.run()
    print_result(backend_res)


def at_sig_halt(signal=None, frame=None):
    sys.stderr.write("\nKilled by the user.\n")
    clean()


def clean():
    if not Config.preserve_artifacts:
        shutil.rmtree(Config.working_dir)

def main():
    #global config
    Config.set()

    if Config.version:
        print(VACDESCRIPTION)
        sys.exit(0)

    # register anti-panic handlers
    signal.signal(signal.SIGINT, at_sig_halt)
    atexit.register(clean)

    # configure how logging should be done

    starttime = time.time()

    if len(sys.argv) == 2:
        defaultAlgorithm(inputfile)
    else:
        customAlgorithm(inputfile, args)

    print "Elapse time: %0.2f" % (time.time() - starttime)


if __name__ == '__main__':
    main()

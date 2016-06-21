#!/usr/bin/env python
'''
    Wrapper script for VAC

ChangeLog:
    2016.05.19   Initial version based on old script vac.sh

'''
import argparse
import sys
import os
import os.path
import signal
import subprocess
import threading
import shutil
import time


VACDESCRIPTION = '''\
* *               VAC 1.0 - Verifier of Access Control                * *
* *                                                                   * *
* *            Anna Lisa Ferrara (1), P. Madhusudan (2),              * *
* *           Truc L. Nguyen (3), and Gennaro Parlato (3).            * *
* *                                                                   * *
* * (1) University of Bristol (UK), (2) University of Illinois (USA), * *
* *               and (3) University of Southampton (UK)              * *

Usage:
    vac.py [options] infile

'''

EPILOG = '''
VAC without any option runs the default option:
it first runs the abstract transformer followed by Interproc;
if a proof cannot be provided, VAC runs the precise transformer
followed by CBMC (unwind set to 2) to look for a counterexample.
Otherwise, it executes SeaHorn for complete analysis.
'''


'''
    Backend parameter and options
'''
backendExec = {}
backendExec['interproc'] = './bin/interproc'
backendExec['cbmc'] = './bin/cbmc'
backendExec['z3'] = './bin/z3'

backendOptions = {}
backendOptions['interproc'] = ' -domain box '
backendOptions['cbmc'] = ' --no-unwinding-assertions --unwind '
backendOptions['z3'] = ' -smt2 '

backendAnswerOK = {}
backendAnswerOK['interproc'] = 'not safe'
backendAnswerOK['cbmc'] = 'VERIFICATION SUCCESSFUL'
backendAnswerOK['z3'] = 'sat'

backendAnswerFAIL = {}
backendAnswerFAIL['interproc'] = 'safe'
backendAnswerFAIL['cbmc'] = 'VERIFICATION FAILED'
backendAnswerFAIL['z3'] = 'unsat'

vacexec = {}
vacexec["simplify"] = './bin/simplify'
vacexec["translate"] = './bin/translate'
vacexec["cex"] = './bin/counterexample'


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


def main():
    parser = argparse.ArgumentParser(description=VACDESCRIPTION,
                                     epilog=EPILOG,
                                     formatter_class=argparse.RawDescriptionHelpFormatter,
                                     usage=argparse.SUPPRESS)
    parser.add_argument('infile', help='input policy', nargs='*')
    parser.add_argument('-n', '--no-pruning', help='no simplification procedure (default No)', dest='nopruning', action='store_true', default=False)
    parser.add_argument('-b', '--backend', metavar='X', help='backend (interproc, z3, hsf, eldarica, nusmv, moped, seahorn, cbmc)', type=str, dest='backend', default='')
    parser.add_argument('-u', '--unwind', metavar='X', help='unwind X times (CBMC only)', type=int, dest='unwind', default=2)
    parser.add_argument('--print-pruned-policy', help='print simplified policy only', dest='printpruned', default=False, action='store_true')
    parser.add_argument('--print-translated-policy', metavar='X', help='print the translated program in the format X (interproc, z3, hsf, eldarica, nusmv, moped, seahorn, cbmc)', dest='printtranslated', type=str, default='')
    parser.add_argument('--mohawk', help='print equivalent Mohawk benchmark', dest='mohawk', default=False, action='store_true')

    # Parse the option
    args = parser.parse_args()
    # print args
    if len(args.infile) == 0:
        print "Error: please specify the input policy"
    if len(args.infile) > 1:
        print "Error: please specify only one input policy"

    inputfile = args.infile[0]

    if not os.path.isfile(inputfile):
        print "Error: please specify the correct input policy"

    starttime = time.time()

    if len(sys.argv) == 2:
        defaultAlgorithm(inputfile)
    else:
        customAlgorithm(inputfile, args)

    print "Elapse time: %0.2f" % (time.time() - starttime)


if __name__ == '__main__':
    main()

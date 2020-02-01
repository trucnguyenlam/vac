#!/usr/bin/env python
import shlex, signal, subprocess, threading
import os
import sys
import getopt
import time
from time import sleep, gmtime, strftime


class colors:
    BLINK = '\033[5m'
    BLACK = '\033[90m'
    DARKRED = '\033[31m'
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    NO = '\033[0m'


def saveFile(filename, string):
    outfile = open(filename,"w")
    outfile.write(string)
    outfile.close()


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
                ###self.process.terminate()
                ##os.killpg(self.process.pid, signal.SIGTERM)
                os.killpg(self.process.pid, signal.SIGKILL)
                thread.join()
        except KeyboardInterrupt:
            self.process.kill()

        return self.output, self.stderr, self.process.returncode


def printStats(match, file, result, time):
    if result == 'UNKNOWN':
        result = colors.YELLOW + result + colors.NO
    elif result == 'NOT_REACHABLE':
        result = colors.GREEN + result + colors.NO
    elif result == 'REACHABLE':
        result = colors.RED + result + colors.NO

    print "%s, %s, %s, %0.2f" % (match, file, result, time)


def main(inputlist):
    logfilename = 'temp.log'
    with open(inputlist, "r") as listtest:
        for l in listtest.read().splitlines():
            if l.strip() != '' and not l.strip().startswith('#'):
                inputfile = l.split()[1]
                checkcmd = './vac.sh ' + inputfile
                command = Command(checkcmd)
                out, err, code = command.run(timeout=3600)
                saveFile(logfilename, out)   # klee outputs errors to stdout, all other backends to stderr
                if os.path.isfile(logfilename):
                    myfile = open(logfilename)
                    backendAnswer = list(myfile)
                    outcome = ''
                    for line in backendAnswer:
                        if 'is safe.' in line:
                            outcome = 'NOT_REACHABLE'
                            break
                        elif 'may not be safe.' in line or 'is not safe.' in line:
                            outcome = 'REACHABLE'
                            break
                    if outcome == '' and code == -9:  # backend killed due to timeout
                        outcome = 'TIMEOUT'
                    if outcome == '':
                        outcome = 'UNKNOWN'
                expectoutcome = outcome
                expectoutcome_decorated = expectoutcome
                if expectoutcome == 'UNKNOWN':
                    expectoutcome_decorated = colors.YELLOW + expectoutcome + colors.NO
                elif expectoutcome == 'NOT_REACHABLE':
                    expectoutcome_decorated = colors.GREEN + expectoutcome + colors.NO
                elif expectoutcome == 'REACHABLE':
                    expectoutcome_decorated = colors.RED + expectoutcome + colors.NO

                print "command: " + l + ', expect %s' % expectoutcome_decorated
                cmdline = l
                realstarttime = time.time()    # save wall time
                command = Command(cmdline)
                out, err, code = command.run(timeout=3600)
                saveFile(logfilename, out)   # klee outputs errors to stdout, all other backends to stderr
                overalltime = time.time() - realstarttime

                # report analysis details
                if os.path.isfile(logfilename):
                    myfile = open(logfilename)
                    backendAnswer = list(myfile)
                    outcome = ''
                    for line in backendAnswer:
                        if 'is not safe.' in line:
                            outcome = 'REACHABLE'
                            break
                        elif 'is safe.' in line:
                            outcome = 'NOT_REACHABLE'
                            break
                    if outcome == '' and code == -9:  # backend killed due to timeout
                        outcome = 'TIMEOUT'
                    if outcome == '':
                        outcome = 'UNKNOWN'
                    result = True
                    if expectoutcome != outcome:
                        result = False
                    printStats(result, inputfile, outcome, overalltime)


if __name__ == '__main__':
    main(sys.argv[1])

import time
import subprocess
import threading
import os
import signal
import shutil
import sys


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
                os.killpg(self.process.pid, signal.SIGKILL)
                thread.join()
        except KeyboardInterrupt:
            self.process.kill()

        return self.output, self.stderr, self.process.returncode

def readLog(logfile):
    header = 'ARBAC system before pruning:'
    footer = 'ARBAC system after reducing:'

    with open(logfile, "r") as log:
        lines = log.read().splitlines()
        for i, l in enumerate(lines):
            if header in l:
                rline = lines[i + 1]
                uline = lines[i + 2]
                ruleline = lines[i + 5]
                roles = int(rline[rline.rfind(' ')+1:])
                users = int(uline[uline.rfind(' ')+1:])
                rules = int(ruleline[ruleline.rfind(' ')+1:])
                print "BEFORE PRUNING: Roles: %s Users: %s Rules: %s" % (roles, users, rules)
            if footer in l:
                rline = lines[i + 1]
                uline = lines[i + 2]
                ruleline = lines[i + 5]
                roles = int(rline[rline.rfind(' ')+1:])
                users = int(uline[uline.rfind(' ')+1:])
                rules = int(ruleline[ruleline.rfind(' ')+1:])
                print "AFTER PRUNING: Roles: %s Users: %s Rules: %s" % (roles, users, rules)


def singleTest(inputfile, BackendTest):
    print "============= %s ==================" % inputfile
    backend = ("cbmc", "moped", "nusmv", "hsf", "eldarica", "z3", "interproc")
    #  Launch VAC default
    cmd = "./vac.sh %s" % inputfile
    command = Command(cmd)
    timestart = time.time()
    out, err, code = command.run(timeout=1200)
    timeend = time.time() - timestart

    print out
    print "DEFAULT IN TIME %.3fs" % timeend

    if BackendTest == "yes":
        print "-- BACKEND --"
        #  For each backend
        for b in backend:
            #  first the translation
            cmd = "./vac.sh --print-translated-policy=%s %s" % (b, inputfile)
            command =  Command(cmd)
            out, err, code = command.run(timeout=1200)

            #  Second the backend
            cmd2 = ''
            translatedfile = inputfile
            if b == "interproc":
                cmd2 = './bin/interproc -domain box '
                translatedfile += "translated.cpp"
            elif b == "moped":
                cmd2 = './bin/moped -b '
                translatedfile += "translated.bp"
            elif b == "z3":
                cmd2 = './bin/z3 -smt2 '
                translatedfile += "translated.smt2"
            elif b == "cbmc":
                cmd2 = './bin/cbmc --unwind 2 --no-unwinding-assertions '
                translatedfile += "translated.c"
            elif b == "hsf":
                cmd2 = './bin/qarmc '
                translatedfile += "translated.qarmc"
            elif b == "nusmv":
                cmd2 = './bin/NuSMV  '
                translatedfile += "translated.smv"
            elif b == "eldarica":
                cmd2 = 'java -jar ./bin/eldarica-2063.jar -horn -hin -princess -bup -n '
                translatedfile += "translated.horn"

            with open(translatedfile, "w") as outfile:
                outfile.write(out)

            # Launch command
            cmd2 += translatedfile

            command = Command(cmd2)
            starttime = time.time()
            out, err, code = command.run(timeout=1200)
            endtime = time.time() - starttime

            os.remove(translatedfile)

            answer = ''
            #  Interpret answer
            if b == "interproc":
                if 'not safe' in out:
                    answer = "UNSAFE"
                elif 'safe' in out:
                    answer = "SAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "moped":
                if 'Not reachable.' in out:
                    answer = "SAFE"
                elif 'Reachable.' in out:
                    answer = "UNSAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "z3":
                if 'unsat' in out:
                    answer = "UNSAFE"
                elif 'sat' in out:
                    answer = "SAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "cbmc":
                if 'VERIFICATION SUCCESSFUL' in out:
                    answer = "SAFE"
                elif 'VERIFICATION FAILED' in out:
                    answer = "UNSAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "hsf":
                if 'not correct' in out:
                    answer = "UNSAFE"
                elif 'correct' in out:
                    answer = "SAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "nusmv":
                if 'is false' in out:
                    answer = "UNSAFE"
                elif 'is true' in out:
                    answer = "SAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'
            elif b == "eldarica":
                if 'NOT SOLVABLE' in out:
                    answer = "UNSAFE"
                elif 'SOLVABLE' in out:
                    answer = "SAFE"
                elif code == -9:
                    answer = 'TIMEOUT'
                else:
                    print err
                    answer = 'ERROR'

            print "BACKEND: %s, TIME: %.3fs, ANWSER: %s" % (b, endtime, answer)

    #  Launch simplify - get the simplified file
    logfile = inputfile + ".log"
    cmd = "./bin/simplify -l %s %s" % (logfile, inputfile)
    command = Command(cmd)
    timestart = time.time()
    out, err, code = command.run(timeout=1200)
    endtime = time.time() - timestart
    print "-- PRUNING --"
    readLog(logfile)
    print "PRUNING TIME: %.3fs" % endtime
    os.remove(logfile)

if __name__ == '__main__':
    singleTest(sys.argv[1], sys.argv[2])

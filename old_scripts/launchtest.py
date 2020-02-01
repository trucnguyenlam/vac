import subprocess
import sys
import os
import os.path
import signal
import threading


class Command(object):
    status = None
    output = stderr = ''

    def __init__(self, cmdline):
        self.cmd = cmdline
        self.process = None

    def run(self, timeout):
        def target():
            # Thread started
            self.process = subprocess.Popen(
                self.cmd, shell=True, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
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
            self.process.kill()

        return self.output, self.stderr, self.process.returncode


def launchonetest(inputfile, backend):
    var1 = var2 = ''
    result = ''
    # print "======================="
    cmd1 = './vac.sh --backend=%s %s' % (backend, inputfile)
    if(backend == "cbmc"):
        cmd1 += " --unwind=3"
    # print cmd1,
    command = Command(cmd1)
    out, err, code = command.run(timeout=180)
    if 'not' in out:
        print " ==> UNSAFE",
        result = 'UNSAFE'
        var1 = False
    elif 'safe' in out:
        result = 'SAFE'
        print " ==> SAFE",
        var1 = True
    elif code == -9:
        print " ==> TIMEOUT",
    else:
        print " ==> WRONG TRANSLATION FILE",

    cmd2 = './vac.sh --backend=%s %s --no-pruning' % (backend, inputfile)
    if(backend == "cbmc"):
        cmd2 += " --unwind=3"
    # print cmd1,
    command = Command(cmd2)
    out, err, code = command.run(timeout=180)
    if 'not' in out:
        print " ==> UNSAFE",
        var2 = False
    elif 'safe' in out:
        print " ==> SAFE",
        var2 = True
    elif code == -9:
        print " ==> TIMEOUT",
    else:
        print " ==> WRONG TRANSLATION FILE",

    if var1 == var2:
        print "OK"
        return result
    else:
        print "TROUBLE"

    return result


def all_same(items):
    return all(x == items[0] for x in items)


def lauchTest(inputfile):
    print "===== %s =====" % inputfile
    cmd = './vac.sh %s' % inputfile
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    print out + err

    overall = []
    interproc = ''
    # for b in ("interproc", "moped", "z3", "cbmc", "hsf", "eldarica"):
    for b in ("interproc", "moped", "z3", "cbmc", "hsf", "nusmv", "eldarica"):
        print "Test with backend", b,
        result = launchonetest(inputfile, b)
        if b == "interproc":
            interproc = result
        if b in ("moped", "z3", "hsf", "nusmv", "eldarica"):
            overall.append(result)

    if all_same(overall):
        if interproc == 'SAFE' and interproc in overall:
            print "*********CONSISTENT******************\n"
        elif interproc == 'SAFE' and interproc not in overall:
            print "^^^^^^^^^INCONSISTENT^^^^^^^^^^^^^^^^\n"
        else:
            print "*********CONSISTENT******************\n"
    else:
        print "^^^^^^^^^INCONSISTENT^^^^^^^^^^^^^^^^\n"


if __name__ == '__main__':
    for f in sorted(os.listdir(sys.argv[1])):
        if f.endswith('.arbac'):
            print sys.argv[1] + f
            lauchTest(sys.argv[1] + f)

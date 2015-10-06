import subprocess
import sys
import os
import os.path


def launchonetest(inputfile, backend):
    var1 = var2 = ''
    result = ''
    # print "======================="
    cmd1 = './vac.sh --backend=%s %s' % (backend, inputfile)
    if(backend == "cbmc"):
        cmd1 += " --unwind=3"
    # print cmd1,
    p = subprocess.Popen(cmd1, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    if 'not' in out:
        print " ==> UNSAFE",
        result = 'UNSAFE'
        var1 = False
    elif 'safe' in out:
        result = 'SAFE'
        print " ==> SAFE",
        var1 = True
    else:
        print " ==> WRONG TRANSLATION FILE",

    cmd1 = './vac.sh --backend=%s %s --no-pruning' % (backend, inputfile)
    if(backend == "cbmc"):
        cmd1 += " --unwind=3"
    # print cmd1,
    p = subprocess.Popen(cmd1, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    if 'not' in out:
        print " ==> UNSAFE",
        var2 = False
    elif 'safe' in out:
        print " ==> SAFE",
        var2 = True
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
    for b in ("interproc", "moped", "z3", "cbmc", "hsf", "eldarica"):
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

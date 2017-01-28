import subprocess
import time


def launchUnit(cmd):
    starttime = time.time()
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    endtime = time.time() - starttime
    # code = p.returncode
    if 'is safe' in out:
        print cmd[cmd.rfind('/')+1:], 'SAFE', '%0.3fs' % endtime
    else:
        print cmd[cmd.rfind('/')+1:], 'UNSAFE', '%0.3fs' % endtime,
        if 'Counter Example Trace' in out:
            print "SUCCESSFUL CEX"
        else:
            print "UNCESSESSFUL CEX"


def main():
    print "=============="
    print "Hospital"
    print "=============="
    cmd = './vac.sh ../regression/original/Hospital/Hospital1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Hospital/Hospital2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Hospital/Hospital3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Hospital/Hospital4.arbac'
    launchUnit(cmd)
    print "=============="
    print "University"
    print "=============="
    cmd = './vac.sh ../regression/original/University/University1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/University/University2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/University/University3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/University/University4.arbac'
    launchUnit(cmd)
    print "=============="
    print "Bank"
    print "=============="
    cmd = './vac.sh ../regression/original/Bank/Bank1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Bank/Bank2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Bank/Bank3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/original/Bank/Bank4.arbac'
    launchUnit(cmd)
    print "=============="
    print "Mohawk EASY TEST MIXED"
    print "=============="
    cmd = './vac.sh ../regression/testcases/mixed/test1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test4.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test5.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test6.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test7.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test8.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test9.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixed/test10.arbac'
    launchUnit(cmd)
    print "=============="
    print "Mohawk EASY TEST MIXEDNOCR"
    print "=============="
    cmd = './vac.sh ../regression/testcases/mixednocr/test1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test4.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test5.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test6.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test7.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test8.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test9.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/mixednocr/test10.arbac'
    launchUnit(cmd)
    print "=============="
    print "Mohawk EASY TEST POSITIVE"
    print "=============="
    cmd = './vac.sh ../regression/testcases/positive/test1.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test2.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test3.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test4.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test5.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test6.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test7.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test8.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test9.arbac'
    launchUnit(cmd)
    cmd = './vac.sh ../regression/testcases/positive/test10.arbac'
    launchUnit(cmd)

if __name__ == '__main__':
    main()

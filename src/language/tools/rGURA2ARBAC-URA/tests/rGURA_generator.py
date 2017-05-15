import random

# Generating random RGURA policy


density = {
    "sattrs": 70,
    "mattrs": 70,
    "assign": 70,
    "add": 70,
    "not": 30
}


def getChoiceByPercentage(percentage):
    a = percentage * [True] + (100 - percentage) * [False]
    return random.choice(a)


def TrueOrFalse():
    return random.choice([True, False])


def generateTest(inputfile,
                 nusers,
                 nsingleattrs,
                 nmultiattrs,
                 max_sattr_values,
                 max_mattr_values,
                 nadminroles,
                 nassign_rules,
                 nadd_rules,
                 ndelete_rules
                 ):
    ''' This generator retrieve
        @nuser: number of users
        @nsingleattrs: number of single-value attributes
        @nmultiattrs: number of multi-value attributes
        @max_sattr_values: max |domain| size of each single-value attribute
        @max_mattr_values: max |domain| size of each multi-value attribute
        @nadminroles: number of admin roles

    '''
    s_attr_val_dict = {}
    m_attr_val_dict = {}

    with open(inputfile, "w") as out:
        # USERS
        out.write("USERS\n")
        for i in xrange(nusers):
            out.write("user%s\n" % i)
        out.write(";\n")

        # Single attributes
        out.write("ATTRIBUTE_SINGLE\n")
        for i in xrange(nsingleattrs):
            out.write("s_attr%s\n" % i)
            s_attr_val_dict["s_attr%s" % i] = {}
        out.write(";\n")

        # Multiple attributes
        out.write("ATTRIBUTE_MULTIPLE\n")
        for i in xrange(nmultiattrs):
            out.write("m_attr%s\n" % i)
            m_attr_val_dict["m_attr%s" % i] = {}
        out.write(";\n")

        # Scope
        out.write("SCOPE\n")
        # single values
        for i in xrange(nsingleattrs):
            domain_size = random.randint(1, max_sattr_values)
            out.write("<s_attr%s," % i)
            for j in xrange(domain_size):
                out.write(" sa%i_value%s" % (i, j))
                s_attr_val_dict["s_attr%s" % i]["sa%i_value%s" % (i, j)] = True
            out.write(">\n")
        # multiple values
        for i in xrange(nmultiattrs):
            domain_size = random.randint(1, max_mattr_values)
            out.write("<m_attr%s," % i)
            for j in xrange(domain_size):
                out.write(" ma%i_value%s" % (i, j))
                m_attr_val_dict["m_attr%s" % i]["ma%i_value%s" % (i, j)] = True
            out.write(">\n")
        out.write(";\n")

        # UATTR_S
        out.write("UATTR_S\n")
        for u in xrange(nusers):           # for each user
            s = "user%s" % u
            a = ""
            for i in xrange(nsingleattrs):    # for each single attribute
                if getChoiceByPercentage(density["sattrs"]):
                    a += " <s_attr%s, " % i
                    j = random.randint(0, len(s_attr_val_dict['s_attr%s' % i]) - 1)
                    a += "sa%s_value%s>" % (i, j)
            if a != "":
                out.write(s + a + "\n")
        out.write(";\n")

        # UATTR_M
        out.write("UATTR_M\n")
        for u in xrange(nusers):           # for each user
            s = "user%s" % u
            a = ""
            for i in xrange(nmultiattrs):    # for each multi attribute
                if getChoiceByPercentage(density["mattrs"]):
                    a += " <m_attr%s" % i
                    jlist = random.sample(
                        xrange(len(m_attr_val_dict['m_attr%s' % i])),
                        random.randint(1, len(m_attr_val_dict['m_attr%s' % i])))
                    for j in jlist:
                        a += ", ma%s_value%s" % (i, j)
                    a += ">"
            if a != "":
                out.write(s + a + "\n")
        out.write(";\n")

        # adminrole
        out.write("ADMINROLES\n")
        for a in xrange(nadminroles):
            out.write("admin%s\n" % (a))
        out.write(";\n")

        # rules
        out.write("RULES\n")
        # assign
        for repeat in xrange(nassign_rules):
            adminid = random.randint(0, nadminroles - 1)
            attrid = random.randint(0, nsingleattrs - 1)
            targetid = random.randint(0, len(s_attr_val_dict["s_attr%s" % attrid]) - 1)
            # precondition
            precond = ""
            if getChoiceByPercentage(1):
                precond = "TRUE"
            else:
                for s in xrange(nsingleattrs):
                    if getChoiceByPercentage(density["assign"]) and s != attrid:
                        v = random.randint(0, len(s_attr_val_dict["s_attr%s" % s]) - 1)
                        if getChoiceByPercentage(density['not']):
                            precond += "not "
                        precond += "s_attr%s=sa%s_value%s & " % (s, s, v)
                for m in xrange(nmultiattrs):
                    if getChoiceByPercentage(density["assign"]):
                        vlist = random.sample(
                            xrange(len(m_attr_val_dict["m_attr%s" % m])),
                            random.randint(1, len(m_attr_val_dict["m_attr%s" % m]))
                        )
                        for v in vlist:
                            if getChoiceByPercentage(density['not']):
                                precond += "not "
                            precond += "m_attr%s=ma%s_value%s & " % (m, m, v)
                if precond.endswith("& "):
                    precond = precond[:-2]  # remove last &
            if precond == "":
                precond = "TRUE"

            out.write("<admin%s, %s, s_attr%s, sa%s_value%s>\n" % (adminid, precond, attrid, attrid, targetid))

        # add
        for repeat in xrange(nadd_rules):
            adminid = random.randint(0, nadminroles - 1)
            attrid = random.randint(0, nmultiattrs - 1)
            targetid = random.randint(0, len(m_attr_val_dict["m_attr%s" % attrid]) - 1)
            # precondition
            precond = ""
            if getChoiceByPercentage(1):
                precond = "TRUE"
            else:
                for s in xrange(nsingleattrs):
                    if getChoiceByPercentage(density["add"]):
                        v = random.randint(0, len(s_attr_val_dict["s_attr%s" % s]) - 1)
                        if getChoiceByPercentage(density['not']):
                            precond += "not "
                        precond += "s_attr%s=sa%s_value%s & " % (s, s, v)
                for m in xrange(nmultiattrs):
                    if getChoiceByPercentage(density["add"]):
                        vlist = random.sample(
                            xrange(len(m_attr_val_dict["m_attr%s" % m])),
                            random.randint(1, len(m_attr_val_dict["m_attr%s" % m]))
                        )
                        for v in vlist:
                            if getChoiceByPercentage(density['not']) and v != targetid:
                                precond += "not "
                            precond += "m_attr%s=ma%s_value%s & " % (m, m, v)
                if precond.endswith("& "):
                    precond = precond[:-2]  # remove last &
            if precond == "":
                precond = "TRUE"
            out.write("<admin%s, %s, m_attr%s, ma%s_value%s>\n" % (adminid, precond, attrid, attrid, targetid))

        # delete
        for repeat in xrange(ndelete_rules):
            adminid = random.randint(0, nadminroles - 1)
            if TrueOrFalse():   # single var
                attrid = random.randint(0, nsingleattrs - 1)
                targetid = random.randint(0, len(s_attr_val_dict["s_attr%s" % attrid]) - 1)
                out.write("<admin%s, s_attr%s, sa%s_value%s>\n" % (
                    adminid, attrid, attrid, targetid
                ))
            else:
                attrid = random.randint(0, nmultiattrs - 1)
                targetid = random.randint(0, len(m_attr_val_dict["m_attr%s" % attrid]) - 1)
                out.write("<admin%s, m_attr%s, ma%s_value%s>\n" % (
                    adminid, attrid, attrid, targetid
                ))
        out.write(";\n")

        out.write("SPEC\n")
        if TrueOrFalse():
            attrid = random.randint(0, nsingleattrs - 1)
            targetid = random.randint(0, len(s_attr_val_dict["s_attr%s" % attrid]) - 1)
            out.write("s_attr%s sa%s_value%s\n" % (attrid, attrid, targetid))
        else:
            attrid = random.randint(0, nmultiattrs - 1)
            targetid = random.randint(0, len(m_attr_val_dict["m_attr%s" % attrid]) - 1)
            out.write("m_attr%s ma%s_value%s\n" % (attrid, attrid, targetid))
        out.write(";\n")


def help():
    print "rGURA_generator.py PATH N_TESTCASES"


if __name__ == '__main__':
    import time
    import sys
    import os
    import os.path

    try:
        path = sys.argv[1]
    except Exception:
        help()
        sys.exit(1)

    try:
        testcases = int(sys.argv[2])
    except Exception:
        help()
        sys.exit(1)

    try:
        os.makedirs(path)
    except OSError:
        if not os.path.isdir(path):
            raise

    random.seed(time.time())
    nusers = random.randint(10, 20)
    nsingleattrs = random.randint(10, 15)
    nmultiattrs = random.randint(5, 10)
    max_sattr_values = random.randint(10, 20)
    max_mattr_values = random.randint(20, 30)
    nadminroles = random.randint(1, 5)
    nassign_rules = random.randint(50, 100)
    nadd_rules = random.randint(50, 100)
    ndelete_rules = random.randint(40, 50)

    for i in xrange(testcases):
        generateTest(path + "/rGURA_random_policy_%s.txt" % str(i).zfill(3),
                     nusers,
                     nsingleattrs,
                     nmultiattrs,
                     max_sattr_values,
                     max_mattr_values,
                     nadminroles,
                     nassign_rules,
                     nadd_rules,
                     ndelete_rules)

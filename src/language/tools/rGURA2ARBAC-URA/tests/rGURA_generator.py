import random

# Generating random RGURA policy


density = {
        "sattrs": 70,
        "mattrs": 70
    }


def getChoiceByPercentage(percentage):
    a = percentage * [True] + (100 - percentage) * [False]
    return random.choice(a)


def generateTest(inputfile,
                 nusers,
                 nsingleattrs,
                 nmultiattrs,
                 max_sattr_values,
                 max_mattr_values,
                 nadminroles
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
            out.write("user%s" % u)
            for i in xrange(nsingleattrs):    # for each single attribute
                if getChoiceByPercentage(density["sattrs"]):
                    out.write(" <s_attr%s, " % i)
                    j = random.randint(0, len(s_attr_val_dict['s_attr%s' % i]))
                    out.write("sa%s_value%s>" % (i, j))
            out.write("\n")
        out.write(";\n")

        # UATTR_M
        out.write("UATTR_M\n")
        for u in xrange(nusers):           # for each user
            out.write("user%s" % u)
            for i in xrange(nmultiattrs):    # for each multi attribute
                if getChoiceByPercentage(density["mattrs"]):
                    out.write(" <m_attr%s, " % i)
                    jlist = random.sample(
                        xrange(len(m_attr_val_dict['m_attr%s' % i])),
                            random.randint(1, len(m_attr_val_dict['m_attr%s' % i])))
                    for j in jlist:
                        out.write("ma%s_value%s" % (i, j))
                    out.write
            out.write("\n")
        out.write(";\n")




        out.write("CR")
        for repeat in xrange(10):
            for r1 in xrange(roles):
                if getChoiceByPercentage(70):
                    r2 = random.choice(xrange(roles))
                    if getChoiceByPercentage(70):
                        out.write("<r%s, r%s>\n" % (r1, r2))
        out.write(";\n")
        out.write("CA")
        for repeat in xrange(10):
            for admin in xrange(roles):
                if getChoiceByPercentage(70):
                    target = random.choice(xrange(roles))
                    if admin != target:
                        # Precondition
                        if getChoiceByPercentage(90):
                            for i in xrange(random.randint(10, 30)):
                                out.write("<r%s," % admin)
                                precond = random.sample(
                                    xrange(roles),
                                    random.randint(1, roles))
                                for index, r in enumerate(precond):
                                    if index != 0:
                                        out.write("&")
                                    if getChoiceByPercentage(60):
                                        out.write("r%s" % r)
                                    else:
                                        out.write("-r%s" % r)
                                out.write(",r%s>\n" % target)
                        elif getChoiceByPercentage(30):
                            out.write("<r%s,TRUE,r%s>\n" % (admin, target))
        out.write(";\n")

        out.write("SPEC")
        if hasNEW:
            if getChoiceByPercentage(50):
                out.write(" newuser%s" % random.randint(0, newusers - 1))
            elif getChoiceByPercentage(30):
                out.write(" u%s" % random.randint(0, users - 1))
        elif getChoiceByPercentage(50):
            out.write(" u%s" % random.randint(0, users - 1))
        out.write(" r%s" % spec)
        out.write(";\n")


if __name__ == '__main__':
    import time
    random.seed(time.time())
    for i in xrange(1000):
        generateTest("rGURA_random_policy_%s.text" % (str(i).zfill(3),
                                                      random.randint(6, 10),
                                                      random.randint(6, 10),
                                                      random.randint(2, 4),
                                                      getChoiceByPercentage(50)))

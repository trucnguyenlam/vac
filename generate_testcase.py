import random


def getChoiceByPercentage(percentage):
    a = percentage * [True] + (100 - percentage) * [False]
    return random.choice(a)


def generateTest(inputfile, roles, users, newusers, hasNEW=False):
    with open(inputfile, "w") as out:
        # spec = ''
        out.write("ROLES")
        for i in xrange(roles):
            out.write(" r%s" % i)
        out.write(";\n")
        out.write("USERS")
        for i in xrange(users):
            out.write(" u%s" % i)
        out.write(";\n")
        if hasNEW:
            for i in xrange(newusers):
                combination = random.sample(xrange(roles), random.randint(1, roles - 2))
                out.write("<newuser%s, %s>\n" % (i, ["r%s" % r for r in combination].join("&")))
        out.write(";\n")

        out.write("UA ")
        for u in xrange(users):
            assignment = random.sample(xrange(roles), random.randint(0, roles - 2))
            for r in assignment:
                out.write("<u%s, r%s>\n" % (u, r))
        out.write(";\n")

        out.write("CR")
        for r1 in xrange(roles):
            r2 = random.choice(xrange(roles))
            if getChoiceByPercentage(50):
                out.write("<r%s, r%s>\n" % (r1, r2))
        out.write(";\n")
        out.write("CA")
        for admin in xrange(roles):
            target = random.choice(xrange(roles))
            if admin != target:
                # Precondition
                if getChoiceByPercentage(60):
                    for i in xrange(random.randint(5, 10)):
                        out.write("<r%s," % admin)
                        precond = random.sample(xrange(roles), random.randint(1, roles))
                        for index, r in enumerate(precond):
                            if index != 0:
                                out.write("&")
                            if getChoiceByPercentage(60):
                                out.write("r%s" % r)
                            else:
                                out.write("-r%s" % r)
                        out.write(",r%s>\n" % target)
                else:
                    out.write("<r%s,TRUE,r%s>\n" % (admin, target))
        out.write(";\n")

        out.write("SPEC")
        if hasNEW:
            if getChoiceByPercentage(50):
                out.write(" newuser%s" % random.randint(0, newusers - 1))
            elif getChoiceByPercentage(30):
                out.write(" user%s" % random.randint(0, users - 1))
        elif getChoiceByPercentage(50):
            out.write(" u%s" % random.randint(0, users - 1))

        out.write(" role%s" % random.randint(0, roles - 1))
        out.write(";\n")


if __name__ == '__main__':
    for i in xrange(1000):
        generateTest("generated_%s.arbac" % str(i).zfill(3), random.randint(3, 5), random.randint(3, 5), random.randint(3, 5), getChoiceByPercentage(40))

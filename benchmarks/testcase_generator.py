import random


def getChoiceByPercentage(percentage):
    a = percentage * [True] + (100 - percentage) * [False]
    return random.choice(a)


def generateTest(inputfile, roles, users, newusers, hasNEW=False):
    with open(inputfile, "w") as out:
        spec = random.randint(0, roles - 1)
        out.write("ROLES")
        for i in xrange(roles):
            out.write(" r%s" % i)
        out.write(";\n")
        out.write("USERS")
        for i in xrange(users):
            out.write(" u%s" % i)
        out.write(";\n")

        if hasNEW:
            out.write("NEWUSERS")
            for i in xrange(newusers):
                combination = random.sample(xrange(roles), random.randint(1, roles - 2))
                if getChoiceByPercentage(80):
                    if spec not in combination:
                        out.write("<newuser%s, %s>\n" % (i, "&".join(["r%s" % r for r in combination])))
            out.write(";\n")

        out.write("UA ")
        for u in xrange(users):
            if getChoiceByPercentage(80):
                assignment = random.sample(xrange(roles), random.randint(0, roles - 2))
                for r in assignment:
                    if spec != r:
                        out.write("<u%s, r%s>\n" % (u, r))

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
                                precond = random.sample(xrange(roles), random.randint(1, roles))
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
    for i in xrange(10):
        generateTest("generated_%s.arbac" % str(i).zfill(3), random.randint(100, 200), random.randint(300, 400), random.randint(0, 0), getChoiceByPercentage(0))

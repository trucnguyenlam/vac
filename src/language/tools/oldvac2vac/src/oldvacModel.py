

class Policy:

    def __init__(self):
        self.users = []
        self.newusers = []
        self.roles = []
        self.admins = []
        self.hier = Hierarchy()
        self.ca_rules = []
        self.cr_rules = []
        self.spec = Spec()

    def __str__(self):
        ret = ""
        ret += "Users:\n" + "\n".join([str(u) for u in self.users]) + '\n'
        ret += "Roles:\n" + "\n".join([str(u) for u in self.roles]) + '\n'
        ret += "Hierarchy:\n" + str(self.hier) + '\n'
        ret += "CA Rules:\n" + "\n".join([str(u)
                                          for u in self.ca_rules]) + '\n'
        ret += "CR Rules:\n" + "\n".join([str(u)
                                          for u in self.cr_rules]) + '\n'
        return ret


class User:

    def __init__(self, username):
        self.name = username

    def __str__(self):
        return self.name


class NewUser:

    def __init__(self, username, configs):
        self.name = username
        self.configs = configs

    def __str__(self):
        return "<%s, " % self.name + " ".join(self.configs) + ">"


class Spec:

    def __init__(self, goaluser, goalrole):
        self.goaluser = goaluser
        self.goalrole = goalrole


class Role:

    def __init__(self, rolename):
        self.name = rolename

    def __str__(self):
        return self.name


class Hierarchy:

    def __init__(self):
        self._smaller_orders = {}
        self._larger_orders = {}

    def addPartialOrder(self, l, r):
        ''' @parameter
                l: inferior role
                r: superior role
        '''
        if l in self._smaller_orders:
            self._smaller_orders[l].append(r)
        else:
            self._smaller_orders[l] = []
            self._smaller_orders[l].append(r)

        if r in self._larger_orders:
            self._larger_orders[r].append(l)
        else:
            self._larger_orders[r] = []
            self._larger_orders[r].append(l)

    def getSuperiorRoles(self, r):
        if r in self._smaller_orders:
            return self._smaller_orders[r]
        else:
            return []

    def getInferiorRoles(self, r):
        if r in self._larger_orders:
            return self._larger_orders[r]
        else:
            return []

    def __str__(self):
        ret = ""
        for l in self._smaller_orders:
            for r in self._smaller_orders[l]:
                ret += l + ' < ' + r + '\n'
        return ret


class CARule:

    def __init__(self, admin, precondition, target):
        self.admin = admin
        self.precondition = precondition
        self.target = target

    def __str__(self):
        return "<%s, %s, %s>" % (
            self.admin, str(self.precondition), self.target)

    def toVACRule(self):
        ret = ""
        ret += "<"
        ret += "x." + self.admin + "=1"
        if not self.precondition.isTrue:
            for c in self.precondition.conjunct:
                value = "0" if c.negative else "1"
                ret += " & " + "y." + c.name + value
        ret += ", y." + self.target + "=1"
        ret += ">"
        return ret

    def toVACRuleWithHierarchy(self, hier):
        ret = ""
        ret += "<"
        ret += "(x.%s=1" % self.admin
        for sr in hier.getSuperiorRoles(self.admin):
            ret += " | x.%s=1" % sr
        ret += ')'
        if not self.precondition.isTrue:
            for c in self.precondition.conjunct:
                if not c.negative:
                    ret += " & (y.%s=0" % c.name
                    for sr in hier.getSuperiorRoles(c.name):
                        ret += " & y.%s=0" % sr
                    ret += ")"
                else:
                    ret += " & (y.%s=1" % c.name
                    for sr in hier.getSuperiorRoles(c.name):
                        ret += " | y.%s=1" % sr
                    ret += ")"
        ret += ", y." + self.target + "=1"
        ret += ">"
        return ret


class Precondition:

    def __init__(self, isTrue, conjunct):
        self.isTrue = isTrue
        self.conjunct = conjunct

    def __str__(self):
        if self.isTrue:
            return "TRUE"
        else:
            return " & ".join([str(l) for l in self.conjunct])


class Literal:

    def __init__(self, name, negative):
        self.name = name
        self.negative = negative

    def __str__(self):
        return self.name if not self.negative else '-' + self.name


class CRRule:

    def __init__(self, admin, target):
        self.admin = admin
        self.target = target

    def __str__(self):
        return "<" + self.admin + ',' + self.target + '>'

    def toVACRule(self):
        ret = "<x.%s=1, y.%s=0>" % (self.admin, self.target)
        return ret

    def toVACRuleWithHierarchy(self, hier):
        ret = ""
        ret += "<x.%s=1" % self.admin
        for sr in hier.getSuperiorRoles(self.admin):
            ret += " | x.%s=1" % sr
        ret += ', y.%s=0>' % self.target
        return ret

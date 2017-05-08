

class Policy:

    def __init__(self):
        self.users = []
        self.roles = []
        self.hier = Hierarchy()
        self.pras = []
        self.ca_rules = []
        self.cr_rules = []
        self.smers = []
        self.queries = []

    def __str__(self):
        ret = ""
        ret += "Users:\n" + "\n".join([str(u) for u in self.users]) + '\n'
        ret += "Roles:\n" + "\n".join([str(u) for u in self.roles]) + '\n'
        ret += "Hierarchy:\n" + str(self.hier) + '\n'
        ret += "PRA:\n" + "\n".join([str(u) for u in self.pras]) + '\n'
        ret += "CA Rules:\n" + "\n".join([str(u) for u in self.ca_rules]) + '\n'
        ret += "CR Rules:\n" + "\n".join([str(u) for u in self.cr_rules]) + '\n'
        ret += "Invariants:\n" + "\n".join([str(u) for u in self.smers]) + '\n'
        ret += "Queries:\n" + "\n".join([str(u) for u in self.queries]) + '\n'
        return ret


class User:

    def __init__(self, username):
        self.name = username

    def __str__(self):
        return self.name


class Role:

    def __init__(self, rolename):
        self.name = rolename

    def __str__(self):
        return self.name


class Hierarchy:

    def __init__(self):
        self._partial_orders = {}

    def addPartialOrder(self, l, r):
        ''' @parameter
                l: inferior role
                r: superior role
        '''
        if l in self._partial_orders:
            self._partial_orders[l].append(r)
        else:
            self._partial_orders[l] = []
            self._partial_orders[l].append(r)

    def getSuperiorRoles(self, r):
        if r in self._partial_orders:
            return self._partial_orders[r]
        else:
            return []

    def __str__(self):
        ret = ""
        for l in self._partial_orders:
            for r in self._partial_orders[l]:
                ret += l + ' < ' + r + '\n'
        return ret


class Permission:

    def __init__(self, r, action):
        self.role = r
        self.action = action

    def __str__(self):
        return "PA(" + self.role + "[" + ",".join(self.action) + "])"


class CARule:

    def __init__(self, admin, precondition, target):
        self.admin = admin
        self.precondition = precondition
        self.target = target

    def __str__(self):
        return "can_assign(" + self.admin + "," + str(self.precondition) + "," + self.target + ")"


class Precondition:

    def __init__(self, isTrue, conjunct):
        self.isTrue = isTrue
        self.conjunct = conjunct

    def __str__(self):
        if self.isTrue:
            return "true"
        else:
            return " and ".join([str(l) for l in self.conjunct])


class Literal:

    def __init__(self, name, negative):
        self.name = name
        self.negative = negative

    def __str__(self):
        return self.name if not self.negative else 'not ' + self.name


class CRRule:

    def __init__(self, admin, target):
        self.admin = admin
        self.target = target

    def __str__(self):
        return "can_revoke(" + self.admin + ',' + self.target + ')'


class SMER:

    def __init__(self, l, r):
        self.role1 = l
        self.role2 = r

    def __str__(self):
        return "SMER(" + self.role1 + ',' + self.role2 + ')'


class Query:

    def __init__(self, ua, index, goal):
        self.ua_configs = ua
        self.user_index = index
        self.goal = goal

    def __str__(self):
        ret = "reach"
        for ua in self.ua_configs:
            ret += "[" + " ".join(ua) + "]"

        return ret + "(" + str(self.user_index) + "," + " ".join(self.goal) + ")"

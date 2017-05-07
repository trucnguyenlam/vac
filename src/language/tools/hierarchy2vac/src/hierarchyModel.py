

class Policy:

    def __init__(self):
        self.users = []
        self.roles = []
        self.hier = {}
        self.pras = []
        self.ca_rules = []
        self.cr_rules = []
        self.smers = []
        self.queries = []

    def __str__(self):
        pass


class User:

    def __init__(self, username):
        self.name = username

    def __str__(self):
        return self.name


class Role:

    def __init__(self, rolename):
        self.name = rolename


class Hierarchy:

    def __init__(self):
        self._partial_orders = {}

    def addPartialOrder(self, l, r):
        if l in self._partial_orders:
            self._partial_orders[l].append(r)
        else:
            self._partial_orders[l] = []
            self._partial_orders.append(r)

    def getSuperiorRoles(self, r):
        if r in self._partial_orders:
            return self._partial_orders[r]
        else:
            return []


class Permission:

    def __init__(self, r, action):
        self.role = r
        self.action = action


class CARule:

    def __init__(self, admin, precondition, target):
        self.admin = admin
        self.precondition = precondition
        self.target = target


class CRRule:

    def __init__(self, admin, target):
        self.admin = admin
        self.target = target


class SMER:

    def __init__(self, l, r):
        self.role1 = l
        self.role2 = r


class Query:

    def __init__(self, ua, index, goal):
        self.ua_configs = ua
        self.user_index = index
        self.goal = goal

from z3 import *

def _extract(literaleq):
    children = literaleq.children()
    assert(len(children) == 2)
    if str(children[0]) in ['True', 'False']:
        v = children[1]
        val = children[0]
    elif str(children[1]) in ['True', 'False']:
        v = children[0]
        val = children[1]
    else:
        v = "NOT_AVAILABLE" # impact innards
        val = "NOT_AVAILABLE"
        #assert(False)
    return v, val

class tCube:
    def __init__(self, t=0):
        self.t = t
        self.cubeLiterals = list()

    def __lt__(self, other):
        return self.t < other.t

    def clone(self):
        ret = tCube(self.t)
        ret.cubeLiterals = self.cubeLiterals.copy()
        return ret
    
    def clone_and_sort(self):
        ret = tCube(self.t)
        ret.cubeLiterals = self.cubeLiterals.copy()
        ret.cubeLiterals.sort(key=lambda x: str(_extract(x)[0]))
        return ret

    def remove_true(self):
        self.cubeLiterals = [c for c in self.cubeLiterals if c is not True]
    
    def __eq__(self, other):
        return collections.Counter(self.cubeLiterals) == collections.Counter(other.cubeLiterals)

    def addModel(self, lMap, model, remove_input):
        no_var_primes = [l for l in model if str(l)[0] == 'i' or not str(l).endswith('_prime')]
        if remove_input:
            no_input = [l for l in no_var_primes if str(l)[0] != 'i']
        else:
            no_input = no_var_primes
        for l in no_input:
            self.add(lMap[str(l)] == model[l])

    def remove_input(self):
        index_to_remove = set()
        for idx, literal in enumerate(self.cubeLiterals):
            children = literal.children()
            assert(len(children) == 2)

            if str(children[0]) in ['True', 'False']:
                v = str(children[1])
            elif str(children[1]) in ['True', 'False']:
                v = str(children[0])
            else:
                assert(False)
            assert (v[0] in ['i', 'v'])
            if v[0] == 'i':
                index_to_remove.add(idx)
        self.cubeLiterals = [self.cubeLiterals[i] for i in range(len(self.cubeLiterals)) if i not in index_to_remove]

    def addAnds(self, ms):
        for i in ms:
            self.add(i)

    def add(self, m):
        self.cubeLiterals.append(m)

    def true_size(self):
        return len(self.cubeLiterals) - self.cubeLiterals.count(True)

    def join(self, model):
        literal_idx_to_remove = set()
        model = {str(var): model[var] for var in model}
        for idx, literal in enumerate(self.cubeLiterals):
            if literal is True:
                continue
            var, val = _extract(literal)
            # return when var, val both are NOT_AVAILABLE
            if (str(var) == "NOT_AVAILABLE") and (str(val) == "NOT_AVAILABLE"):
                return "NOT_AVAILABLE"
            var = str(var)
            assert(var[0] == 'v')
            if var not in model:
                literal_idx_to_remove.add(idx)
                continue
            val2 = model[var]
            if str(val2) == str(val):
                continue
            literal_idx_to_remove.add(idx)
        for idx in literal_idx_to_remove:
            self.cubeLiterals[idx] = True
        return len(literal_idx_to_remove) != 0

    def delete(self, i: int):
        res = tCube(self.t)
        for it, v in enumerate(self.cubeLiterals):
            if i == it:
                res.add(True)
                continue
            res.add(v)
        return res

    def cube(self):
        return simplify(And(self.cubeLiterals))

    def cube_remove_equal(self):
        res = tCube(self.t)
        for literal in self.cubeLiterals:
            children = literal.children()
            assert(len(children) == 2)
            cube_literal = And(Not(And(children[0],Not(children[1]))), Not(And(children[1],Not(children[0]))))
            res.add(cube_literal)
        return res

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))
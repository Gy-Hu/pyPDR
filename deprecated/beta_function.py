'''
---- ctgDown prototype ----
'''

def mic(self, q: tCube, i: int, d: int = 1):
    for idx in range(len(q.cubeLiterals)):
        if q.cubeLiterals[idx] is True:
            continue
        q_copy = q.delete(idx)
        if self.ctgDown(q_copy, i, d):
            q = q_copy
    return q

def ctgDown(self, q: tCube, i: int, d: int) -> bool:
    ctgs = 0
    while True:
        self.solver.push()
        self.solver.add(self.init.cube())
        self.solver.add(q.cube())
        if sat == self.solver.check():
            self.solver.pop()
            return False
        self.solver.pop()

        self.solver.push()
        self.solver.add(And(self.frames[i - 1].cube(), Not(q.cube()), self.trans.cube(), 
                            substitute(substitute(q.cube(), self.primeMap), self.inp_map)))
        if unsat == self.solver.check():
            self.solver.pop()
            return True
        m = self.solver.model()
        s = tCube(i-1)
        s.addModel(self.lMap, m, remove_input=False)
        
        if d > self.maxDepth:
            self.solver.pop()
            return False
        
        self.solver.push()
        self.solver.add(self.init.cube())
        self.solver.add(s.cube())
        res_check_init = self.solver.check()
        self.solver.pop()
        
        self.solver.push()
        self.solver.add(And(self.frames[i - 1].cube(), Not(s.cube()), self.trans.cube(), 
                            substitute(substitute(Not(s.cube()), self.primeMap), self.inp_map)))
        res_check_relative = self.solver.check()
        self.solver.pop()
        if ctgs < self.maxCTGs and i > 0 and (res_check_init == unsat) and (res_check_relative == unsat):
            ctgs += 1
            for j in range(i, len(self.frames)):
                self.solver.push()
                #if self.frames[j].cube() & Not(s.cube()) & self.trans.cube() !=> substitute(substitute(Not(s.cube()), self.primeMap), self.inp_map):
                if self.solver.check(And(self.frames[j].cube(), Not(s.cube()), self.trans.cube(), substitute(substitute(s.cube(), self.primeMap), self.inp_map))) == unsat:
                    self.solver.pop()
                    break
            s = self.mic(s, j-1, d+1)
            self.frames[j].add(Not(s.cube()), pushed=False)
        else:
            ctgs = 0
            has_removed = q.join(m)
            assert(has_removed)
            
        self.solver.pop()
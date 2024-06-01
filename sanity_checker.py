from z3 import *
from queue import PriorityQueue
from cube_manager import tCube

class SanityChecker:
    def __init__(self, pdr):
        self.pdr = pdr

    def _debug_print_frame(self, fidx, skip_pushed=False):
        if not self.pdr.debug:
            return
        for idx, c in enumerate(self.pdr.frames[fidx].Lemma):
            if skip_pushed and self.pdr.frames[fidx].pushed[idx]:
                continue
            if 'i' in str(c):
                print('C', idx, ':', 'property')
            else:
                print('C', idx, ':', str(c))

    def _debug_c_is_predecessor(self, c, t, f, not_cp):
        if not self.pdr.debug:
            return
        s = Solver()
        s.add(c)
        s.add(t)
        if f is not True:
            s.add(f)
        s.add(not_cp)
        assert (s.check() == unsat)
        
    def _debug_cex_is_not_none(self, tCube):
        if not self.pdr.debug:
            return
        tCube.remove_true() # e.g. [True, v14==False, v12==True]
        assert len(tCube.cubeLiterals) != 0 # e.g. assert [] is not happening after remove_true()
        # cube is never true -> simplify(And(tCube.cubeLiterals)) is never true
        # is_true(cube) -> false
        # nevert assert false -> is_true(cube) is never equal to True
        assert (is_true(Not(simplify(And(tCube.cubeLiterals)))) == False) and (is_false(Not(simplify(And(tCube.cubeLiterals)))) == False)
        
    def _check_MIC(self, st:tCube):
        if not self.pdr.debug:
            return
        cubePrime = substitute(substitute(st.cube(), self.pdr.primeMap),self.pdr.inp_map)
        s = Solver()
        s.add(Not(st.cube()))
        s.add(self.pdr.frames[st.t - 1].cube())
        s.add(self.pdr.trans.cube())
        s.add(cubePrime)
        assert (s.check() == unsat)
    
    def _debug_trace(self, trace: PriorityQueue):
        if not self.pdr.debug:
            return
        prev_fidx = 0
        self.pdr.bmc.setup()
        while not trace.empty():
            idx, cube = trace.get()
            assert (idx == prev_fidx+1)
            self.pdr.bmc.unroll()
            self.pdr.bmc.add(cube.cube())
            reachable = self.pdr.bmc.check()
            if reachable:
                print (f'F {prev_fidx} ---> {idx}')
            else:
                print(f'F {prev_fidx} -/-> {idx}')
                assert(False)
            prev_fidx += 1
        self.pdr.bmc.unroll()
        self.pdr.bmc.add(Not(self.pdr.post.cube()))
        assert(self.pdr.bmc.check() == sat)
        
    def _sanity_check_inv(self, inv):
        if not self.pdr.debug:
            return
        '''
        check the correctness of the inductive invariant
        - init -> inv
        - inv -> P
        - inv & T -> inv’
        '''
        
        # init -> inv
        s = Solver()
        s.add(self.pdr.init.cube())
        s.add(Not(inv))
        assert(s.check() == unsat)
        
        # inv -> P
        prop = self.pdr.post.cube()
        s = Solver()
        s.add(inv)
        s.add(Not(prop))
        assert(s.check() == unsat)
        
        # inv & T -> inv’
        s = Solver()
        s.add(inv)
        s.add(self.pdr.trans.cube())
        s.add(Not(substitute(substitute(inv, self.pdr.primeMap),self.pdr.inp_map)))
        assert(s.check() == unsat)
        

    def _sanity_check_frame(self):
        if not self.pdr.debug:
            return
        for idx in range(0,len(self.pdr.frames)-1):
            Fi = self.pdr.frames[idx].cube()
            Fiadd1 = self.pdr.frames[idx+1].cube()
            s1 = Solver()
            s1.add(Fi)
            s1.add(Not(Fiadd1))
            assert( s1.check() == unsat)
            s2 = Solver()
            s2.add(Fi)
            s2.add(self.pdr.trans.cube())
            s2.add(substitute(substitute(Not(Fiadd1), self.pdr.primeMap),self.pdr.inp_map))
            assert( s2.check() == unsat)
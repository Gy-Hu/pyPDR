from math import fabs
from z3 import *
import sys
import csv
import numpy as np
from queue import PriorityQueue
from functools import wraps
from itertools import combinations
import random
import collections
import ternary_sim

class Frame:
    def __init__(self, lemmas):
        self.Lemma = lemmas
        self.pushed = [False] * len(lemmas)

    def cube(self):
        return And(self.Lemma)

    def add(self, clause, pushed=False):
        self.Lemma.append(clause)
        self.pushed.append(pushed)

    def __repr__(self):
        return str(sorted(self.Lemma, key=str))

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
        assert(False)
    return v, val

class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post, pv2next, primes_inp, filename, debug=False):
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.items = self.primary_inputs + self.literals + primes_inp + primes
        self.lMap = {str(l): l for l in self.items}
        self.post = post
        self.frames = list()
        self.primeMap = [(literals[i], primes[i]) for i in range(len(literals))]
        self.inp_map = [(primary_inputs[i], primes_inp[i]) for i in range(len(primes_inp))]
        self.pv2next = pv2next
        self.initprime = substitute(self.init.cube(), self.primeMap)
        self.ternary_simulator = ternary_sim.AIGBuffer()
        for _, updatefun in self.pv2next.items():
            self.ternary_simulator.register_expr(updatefun)
        self.filename = filename

    def check_init(self):
        s = Solver()
        s.add(self.init.cube())
        s.add(Not(self.post.cube()))
        res1 = s.check()
        if res1 == sat:
            return False
        s = Solver()
        s.add(self.init.cube())
        s.add(self.trans.cube())
        s.add(substitute(substitute(Not(self.post.cube()), self.primeMap),self.inp_map))
        res2 = s.check()
        if res2 == sat:
            return False
        return True

    def run(self):
        if not self.check_init():
            print("Found trace ending in bad state")
            return False

        self.frames = list()
        self.frames.append(Frame(lemmas=[self.init.cube()]))
        self.frames.append(Frame(lemmas=[self.post.cube()]))

        while True:
            c = self.getBadCube()
            if c is not None:
                trace = self.recBlockCube(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    self._debug_trace(trace)
                    while not trace.empty():
                        idx, cube = trace.get()
                        print(cube)
                    return False
                print("recBlockCube Ok! F:")

            else:
                inv = self.checkForInduction()
                if inv != None:
                    print("Found inductive invariant")
                    self._debug_print_frame(len(self.frames)-1)
                    print ('Total F', len(self.frames), ' F[-1]:', len(self.frames[-1].Lemma))
                    return True
                print("Did not find invariant, adding frame " + str(len(self.frames)) + "...")

                print("Adding frame " + str(len(self.frames)) + "...")
                self.frames.append(Frame(lemmas=[]))

                for idx in range(1,len(self.frames)-1):
                    self.pushLemma(idx)

                print("Now print out the size of frames")
                for index in range(len(self.frames)):
                    push_cnt = self.frames[index].pushed.count(True)
                    print("F", index, 'size:', len(self.frames[index].Lemma), 'pushed: ', push_cnt)
                    assert (len(self.frames[index].Lemma) == len(self.frames[index].pushed))

    def checkForInduction(self):
        Fi2 = self.frames[-2].cube()
        Fi = self.frames[-1].cube()
        s = Solver()
        s.add(Fi)
        s.add(Not(Fi2))
        if s.check() == unsat:
            return Fi
        return None

    def pushLemma(self, Fidx:int):
        fi: Frame = self.frames[Fidx]

        for lidx, c in enumerate(fi.Lemma):
            if fi.pushed[lidx]:
                continue
            s = Solver()
            s.add(fi.cube())
            s.add(self.trans.cube())
            s.add(substitute(Not(substitute(c, self.primeMap)),self.inp_map))

            if s.check()==unsat:
                fi.pushed[lidx] = True
                self.frames[Fidx + 1].add(c)
    
    def frame_trivially_block(self, st: tCube):
        Fidx = st.t
        slv = Solver()
        slv.add(self.frames[Fidx].cube())
        slv.add(st.cube())
        if slv.check() == unsat:
            return True
        return False

    def recBlockCube(self, s0: tCube):
        Q = PriorityQueue()
        print("recBlockCube now...")
        Q.put((s0.t, s0))
        prevFidx = None
        while not Q.empty():
            print (Q.qsize())
            s:tCube = Q.get()[1]
            if s.t == 0:
                return Q

            assert(prevFidx != 0)
            if prevFidx is not None and prevFidx == s.t-1:
                self.pushLemma(prevFidx)
            prevFidx = s.t
            if self.frame_trivially_block(s):
                continue

            z = self.solveRelative(s)
            if z is None:
                sz = s.true_size()
                original_s_1 = s.clone()
                q4unsatcore = s.clone()
                self.unsatcore_reduce(q4unsatcore, trans=self.trans.cube(), frame=self.frames[q4unsatcore.t-1].cube())
                q4unsatcore.remove_true()
                s = self.MIC(s)
                self._check_MIC(s)
                print ('MIC ', sz, ' --> ', s.true_size(),  'F', s.t)
                self.frames[s.t].add(Not(s.cube()), pushed=False)
                for i in range(1, s.t):
                    self.frames[i].add(Not(s.cube()), pushed=True)

            else:
                assert(z.t == s.t-1)
                Q.put((s.t, s))
                Q.put((s.t-1, z))
        return None

    def down(self, q: tCube):
        while True:
            print(q.true_size(), end=',')
            s = Solver()
            s.push()
            s.add(self.frames[0].cube())
            s.add(q.cube())
            if sat == s.check():
                print('F')
                return False
            s.pop()
            s.push()
            s.add(And(self.frames[q.t-1].cube(), Not(q.cube()), self.trans.cube(),
                      substitute(substitute(q.cube(), self.primeMap),self.inp_map)))
            if unsat == s.check():
                print('T')
                return True
            m = s.model()
            has_removed = q.join(m)
            s.pop()
            assert (has_removed)

    def MIC(self, q: tCube):
        sz = q.true_size()
        self.unsatcore_reduce(q, trans=self.trans.cube(), frame=self.frames[q.t-1].cube())
        print('unsatcore', sz, ' --> ', q.true_size())
        q.remove_true()

        for i in range(len(q.cubeLiterals)):
            if q.cubeLiterals[i] is True:
                continue
            q1 = q.delete(i)
            print(f'MIC try idx:{i}')
            if self.down(q1): 
                q = q1
        q.remove_true()
        print (q)
        return q

    def unsatcore_reduce(self, q:  tCube, trans, frame):
        slv = Solver()
        slv.set(unsat_core=True)

        l = Or( And(Not(q.cube()), trans, frame), self.initprime)
        slv.add(l)

        plist = []
        for idx, literal in enumerate(q.cubeLiterals):
            p = 'p'+str(idx)
            slv.assert_and_track(substitute(substitute(literal, self.primeMap),self.inp_map), p)
            plist.append(p)
        res = slv.check()
        if res == sat:
            model = slv.model()
            print(model.eval(self.initprime))
            assert False
        assert (res == unsat)
        core = slv.unsat_core()
        for idx, p in enumerate(plist):
            if Bool(p) not in core:
                q.cubeLiterals[idx] = True
        return q

    def solveRelative(self, tcube) -> tCube:
        cubePrime = substitute(substitute(tcube.cube(), self.primeMap),self.inp_map)
        s = Solver()
        s.add(Not(tcube.cube()))
        s.add(self.frames[tcube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(cubePrime)

        if s.check()==sat:
            model = s.model()
            c = tCube(tcube.t - 1)
            c.addModel(self.lMap, model, remove_input=False)
            generalized_p = self.generalize_predecessor(c, next_cube_expr = tcube.cube(), prevF=self.frames[tcube.t-1].cube())
            generalized_p.remove_input()
            return generalized_p
        else:
            return None

    def generalize_predecessor(self, prev_cube:tCube, next_cube_expr, prevF):
        tcube_cp = prev_cube.clone()
        print("original size of !P (or CTI): ", len(tcube_cp.cubeLiterals))

        nextcube = substitute(substitute(substitute(next_cube_expr, self.primeMap),self.inp_map), list(self.pv2next.items()))
        index_to_remove = []

        s = Solver()
        for index, literals in enumerate(tcube_cp.cubeLiterals):
            s.assert_and_track(literals,'p'+str(index))
        s.add(Not(nextcube))
        assert(s.check() == unsat)
        core = s.unsat_core()
        core = [str(core[i]) for i in range(0, len(core), 1)]

        for idx in range(len(tcube_cp.cubeLiterals)):
            var, val = _extract(prev_cube.cubeLiterals[idx])
            if 'p'+str(idx) not in core:
                tcube_cp.cubeLiterals[idx] = True

        tcube_cp.remove_true()
        size_after_unsat_core = len(tcube_cp.cubeLiterals)

        simulator = self.ternary_simulator.clone()
        simulator.register_expr(nextcube)
        simulator.set_initial_var_assignment(dict([_extract(c) for c in tcube_cp.cubeLiterals]))

        out = simulator.get_val(nextcube)
        if out == ternary_sim._X:
            return tcube_cp
        assert out == ternary_sim._TRUE
        for i in range(len(tcube_cp.cubeLiterals)):
            v, val = _extract(tcube_cp.cubeLiterals[i])
            simulator.set_Li(v, ternary_sim._X)
            out = simulator.get_val(nextcube)
            if out == ternary_sim._X:
                simulator.set_Li(v, ternary_sim.encode(val))
                assert simulator.get_val(nextcube) == ternary_sim._TRUE
            else:
                assert simulator.get_val(nextcube) == ternary_sim._TRUE
                tcube_cp.cubeLiterals[i] = True
        tcube_cp.remove_true()
        size_after_ternary_sim = len(tcube_cp.cubeLiterals)
        return tcube_cp

    def getBadCube(self):
        print("seek for bad cube...")

        s = Solver()
        s.add(substitute(substitute(Not(self.post.cube()), self.primeMap),self.inp_map))
        s.add(self.frames[-1].cube())
        s.add(self.trans.cube())

        if s.check() == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, s.model(), remove_input=False)
            print("get bad cube size:", len(res.cubeLiterals), end=' --> ')
            self._debug_c_is_predecessor(res.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map)) 
            new_model = self.generalize_predecessor(res, Not(self.post.cube()), self.frames[-1].cube())
            print(len(new_model.cubeLiterals))
            self._debug_c_is_predecessor(new_model.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map))
            new_model.remove_input()
            return new_model
        else:
            return None

    def _debug_print_frame(self, fidx, skip_pushed=False):
        if not self.debug:
            return
        for idx, c in enumerate(self.frames[fidx].Lemma):
            if skip_pushed and self.frames[fidx].pushed[idx]:
                continue
            if 'i' in str(c):
                print('C', idx, ':', 'property')
            else:
                print('C', idx, ':', str(c))

    def _debug_c_is_predecessor(self, c, t, f, not_cp):
        if not self.debug:
            return
        s = Solver()
        s.add(c)
        s.add(t)
        if f is not True:
            s.add(f)
        s.add(not_cp)
        assert (s.check() == unsat)
        
    def _check_MIC(self, st:tCube):
        if not self.debug:
            return
        cubePrime = substitute(substitute(st.cube(), self.primeMap),self.inp_map)
        s = Solver()
        s.add(Not(st.cube()))
        s.add(self.frames[st.t - 1].cube())
        s.add(self.trans.cube())
        s.add(cubePrime)
        assert (s.check() == unsat)
    
    def _debug_trace(self, trace: PriorityQueue):
        if not self.debug:
            return
        prev_fidx = 0
        self.bmc.setup()
        while not trace.empty():
            idx, cube = trace.get()
            assert (idx == prev_fidx+1)
            self.bmc.unroll()
            self.bmc.add(cube.cube())
            reachable = self.bmc.check()
            if reachable:
                print (f'F {prev_fidx} ---> {idx}')
            else:
                print(f'F {prev_fidx} -/-> {idx}')
                assert(False)
            prev_fidx += 1
        self.bmc.unroll()
        self.bmc.add(Not(self.post.cube()))
        assert(self.bmc.check() == sat)
        
    def _sanity_check_inv(self, inv):
        pass

    def _sanity_check_frame(self):
        if not self.debug:
            return
        for idx in range(0,len(self.frames)-1):
            # check Fi => Fi+1
            # Fi/\T => Fi+1
            Fi = self.frames[idx].cube()
            Fiadd1 = self.frames[idx+1].cube()
            s1 = Solver()
            s1.add(Fi)
            s1.add(Not(Fiadd1))
            assert( s1.check() == unsat)
            s2 = Solver()
            s2.add(Fi)
            s2.add(self.trans.cube())
            s2.add(substitute(substitute(Not(Fiadd1), self.primeMap),self.inp_map))
            assert( s2.check() == unsat)
    
if __name__ == '__main__':
    pass
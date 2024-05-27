from z3 import *
from queue import PriorityQueue
import ternary_sim
from cube_manager import tCube, _extract
from frame_manager import Frame
from sanity_checker import SanityChecker
from monitor_panel import MonitorPannel
from rich.console import Console
from rich.panel import Panel
from rich.live import Live
import logging
import time
from rich.panel import Panel

logging.basicConfig(filename='pdr.log', level=logging.INFO, format='%(message)s')

class HeuristicLitOrder:
    def __init__(self):
        self.counts = {}
        self._mini = float('inf')

    def count(self, cube):
        assert len(cube) > 0
        #self._mini = min(self._mini, cube[0].children()[0])
        for literal in cube:
            self.counts[str(literal.children()[0])] = self.counts.get(str(literal.children()[0]), 0) + 1

    def decay(self):
        # for variable in 0 to max index of the keys in counts
        for var in self.counts.keys():
            self.counts[var] = self.counts.get(var, 0) * 0.99

class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post, pv2next, primes_inp, filename, debug=False):
        self.console = Console()
        self.enable_assert = True
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.items = self.primary_inputs + self.literals + primes_inp + primes
        self.lMap = {str(l): l for l in self.items}
        self.post = post
        self.frames = list()
        self.debug = debug
        self.sanity_checker = SanityChecker(self)
        self.monitor_panel = MonitorPannel(self)
        self.primeMap = [(literals[i], primes[i]) for i in range(len(literals))]
        self.inp_map = [(primary_inputs[i], primes_inp[i]) for i in range(len(primes_inp))]
        self.pv2next = pv2next
        self.initprime = substitute(self.init.cube(), self.primeMap)
        self.ternary_simulator = ternary_sim.AIGBuffer()
        for _, updatefun in self.pv2next.items():
            self.ternary_simulator.register_expr(updatefun)
        self.filename = filename
        self.solver = Solver()
        self.solver4generalization = Solver()
        self.maxDepth = 1
        self.maxCTGs = 3
        # set this as infinity
        self.micAttempts = float('inf')
        self.litOrderManager = HeuristicLitOrder()
        self.status = "Running..."
        
        # measurement variables
        self.avg_propagation_times = []
        self.predecessor_generalization_reduction_percentages = []
        self.mic_reduction_percentages = []
        self.sum_of_propagate_time = 0.0
        self.sum_of_predecessor_generalization_time = 0.0
        self.sum_of_mic_time = 0.0
        self.total_push_attempts = 0
        self.successful_pushes = 0
        self.overall_runtime = 0
        self.sum_of_cti_producing_time = 0
        self.sum_of_solve_relative_time = 0
        self.sum_of_check_induction_time = 0
        self.sum_of_frame_trivially_block_time = 0
        self.sum_of_unsatcore_reduce_time = 0
        self.cti_queue_sizes = []
        self.sum_of_sat_call = 0

    def check_init(self):
        self.solver.push()
        self.solver.add(self.init.cube())
        self.solver.add(Not(self.post.cube()))
        res1 = self.solver.check() ; self.sum_of_sat_call += 1
        self.solver.pop()

        if res1 == sat:
            return False

        self.solver.push()
        self.solver.add(self.init.cube())
        self.solver.add(self.trans.cube())
        self.solver.add(substitute(substitute(Not(self.post.cube()), self.primeMap), self.inp_map))
        res2 = self.solver.check() ; self.sum_of_sat_call += 1
        self.solver.pop()

        if res2 == sat:
            return False

        return True

    def run(self):
        
        if not self.check_init():
            self.status = "Found trace ending in bad state"
            return False

        self.frames = list()
        self.frames.append(Frame(lemmas=[self.init.cube()]))
        self.frames.append(Frame(lemmas=[self.post.cube()]))
        
        try:
            with Live(self.monitor_panel.get_table(), console=self.console, screen=True, refresh_per_second=2) as live:
                
                while True:
                    live.update(self.monitor_panel.get_table())
                    start_time = time.time()
                    c = self.strengthen()
                    if c is not None:
                        assert len(self.solver.assertions()) == 0, "Solver is not empty after strengthen"
                        trace = self.handleObligations(c)
                        if trace is not None:
                            self.status = "FOUND TRACE"
                            self.sanity_checker._debug_trace(trace)
                            while not trace.empty():
                                idx, cube = trace.get()
                                self.console.print(cube)
                            
                            return False

                    else:
                        inv = self.checkForInduction()
                        if inv is not None:
                            self.status = "FOUND INV"
                            self.sanity_checker._debug_print_frame(len(self.frames) - 1)
                            self.sanity_checker._sanity_check_inv(inv)
                            break

                        self.frames.append(Frame(lemmas=[]))

                        for idx in range(1, len(self.frames) - 1):
                            self.propagate(idx)
                    end_time = time.time()
                    self.overall_runtime += end_time - start_time
                while True:
                    live.update(self.monitor_panel.get_table())
        except KeyboardInterrupt:
            self.console.print(Panel("Exiting", style="bold yellow"))
    
    def checkForInduction(self):
        start_time = time.time()  # Start timing
        Fi2 = self.frames[-2].cube()
        Fi = self.frames[-1].cube()
        self.solver.push()
        self.solver.add(Fi)
        self.solver.add(Not(Fi2))
        res = self.solver.check() ; self.sum_of_sat_call += 1
        end_time = time.time()  # End timing
        self.solver.pop()
        self.sum_of_check_induction_time += end_time - start_time  # Update sum of check induction time
        if res == unsat:
            return Fi
        return None

    def propagate(self, Fidx: int): # renamed from pushLemma()
        start_time = time.time()
        fi: Frame = self.frames[Fidx]
        for lidx, c in enumerate(fi.Lemma):
            if fi.pushed[lidx]:
                continue
            self.total_push_attempts += 1
            self.solver.push()
            self.solver.add(fi.cube())
            self.solver.add(self.trans.cube())
            self.solver.add(substitute(Not(substitute(c, self.primeMap)), self.inp_map))
            tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
            if tmp_res == unsat:
                fi.pushed[lidx] = True
                self.successful_pushes += 1
                self.frames[Fidx + 1].addLemma(c, pushed=False)
            self.solver.pop()
        end_time = time.time()
        time_taken = end_time - start_time
        self.avg_propagation_times.append(time_taken)
        self.sum_of_propagate_time += time_taken

    def frame_trivially_block(self, st: tCube):
        start_time = time.time()
        Fidx = st.t
        self.solver.push()
        self.solver.add(self.frames[Fidx].cube())
        self.solver.add(st.cube())
        res = self.solver.check() ; self.sum_of_sat_call += 1
        self.solver.pop()
        end_time = time.time()
        self.sum_of_frame_trivially_block_time += end_time - start_time
        if res == unsat:
            return True
        return False

    def handleObligations(self, s0: tCube): # renamed from recBlockCube()
        Q = PriorityQueue()
        logging.info("recBlockCube now...")
        Q.put((s0.t, s0))
        prevFidx = None
        while not Q.empty():
            s: tCube = Q.get()[1]
            if s.t == 0:
                return Q

            assert (prevFidx != 0)
            if prevFidx is not None and prevFidx == s.t - 1:
                self.propagate(prevFidx)
            prevFidx = s.t
            if self.frame_trivially_block(s):
                continue

            z = self.stateOf(s)
            if z is None:
                assert s.cubeLiterals != [], "CTI producing cube is empty"
                sz = s.true_size()
                original_s_1 = s.clone()
                q4unsatcore = s.clone()
                assert len(self.solver.assertions()) == 0, "Solver is not empty before unsatcore_reduce"
                
                self.unsatcore_reduce(q4unsatcore, trans=self.trans.cube(), frame=self.frames[q4unsatcore.t - 1].cube())
                q4unsatcore.remove_true()
                s = self.mic(s, s.t)
                self.sanity_checker._check_MIC(s)
                assert len(s.cubeLiterals) != 0, "MIC produced an empty cube"
                self.sanity_checker._debug_cex_is_not_none(s)
                self.frames[s.t].block_cex(s, pushed=False, litOrderManager=self.litOrderManager)
                for i in range(1, s.t):
                    self.frames[i].block_cex(s, pushed=True, litOrderManager=self.litOrderManager)

            else:
                assert (z.t == s.t - 1)
                Q.put((s.t, s))
                Q.put((s.t - 1, z))
            self.cti_queue_sizes.append(Q.qsize()) 
        return None
    
    def mic(self, q: tCube, i: int, d: int = 1, use_ctg_down=False):
        start_time = time.time()  # Start timing
        initial_size = q.true_size()
        self.unsatcore_reduce(q, trans=self.trans.cube(), frame=self.frames[q.t - 1].cube())
        q.remove_true()

        if use_ctg_down:
            q.cubeLiterals = self.frames[i].heuristic_lit_order(q.cubeLiterals, self.litOrderManager)
            for idx in range(len(q.cubeLiterals)):
                if self.micAttempts == 0:
                    break
                if q.cubeLiterals[idx] is True:
                    continue
                q_copy = q.delete(idx)
                if self.ctgDown(q_copy, i, d):
                    q = q_copy
                self.micAttempts -= 1
        else: # use down()
            q.cubeLiterals = self.frames[i].heuristic_lit_order(q.cubeLiterals, self.litOrderManager)
            for i in range(len(q.cubeLiterals)):
                if q.cubeLiterals[i] is True:
                    continue
                q1 = q.delete(i)
                if self.down(q1):
                    q = q1

        q.remove_true()
        final_size = q.true_size()
        reduction_percentage = ((initial_size - final_size) / initial_size) * 100 if initial_size > 0 else 0
        self.mic_reduction_percentages.append(reduction_percentage)
        
        end_time = time.time()  # End timing
        time_taken = end_time - start_time
        self.sum_of_mic_time += time_taken  # Update sum of MIC time
        return q

    def down(self, q: tCube):
        while True:
            self.solver.push()
            self.solver.add(self.frames[0].cube())
            self.solver.add(q.cube())
            tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
            if tmp_res == sat:
                self.solver.pop()
                return False
            self.solver.pop()

            self.solver.push()
            self.solver.add(And(self.frames[q.t - 1].cube(), Not(q.cube()), self.trans.cube(),
                                substitute(substitute(q.cube(), self.primeMap), self.inp_map)))
            tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
            if tmp_res == unsat:
                self.solver.pop()
                return True
            m = self.solver.model()
            has_removed = q.join(m)
            self.solver.pop()
            assert (has_removed)

    def ctgDown(self, q: tCube, i: int, d: int) -> bool:
        ctgs = 0
        while True:
            self.solver.push()
            self.solver.add(self.init.cube())
            self.solver.add(q.cube())
            tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
            if tmp_res == sat:
                self.solver.pop()
                return False
            self.solver.pop()

            self.solver.push()
            self.solver.add(And(self.frames[i - 1].cube(), Not(q.cube()), self.trans.cube(), 
                                substitute(substitute(q.cube(), self.primeMap), self.inp_map)))
            tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
            if tmp_res == unsat:
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
            res_check_init = self.solver.check() ; self.sum_of_sat_call += 1
            self.solver.pop()
            
            self.solver.push()
            self.solver.add(And(self.frames[i - 1].cube(), Not(s.cube()), self.trans.cube(), 
                                substitute(substitute(Not(s.cube()), self.primeMap), self.inp_map)))
            res_check_relative = self.solver.check() ; self.sum_of_sat_call += 1
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
                #assert len(s.cubeLiterals) != 0
                self.sanity_checker._debug_cex_is_not_none(s)
                self.frames[j].block_cex(s, pushed=False)
            else:
                ctgs = 0
                has_removed = q.join(m)
                assert(has_removed)
                
            self.solver.pop()

    def unsatcore_reduce(self, q: tCube, trans, frame):
        start_time = time.time()  # Start timing

        l = Or(And(Not(q.cube()), trans, frame), self.initprime)
        self.solver.push()
        self.solver.set(unsat_core=True)
        self.solver.add(l)

        plist = []
        for idx, literal in enumerate(q.cubeLiterals):
            p = 'p' + str(idx)
            self.solver.assert_and_track(substitute(substitute(literal, self.primeMap), self.inp_map), p)
            plist.append(p)

        res = self.solver.check() ; self.sum_of_sat_call += 1
        if res == sat:
            model = self.solver.model()
            print("Satisfying model:")
            for var in model:
                print(f"{var} = {model[var]}")
            assert False, "Unsatcore reduction encountered a satisfiable model"

        assert (res == unsat)
        core = self.solver.unsat_core()
        self.solver.pop()

        for idx, p in enumerate(plist):
            if Bool(p) not in core:
                q.cubeLiterals[idx] = True

        end_time = time.time()  # End timing
        self.sum_of_unsatcore_reduce_time += end_time - start_time  # Update sum of unsatcore reduce time
        return q
    
    def stateOf(self, tcube) -> tCube: # renamed from solveRelative()
        start_time = time.time()
        cubePrime = substitute(substitute(tcube.cube(), self.primeMap),self.inp_map)
        self.solver.push()
        self.solver.add(Not(tcube.cube()))
        self.solver.add(self.frames[tcube.t - 1].cube())
        self.solver.add(self.trans.cube())
        self.solver.add(cubePrime)
        
        tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
        if tmp_res == sat:
            model = self.solver.model()
            self.solver.pop()
            c = tCube(tcube.t - 1)
            c.addModel(self.lMap, model, remove_input=False)
            generalized_p = self.generalize(c, next_cube_expr = tcube.cube(), prevF=self.frames[tcube.t-1].cube())
            generalized_p.remove_input()
            end_time = time.time()
            self.sum_of_solve_relative_time += end_time - start_time
            return generalized_p
        else:
            self.solver.pop()
            end_time = time.time()
            self.sum_of_solve_relative_time += end_time - start_time
            return None

    def generalize(self, prev_cube:tCube, next_cube_expr, prevF, use_ternary_sim=False): # renamed from generalize_predecessor()
        start_time = time.time()  # Start timing
        tcube_cp = prev_cube.clone()

        nextcube = substitute(substitute(substitute(next_cube_expr, self.primeMap),self.inp_map), list(self.pv2next.items()))
        
        self.solver.push()

        self.solver.set(unsat_core=True)
        for index, literals in enumerate(tcube_cp.cubeLiterals):
            self.solver.assert_and_track(literals,'p'+str(index))
        self.solver.add(Not(nextcube))
        tmp_res = self.solver.check() ; self.sum_of_sat_call += 1
        assert(tmp_res== unsat)
        core = self.solver.unsat_core()
        core = [str(core[i]) for i in range(0, len(core), 1)]

        for idx in range(len(tcube_cp.cubeLiterals)):
            var, val = _extract(prev_cube.cubeLiterals[idx])
            if 'p'+str(idx) not in core:
                tcube_cp.cubeLiterals[idx] = True

        initial_size = len(tcube_cp.cubeLiterals)
        tcube_cp.remove_true()
        final_size = len(tcube_cp.cubeLiterals)
        reduction_percentage = ((initial_size - final_size) / initial_size) * 100 if initial_size > 0 else 0
        self.predecessor_generalization_reduction_percentages.append(reduction_percentage)  # Track reduction percentage
        
        # Restore the state of self.solver
        self.solver.pop()

        if use_ternary_sim:
            # On-demand loading of the logic cone
            simulator = self.ternary_simulator.clone()
            simulator.register_expr(nextcube)
            simulator.set_initial_var_assignment(dict([_extract(c) for c in tcube_cp.cubeLiterals]))

            # Heuristic-based variable ordering
            variable_order = self.get_variable_order(tcube_cp.cubeLiterals)
            
            # order using self.litOrderManager
            #variable_order = self.frames[tcube_cp.t].heuristic_lit_order(tcube_cp.cubeLiterals, self.litOrderManager)

            # Early termination condition
            max_iterations = len(tcube_cp.cubeLiterals) // 2  # Terminate after processing half of the variables

            for i, idx in enumerate(variable_order):
                if i >= max_iterations:
                    break

                v, val = _extract(tcube_cp.cubeLiterals[idx])
                simulator.set_Li(v, ternary_sim._X)
                out = simulator.get_val(nextcube)
                if out == ternary_sim._X:
                    simulator.set_Li(v, ternary_sim.encode(val))
                    assert simulator.get_val(nextcube) == ternary_sim._TRUE
                else:
                    assert simulator.get_val(nextcube) == ternary_sim._TRUE
                    tcube_cp.cubeLiterals[idx] = True

            tcube_cp.remove_true()

        end_time = time.time()  # End timing
        time_taken = end_time - start_time
        self.sum_of_predecessor_generalization_time += time_taken  # Update sum of generalization time
        return tcube_cp

    def get_variable_order(self, cubeLiterals):
        # Implement heuristic-based variable ordering logic here
        # Return the indices of the variables in the desired order
        
        return list(range(len(cubeLiterals)))
        
        # return the indices of the variables in the order of the heuristic_lit_order
        # ranking_indices = []
        # for i in range(len(cubeLiterals)):
        #     rank = self.litOrderManager.counts.get(str(cubeLiterals[i].children()[0]), 0)
        #     ranking_indices.append(int(rank)) 
        # return ranking_indices

    def strengthen(self): # renamed from getBadcube()
        start_time = time.time()
        logging.info("seek for bad cube...")
        self.solver.push()
        self.solver.add(substitute(substitute(Not(self.post.cube()), self.primeMap),self.inp_map))
        self.solver.add(self.frames[-1].cube())
        self.solver.add(self.trans.cube())
        
        res = self.solver.check() ; self.sum_of_sat_call += 1
        end_time = time.time()
        self.sum_of_cti_producing_time += end_time - start_time
        
        if res == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, self.solver.model(), remove_input=False)
            self.solver.pop()
            self.sanity_checker._debug_c_is_predecessor(res.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map))
            new_model = self.generalize(res, Not(self.post.cube()), self.frames[-1].cube())
            self.sanity_checker._debug_c_is_predecessor(new_model.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map))
            new_model.remove_input()
            return new_model
        else:
            self.solver.pop()
            return None
    
if __name__ == '__main__':
    pass
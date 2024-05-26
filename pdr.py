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

class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post, pv2next, primes_inp, filename, debug=False):
        self.console = Console()
       
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
        s.add(substitute(substitute(Not(self.post.cube()), self.primeMap), self.inp_map))
        res2 = s.check()
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
                    c = self.getBadCube()
                    if c is not None:
                        trace = self.recBlockCube(c)
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
                            break

                        self.frames.append(Frame(lemmas=[]))

                        for idx in range(1, len(self.frames) - 1):
                            self.pushLemma(idx)
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
        s = Solver()
        s.add(Fi)
        s.add(Not(Fi2))
        res = s.check()
        end_time = time.time()  # End timing
        self.sum_of_check_induction_time += end_time - start_time  # Update sum of check induction time
        if res == unsat:
            return Fi
        return None

    def pushLemma(self, Fidx: int):
        start_time = time.time()  # Start timing
        fi: Frame = self.frames[Fidx]
        for lidx, c in enumerate(fi.Lemma):
            self.total_push_attempts += 1  # Increment total push attempts
            if fi.pushed[lidx]:  # Check if already pushed
                continue
            s = Solver()
            s.add(fi.cube())
            s.add(self.trans.cube())
            s.add(substitute(Not(substitute(c, self.primeMap)), self.inp_map))
            if s.check() == unsat:
                fi.pushed[lidx] = True
                self.successful_pushes += 1  # Increment successful pushes
                self.frames[Fidx + 1].add(c)
        end_time = time.time()  # End timing
        time_taken = end_time - start_time
        self.avg_propagation_times.append(time_taken)  # Record the propagation time
        self.sum_of_propagate_time += time_taken  # Update sum of propagate time

    def frame_trivially_block(self, st: tCube):
        start_time = time.time()  # Start timing
        Fidx = st.t
        slv = Solver()
        slv.add(self.frames[Fidx].cube())
        slv.add(st.cube())
        res = slv.check()
        end_time = time.time()  # End timing
        self.sum_of_frame_trivially_block_time += end_time - start_time  # Update sum of frame trivially block time
        if res == unsat:
            return True
        return False

    def recBlockCube(self, s0: tCube):
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
                self.pushLemma(prevFidx)
            prevFidx = s.t
            if self.frame_trivially_block(s):
                continue

            z = self.solveRelative(s)
            if z is None:
                sz = s.true_size()
                original_s_1 = s.clone()
                q4unsatcore = s.clone()
                self.unsatcore_reduce(q4unsatcore, trans=self.trans.cube(), frame=self.frames[q4unsatcore.t - 1].cube())
                q4unsatcore.remove_true()
                s = self.MIC(s)
                self.sanity_checker._check_MIC(s)
                self.frames[s.t].add(Not(s.cube()), pushed=False)
                for i in range(1, s.t):
                    self.frames[i].add(Not(s.cube()), pushed=True)

            else:
                assert (z.t == s.t - 1)
                Q.put((s.t, s))
                Q.put((s.t - 1, z))
            self.cti_queue_sizes.append(Q.qsize()) 
        return None

    def down(self, q: tCube):
        while True:
            s = Solver()
            s.push()
            s.add(self.frames[0].cube())
            s.add(q.cube())
            if sat == s.check():
                return False
            s.pop()
            s.push()
            s.add(And(self.frames[q.t - 1].cube(), Not(q.cube()), self.trans.cube(),
                      substitute(substitute(q.cube(), self.primeMap), self.inp_map)))
            if unsat == s.check():
                return True
            m = s.model()
            has_removed = q.join(m)
            s.pop()
            assert (has_removed)

    def MIC(self, q: tCube):
        start_time = time.time()  # Start timing
        initial_size = q.true_size()
        self.unsatcore_reduce(q, trans=self.trans.cube(), frame=self.frames[q.t - 1].cube())
        q.remove_true()

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

    def unsatcore_reduce(self, q: tCube, trans, frame):
        start_time = time.time()  # Start timing
        slv = Solver()
        slv.set(unsat_core=True)

        l = Or(And(Not(q.cube()), trans, frame), self.initprime)
        slv.add(l)

        plist = []
        for idx, literal in enumerate(q.cubeLiterals):
            p = 'p' + str(idx)
            slv.assert_and_track(substitute(substitute(literal, self.primeMap), self.inp_map), p)
            plist.append(p)
        res = slv.check()
        if res == sat:
            model = slv.model()
            assert False
        assert (res == unsat)
        core = slv.unsat_core()
        for idx, p in enumerate(plist):
            if Bool(p) not in core:
                q.cubeLiterals[idx] = True
        end_time = time.time()  # End timing
        self.sum_of_unsatcore_reduce_time += end_time - start_time  # Update sum of unsatcore reduce time
        return q
    
    def solveRelative(self, tcube) -> tCube:
        start_time = time.time()  # Start timing
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
            end_time = time.time()  # End timing
            self.sum_of_solve_relative_time += end_time - start_time  # Update sum of solve relative time
            return generalized_p
        else:
            end_time = time.time()  # End timing
            self.sum_of_solve_relative_time += end_time - start_time
            return None

    def generalize_predecessor(self, prev_cube:tCube, next_cube_expr, prevF):
        start_time = time.time()  # Start timing
        tcube_cp = prev_cube.clone()
        #logging.info("original size of !P (or CTI): ", len(tcube_cp.cubeLiterals))

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

        initial_size = len(tcube_cp.cubeLiterals)
        tcube_cp.remove_true()
        final_size = len(tcube_cp.cubeLiterals)
        reduction_percentage = ((initial_size - final_size) / initial_size) * 100 if initial_size > 0 else 0
        self.predecessor_generalization_reduction_percentages.append(reduction_percentage)  # Track reduction percentage

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
        end_time = time.time()  # End timing
        time_taken = end_time - start_time
        self.sum_of_predecessor_generalization_time += time_taken  # Update sum of generalization time
        return tcube_cp

    def getBadCube(self):
        start_time = time.time()
        logging.info("seek for bad cube...")
        s = Solver()
        s.add(substitute(substitute(Not(self.post.cube()), self.primeMap),self.inp_map))
        s.add(self.frames[-1].cube())
        s.add(self.trans.cube())
        
        res = s.check()
        end_time = time.time()
        self.sum_of_cti_producing_time += end_time - start_time

        if res == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, s.model(), remove_input=False)
            self.sanity_checker._debug_c_is_predecessor(res.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map)) 
            new_model = self.generalize_predecessor(res, Not(self.post.cube()), self.frames[-1].cube())
            self.sanity_checker._debug_c_is_predecessor(new_model.cube(), self.trans.cube(), self.frames[-1].cube(), substitute(substitute(self.post.cube(), self.primeMap),self.inp_map))
            new_model.remove_input()
            return new_model
        else:
            return None
    
if __name__ == '__main__':
    pass
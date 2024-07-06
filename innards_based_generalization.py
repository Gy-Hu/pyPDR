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
#import logging
import time
from rich.panel import Panel
import random
from pprint import pprint

class InnardsGeneralizer:
    def __init__(self, internal_signals):
        self.internal_signals = internal_signals

    def extend_lemma_with_innards(self, lemma: tCube):
        extended_lemma = lemma.clone()

        # Set each literal in the lemma to 0 and find implied innards
        for lit in lemma.cubeLiterals:
            if lit == True:
                continue
            var, val = _extract(lit)
            if val == False:
                implied_innards = self.find_implied_innards(var, BoolVal(False))
                for innard in implied_innards:
                    extended_lemma.cubeLiterals.append(innard)

        return extended_lemma

    def find_implied_innards(self, var, val):
        implied_innards = []

        # Perform constant propagation in the Tr_inn part of the netlist
        # to find implied innards when var is set to val
        for innard_var, innard_expr in self.internal_signals.items():
            propagation_res = self.is_implied(innard_expr, assignments=(var,val))
            if propagation_res is not None: # means it is constant False
                implied_innards.append(Bool(innard_var)==False)
        return implied_innards
    
    def is_implied(self, expr, assignments):
        # Create a copy of the expression
        expr_copy = substitute(expr, assignments)

        # Perform constant propagation
        def simplify_expr(expr):
            if self.is_const(expr):
                return expr
            
            if is_not(expr):
                arg = simplify_expr(expr.arg(0))
                if self.is_const(arg):
                    return BoolVal(not is_true(arg))
                return Not(arg)
            
            if is_and(expr):
                args = [simplify_expr(arg) for arg in expr.children()]
                if any(is_false(arg) for arg in args):
                    return BoolVal(False)
                args = [arg for arg in args if not is_true(arg)]
                if len(args) == 0:
                    return BoolVal(True)
                if len(args) == 1:
                    return args[0]
                return And(*args)
            
            if is_or(expr):
                args = [simplify_expr(arg) for arg in expr.children()]
                if any(is_true(arg) for arg in args):
                    return BoolVal(True)
                args = [arg for arg in args if not is_false(arg)]
                if len(args) == 0:
                    return BoolVal(False)
                if len(args) == 1:
                    return args[0]
                return Or(*args)
            
            return expr

        simplified_expr = simplify_expr(expr_copy)
        if is_false(simplified_expr):
            return simplified_expr
        else:
            return None

    def is_const(self, expr):
        return is_true(expr) or is_false(expr)
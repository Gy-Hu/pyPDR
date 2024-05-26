from z3 import *

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
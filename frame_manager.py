from z3 import *



class Frame:
    def __init__(self, lemmas):
        self.Lemma = lemmas
        self.pushed = [False] * len(lemmas)
        #self.litOrder = HeuristicLitOrder()

    def cube(self):
        #TODO: Simplify this?
        return And(self.Lemma)

    def add(self, cube, pushed=False, litOrderManager=None):
        cube.remove_true()
        #assert len(cube.cubeLiterals) != 0
        # if len(cube.cubeLiterals) == 0:
        #     return
        clause = Not(simplify(And(cube.cubeLiterals)))
        if str(clause) == 'False':
            return
        self.Lemma.append(clause)
        self.pushed.append(pushed)
        self.updateLitOrder(cube, litOrderManager)
    
    def addLemma(self, lemma, pushed=False):
        self.Lemma.append(lemma)
        self.pushed.append(pushed)

    def updateLitOrder(self, cube, litOrderManager):
        cube.remove_true()
        assert len(cube.cubeLiterals) != 0
        cube_lst = cube.cubeLiterals
        litOrderManager.count(cube_lst)
        litOrderManager.decay()

    def heuristic_lit_order(self, cube_literals, litOrderManager):
        ordered_literals = sorted(cube_literals, key=lambda l: litOrderManager.counts.get(str(l.children()[0]), 0), reverse=True)
        return ordered_literals

    def __repr__(self):
        return str(sorted(self.Lemma, key=str))
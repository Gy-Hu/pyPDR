from z3 import *



class Frame:
    def __init__(self, lemmas):
        self.Lemma = lemmas
        self.pushed = [False] * len(lemmas)
        self.Lemma_size = [0 * len(lemmas)]
        #self.litOrder = HeuristicLitOrder()

    def cube(self):
        #TODO: Simplify this?
        return And(self.Lemma)

    def block_cex(self, cube, pushed=False, litOrderManager=None):
        #cube.remove_true()
        #assert len(cube.cubeLiterals) != 0
        # if len(cube.cubeLiterals) == 0:
        #     return
        blocked_cube = Not(simplify(And(cube.cubeLiterals)))
        #assert str(blocked_cube) != 'False'
        # if blocked_cube == BoolVal(False): # the clause is always true -> Nothing to add
        #     return
        if is_true(blocked_cube) == True:
            return
        self.Lemma.append(blocked_cube)
        self.pushed.append(pushed)
        self.Lemma_size.append(len(cube.cubeLiterals))
        self.updateLitOrder(cube, litOrderManager)
    
    def addLemma(self, lemma, pushed=False):
        # block_cube = Not(simplify(And(lemma.cubeLiterals)))
        # if is_true(block_cube) == True:
        #     return
        self.Lemma.append(lemma)
        #self.Lemma_size.append(len(lemma.cubeLiterals))
        self.pushed.append(pushed)

    def updateLitOrder(self, cube, litOrderManager):
        cube.remove_true()
        assert len(cube.cubeLiterals) != 0
        cube_lst = cube.cubeLiterals
        litOrderManager.count(cube_lst)
        litOrderManager.decay()

    def heuristic_lit_order(self, cube_literals, litOrderManager):
        return sorted(
            cube_literals,
            key=lambda l: litOrderManager.counts.get(str(l.children()[0]), 0),
            reverse=False,
        )

    def __repr__(self):
        return str(sorted(self.Lemma, key=str))
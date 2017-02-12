from proveit import Literal, BinaryOperation
from proveit.common import A, B, x

SUPERSET = Literal(__package__, stringFormat = 'superset', latexFormat = r'\supset')
SUPERSET_EQ = Literal(__package__, stringFormat = 'superseteq', latexFormat = r'\supseteq')

class Superset(BinaryOperation):
    def __init__(self, superset, subset):
        BinaryOperation.__init__(self, SUPERSET, superset, subset)
        self.subset = self.operands[0]
        self.superset = self.operands[1]

    @classmethod
    def operatorOfOperation(subClass):
        return SUPERSET
        
class SupersetEq(BinaryOperation):
    def __init__(self, superset, subset):
        BinaryOperation.__init__(self, SUPERSET_EQ, superset, subset)
        self.superset = superset
        self.subset = subset
        
    @classmethod
    def operatorOfOperation(subClass):
        return SUPERSET_EQ

    def conclude(self, assumptions):
        from _theorems_ import supersetEqViaEquality
        if self.operands[0] == self.operands[1]:
            return supersetEqViaEquality.specialize({A:self.operands[0], B:self.operands[1]})

    def unfold(self, elemInstanceVar=x):
        '''
        From A superset B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        from _theorems_ import unfoldSupersetEq
        return unfoldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().checked({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A superset B, from the unfolded version,
        (forall_{x in B} x in A).
        '''
        from _theorems_ import foldSupersetEq
        return foldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

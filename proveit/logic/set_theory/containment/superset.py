from proveit import Literal, BinaryOperation
from proveit.common import A, B, x

SUPERSET_EQ = Literal(__package__, stringFormat = 'superseteq', latexFormat = r'\supseteq')

class SupersetEq(BinaryOperation):
    def __init__(self, superSet, subSet):
        BinaryOperation.__init__(self, SUPERSET_EQ, superSet, subSet)
        
    @classmethod
    def operatorOfOperation(subClass):
        return SUPERSET_EQ

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

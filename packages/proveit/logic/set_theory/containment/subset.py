from proveit import Literal, BinaryOperation, MultiVariable, Operation, Etcetera
from proveit._common_ import A, B, x
from proveit._common_ import f, S, Qmulti, xEtc

class Subset(BinaryOperation):
    # operator of the Subset operation
    _operator_ = Literal(stringFormat='subset', latexFormat=r'\subset', context=__file__)    
    
    def __init__(self, subset, superset):
        BinaryOperation.__init__(self, Subset._operator_, subset, superset)
        self.subset = self.operands[0]
        self.superset = self.operands[1]

class SubsetEq(BinaryOperation):
    # operator of the SubsetEq operation
    _operator_ = Literal(stringFormat='\subseteq', latexFormat=r'\subseteq', context=__file__)    

    def __init__(self, subset, superset):
        BinaryOperation.__init__(self, SubsetEq._operator_, subset, superset)
        self.subset = subset
        self.superset = superset

    def conclude(self, assumptions):
        from _theorems_ import subsetEqViaEquality
        if self.operands[0] == self.operands[1]:
            return subsetEqViaEquality.specialize({A:self.operands[0], B:self.operands[1]})
            
        # Check for special case of [{x | Q*(x)}_{x \in S}] \subseteq S
        from proveit.logic.set_theory._theorems_ import conditionedSubsetIsSubset
        from proveit.logic import SetOfAll
        if isinstance(self.subset, SetOfAll):
            setOfAll = self.subset
            if len(setOfAll.instanceVars)==1 and setOfAll.instanceElement == setOfAll.instanceVars[0] and setOfAll.domain==self.superset:
                Q_op, Q_op_sub = Etcetera(Operation(Qmulti, setOfAll.instanceVars)), setOfAll.conditions
                return conditionedSubsetIsSubset.specialize({S:setOfAll.domain, Q_op:Q_op_sub, x:setOfAll.instanceVars[0]})
            
    def unfold(self, elemInstanceVar=x):
        '''
        From A subseteq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        from _theorems_ import unfoldSubsetEq
        return unfoldSubsetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().checked({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A subseteq B, from the unfolded version,
        (forall_{x in A} x in B).
        '''
        from _theorems_ import foldSubsetEq
        return foldSubsetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

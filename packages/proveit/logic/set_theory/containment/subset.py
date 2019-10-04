from proveit import Literal, Operation, safeDummyVar, USE_DEFAULTS, asExpression
from proveit._common_ import A, B, C, x
from proveit._common_ import f, S, QQ
from .containment_relation import ContainmentRelation, ContainmentSequence, makeSequenceOrRelation

class SubsetRelation(ContainmentRelation):
    def __init__(self, operator, subset, superset):
        ContainmentRelation.__init__(self, operator, subset, superset)
        self.subset = self.operands[0]
        self.superset = self.operands[1]
    
    @staticmethod
    def WeakRelationClass():
        return SubsetEq 

    @staticmethod
    def StrongRelationClass():
        return Subset
    
    @staticmethod
    def SequenceClass():
        return SubsetSequence

class SubsetSequence(ContainmentSequence):
    def __init__(self, operators, operands):
        ContainmentSequence.__init__(self, operators, operands)
    
    @staticmethod
    def RelationClass():
        return SubsetRelation

def subsetSequence(operators, operands):
    '''
    Create a SubsetSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return makeSequenceOrRelation(SubsetSequence, operators, operands)
  
class Subset(SubsetRelation):    
    # operator of the Subset operation
    _operator_ = Literal(stringFormat='subset', latexFormat=r'\subset', context=__file__)    

    # map left-hand-sides to Subset KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to Subset KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()        
    
    def __init__(self, subset, superset):
        SubsetRelation.__init__(self, Subset._operator_, subset, superset)
 
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A subset B, derive B supset A.
        '''
        from ._theorems_ import reverseSubset
        return reverseSubset.specialize({A:self.subset, B:self.superset}, assumptions=assumptions)
       
    def deriveRelaxed(self, assumptions=USE_DEFAULTS):
        '''
        From A subset B, derive A subseteq B.
        '''
        from ._theorems_ import relaxSubset
        return relaxSubset.specialize({A:self.subset, B:self.superset}, assumptions=assumptions)
            
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this A subset B expression 
        and something of the form B subseteq C, B subset C, or B=C to 
        obtain A subset B as appropriate.
        '''
        from proveit.logic import Equals, Subset, SubsetEq
        from ._theorems_ import transitivitySubsetSubset, transitivitySubsetSubsetEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(other, assumptions) # handles this special case
       # if isinstance(other,Subset) or isinstance(other,SubsetEq):
        #    other = other.deriveReversed(assumptions)
        if other.lhs == self.rhs:
            if isinstance(other,Subset):
                result = transitivitySubsetSubset.specialize({A:self.lhs, B:self.rhs, C:other.rhs}, assumptions=assumptions)
                return result
            elif isinstance(other,SubsetEq):
                result = transitivitySubsetSubsetEq.specialize({A:self.lhs, B:self.rhs, C:other.rhs}, assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,Subset):
                result = transitivitySubsetSubset.specialize({A:self.lhs, B:self.rhs, C:other.lhs}, assumptions=assumptions)
                return result
            elif isinstance(other,SubsetEq):
                result = transitivitySubsetSubsetEq.specialize({A:self.lhs, B:self.rhs, C:other.lhs}, assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))


class SubsetEq(SubsetRelation):
    # operator of the SubsetEq operation
    _operator_ = Literal(stringFormat='subseteq', latexFormat=r'\subseteq', context=__file__)    

    # map left-hand-sides to SubsetEq KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to SubsetEq KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()      
    
    def __init__(self, subset, superset):
        SubsetRelation.__init__(self, SubsetEq._operator_, subset, superset)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive B supseteq A.
        '''
        from ._theorems_ import reverseSubsetEq
        return reverseSubsetEq.specialize({A:self.subset, B:self.superset}, assumptions=assumptions)
        
    def conclude(self, assumptions):
        from proveit import ProofFailure
        from proveit.logic import SetOfAll, Equals

        # Any set contains itself
        try:
            Equals(*self.operands).prove(assumptions, automation=False)
            return self.concludeViaEquality(assumptions)
        except ProofFailure:
            pass
                
        try:
            # Attempt a transitivity search
            return ContainmentRelation.conclude(self, assumptions)
        except ProofFailure:
            pass # transitivity search failed
        
        # Check for special case of [{x | Q*(x)}_{x \in S}] \subseteq S
        if isinstance(self.subset, SetOfAll):
            from proveit.logic.set_theory.comprehension._theorems_ import comprehensionIsSubset
            setOfAll = self.subset
            if len(setOfAll.instanceVars)==1 and setOfAll.instanceElement == setOfAll.instanceVars[0] and setOfAll.domain==self.superset:
                Q_op, Q_op_sub = Operation(Qmulti, setOfAll.instanceVars), setOfAll.conditions
                return comprehensionIsSubset.specialize({S:setOfAll.domain, Q_op:Q_op_sub}, relabelMap={x:setOfAll.instanceVars[0]}, assumptions=assumptions)
        
        # Finally, attempt to conclude A subseteq B via forall_{x in A} x in B.
        # Issue: Variables do not match when using safeDummyVar: _x_ to x.
        # We need to automate this better, right now it is only practical to do concludeAsFolded manually.
        return self.concludeAsFolded(elemInstanceVar=safeDummyVar(self), assumptions=assumptions)
    
    def concludeViaEquality(self, assumptions):
        from ._theorems_ import subsetEqViaEquality
        return subsetEqViaEquality.specialize({A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)        
    
    def unfold(self, elemInstanceVar=x, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        from ._theorems_ import unfoldSubsetEq
        return unfoldSubsetEq.specialize({A:self.subset, B:self.superset}, relabelMap={x:elemInstanceVar}, assumptions=assumptions)
    
    def deriveSupsersetMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B and x in A, derive x in B.
        '''
        from ._theorems_ import unfoldSubsetEq
        return unfoldSubsetEq.specialize({A:self.subset, B:self.superset, x:element}, assumptions=assumptions)
    
    def concludeAsFolded(self, elemInstanceVar=x, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A subseteq B, from the unfolded version,
        (forall_{x in A} x in B).
        '''
        from ._theorems_ import foldSubsetEq
        return foldSubsetEq.specialize({A:self.subset, B:self.superset}, relabelMap={x:elemInstanceVar}, assumptions=assumptions).deriveConsequent(assumptions)
    
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this A subseteq B expression 
        and something of the form B subseteq C, B subset C, or B=C to 
        obtain A subset B or A subseteq B as appropriate.
        '''
        from proveit.logic import Equals, Subset, SubsetEq
        from ._theorems_ import transitivitySubsetEqSubset, transitivitySubsetEqSubsetEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(other, assumptions) # handles this special case
        #if isinstance(other,Subset) or isinstance(other,SubsetEq):
         #   other = other.deriveReversed(assumptions)
        if other.lhs == self.rhs:
            if isinstance(other,Subset):
                return transitivitySubsetEqSubset.specialize({A:self.lhs, B:self.rhs, C:other.rhs}, assumptions=assumptions)
            elif isinstance(other,SubsetEq):
                return transitivitySubsetEqSubsetEq.specialize({A:self.lhs, B:self.rhs, C:other.rhs}, assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other,Subset):
                return transitivitySubsetEqSubset.specialize({A:self.lhs, B:self.rhs, C:other.lhs}, assumptions=assumptions)
            elif isinstance(other,SubsetEq):
                return transitivitySubsetEqSubsetEq.specialize({A:self.lhs, B:self.rhs, C:other.lhs}, assumptions=assumptions)
        else:
            raise ValueError("Cannot perform transitivity with %s and %s!"%(self, other))


class NotSubset(Operation):
    # operator of the NotSubset operation
    _operator_ = Literal(stringFormat='nsubset',
                         latexFormat=r'\not\subset',
                         context=__file__)    

    def __init__(self, subset, superset):
        Operation.__init__(self, NotSubset._operator_, (subset, superset))
    
    def deriveSideEffects(self, knownTruth):
        self.unfold(knownTruth.assumptions) # unfold as an automatic side-effect

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsubset B, derive and return not(supset(A, B)).
        '''
        from ._theorems_ import unfoldNotSubset
        return unfoldNotSubset.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded version,
        not(A supset B).
        '''
        from ._theorems_ import foldNotSubset
        return foldNotSubset.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

class NotSubsetEq(Operation):
    # operator of the NotSubsetEq operation
    _operator_ = Literal(stringFormat='nsubseteq', latexFormat=r'\nsubseteq', context=__file__)    

    def __init__(self, subset, superset):
        Operation.__init__(self, NotSubsetEq._operator_, (subset, superset))
    
    def deriveSideEffects(self, knownTruth):
        self.unfold(knownTruth.assumptions) # unfold as an automatic side-effect

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsubseteq B, derive and return not(supseteq(A, B)).
        '''
        from ._theorems_ import unfoldNotSubsetEq
        return unfoldNotSubsetEq.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded version,
        not(A supset B).
        '''
        from ._theorems_ import foldNotSubsetEq
        return foldNotSubsetEq.specialize({A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

# Provide an alias for Subset and SubsetProper
ProperSubset = Subset
SubsetProper = Subset

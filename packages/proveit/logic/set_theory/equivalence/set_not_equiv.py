from proveit import Literal, Operation, USE_DEFAULTS
from .set_equiv import SetEquiv
# from .equals import Equals
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit._common_ import A, B

class SetNotEquiv(Operation):
    '''
    Class to capture the LACK of membership equivalence of 2 sets
    A and B. SetNotEquiv(A, B) is a claim that at least one element of
    set A does not also appear in set B, and/or vice versa.
    Like the SetEquiv class, the SetNotEquiv relation uses the
    (negated) congruence symbol to distinguish the SetNotEquiv claims
    from the distinctive claim that A ≠ B. The class was initially
    established using the class NotEquals as an archetype.
    '''
    # operator of the SetNotEquiv operation
    _operator_ = Literal(stringFormat='not_equiv',
                         latexFormat=r'\ncong',
                         context=__file__)
    
    def __init__(self, a, b):
        Operation.__init__(self, SetNotEquiv._operator_, (a, b))
        self.lhs = self.operands[0]
        self.rhs = self.operands[1]
            
    def sideEffects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for
        this SetNotEquiv operation.
        '''
        from proveit.logic.boolean._common_ import FALSE
        # automatically derive the reversed form which is equivalent
        yield self.deriveReversed # B not_equiv A from A not_equiv B
        # if self.rhs==FALSE:
        #     yield self.deriveViaDoubleNegation # A from A != False and A in Booleans
        # yield self.unfold # Not(x=y) from x != y
    
    # def conclude(self, assumptions):
    #     from proveit.logic import FALSE
    #     if isIrreducibleValue(self.lhs) and isIrreducibleValue(self.rhs):
    #         # prove that two irreducible values are not equal
    #         return self.lhs.notEqual(self.rhs, assumptions)
    #     if self.lhs == FALSE or self.rhs == FALSE:
    #         try:
    #             # prove something is not false by proving it to be true
    #             return self.concludeViaDoubleNegation(assumptions)
    #         except:
    #             pass
    #     if hasattr(self.lhs, 'notEqual') and isIrreducibleValue(self.rhs):
    #         try:
    #             return self.lhs.notEqual(self.rhs, assumptions)
    #         except:
    #             pass
    #     try:
    #         return self.concludeAsFolded(assumptions)
    #     except:
    #         return Operation.conclude(assumptions) # try the default (reduction)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A not_equiv B derive B not_equiv A.
        Derived automatically as a side-effect in sideEffects() method.
        '''
        from ._theorems_ import setNotEquivReversal
        return setNotEquivReversal.instantiate({A:self.lhs, B:self.rhs},
                                              assumptions=assumptions)
        

    # Later consider a form of double negation like
    # Not(SetNotEquiv(A, B)) giving SetEquiv(A, B)
    # Useful or not?
    # def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     From A != FALSE, derive and return A assuming inBool(A).
    #     Also see version in Not class.
    #     '''
    #     from proveit.logic import FALSE
    #     from proveit.logic.boolean._theorems_ import fromNotFalse
    #     if self.rhs == FALSE:
    #         return fromNotFalse.instantiate({A:self.lhs})
    #     raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form A != FALSE")

    # def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     Prove and return self of the form A != FALSE or FALSE != A assuming A.
    #     Also see version in Not class.
    #     '''
    #     from proveit.logic import FALSE
    #     from proveit.logic.boolean._theorems_ import notEqualsFalse
    #     if self.lhs == FALSE:
    #         # switch left and right sides and prove it that way.
    #         NotEquals(self.rhs, self.lhs).prove(assumptions)
    #         return self.prove()
    #     if self.rhs == FALSE:
    #         return notEqualsFalse.instantiate({A:self.lhs}, assumptions=assumptions)

    def definition(self):
        '''
        Return (A not_equiv B) = Not(A equiv B) where self represents
        (A not_equiv B).
        '''
        from ._axioms_ import setNotEquivDef
        return setNotEquivDef.instantiate({A:self.lhs, B:self.rhs})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (A not_equiv B) derive and return Not(A equiv B).
        '''
        from ._theorems_ import unfoldSetNotEquiv
        return unfoldSetNotEquiv.instantiate(
            {A:self.lhs, B:self.rhs}, assumptions=assumptions)
    
    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (A not_equiv B) from Not(A equiv B).
        '''
        from ._theorems_ import foldSetNotEquiv
        return foldSetNotEquiv.instantiate(
                {A:self.lhs, B:self.rhs}, assumptions=assumptions)
        
    # def evaluation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     Given operands that may be evaluated to irreducible values that
    #     may be compared, or if there is a known evaluation of this
    #     inequality, derive and return this expression equated to
    #     TRUE or FALSE.
    #     '''
    #     definitionEquality = self.definition()
    #     unfoldedEvaluation = definitionEquality.rhs.evaluation(assumptions)        
    #     return Equals(self, unfoldedEvaluation.rhs).prove(assumptions)

    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A not_equiv B, and assuming (A equiv B),
        derive and return FALSE.
        '''
        from ._theorems_ import setNotEquivContradiction
        return setNotEquivContradiction.instantiate(
                {A:self.lhs, B:self.rhs}, assumptions=assumptions)
    
    # def affirmViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
    #     '''
    #     From A not_equiv B, derive the conclusion, provided that
    #     the negated conclusion implies ((A not_equiv B) AND
    #     (A equiv B)), and the conclusion is a Boolean.
    #     Still being considered here.
    #     '''
    #     from proveit.logic.boolean.implication import affirmViaContradiction
    #     return affirmViaContradiction(self, conclusion, assumptions)

    # def denyViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
    #     '''
    #     From x != y, derive the negated conclusion provided that the conclusion
    #     implies x != y and x = y, and the conclusion is a Boolean.
    #     '''
    #     from proveit.logic.boolean.implication import denyViaContradiction
    #     return denyViaContradiction(self, conclusion, assumptions)
                        
    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'not equiv' statement is in
        the set of BOOLEANS.
        '''
        from ._theorems_ import setNotEquivInBool
        return setNotEquivInBool.instantiate({A:self.lhs, B:self.rhs})

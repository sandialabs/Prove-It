from proveit import Literal, Operation, USE_DEFAULTS
from .set_equiv import SetEquiv
# from .equals import Equals
from proveit.logic.irreducible_value import is_irreducible_value
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
    _operator_ = Literal(string_format='not_equiv',
                         latex_format=r'\ncong',
                         theory=__file__)
    
    def __init__(self, a, b):
        Operation.__init__(self, SetNotEquiv._operator_, (a, b))
        self.lhs = self.operands[0]
        self.rhs = self.operands[1]
            
    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for
        this SetNotEquiv operation.
        '''
        from proveit.logic.booleans._common_ import FALSE
        # automatically derive the reversed form which is equivalent
        yield self.derive_reversed # B not_equiv A from A not_equiv B
        # if self.rhs==FALSE:
        #     yield self.derive_via_double_negation # A from A != False and A in Boolean
        # yield self.unfold # Not(x=y) from x != y
    
    # def conclude(self, assumptions):
    #     from proveit.logic import FALSE
    #     if is_irreducible_value(self.lhs) and is_irreducible_value(self.rhs):
    #         # prove that two irreducible values are not equal
    #         return self.lhs.not_equal(self.rhs, assumptions)
    #     if self.lhs == FALSE or self.rhs == FALSE:
    #         try:
    #             # prove something is not false by proving it to be true
    #             return self.conclude_via_double_negation(assumptions)
    #         except:
    #             pass
    #     if hasattr(self.lhs, 'not_equal') and is_irreducible_value(self.rhs):
    #         try:
    #             return self.lhs.not_equal(self.rhs, assumptions)
    #         except:
    #             pass
    #     try:
    #         return self.conclude_as_folded(assumptions)
    #     except:
    #         return Operation.conclude(assumptions) # try the default (reduction)
    
    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From A not_equiv B derive B not_equiv A.
        Derived automatically as a side-effect in side_effects() method.
        '''
        from ._theorems_ import set_not_equiv_reversal
        return set_not_equiv_reversal.instantiate({A:self.lhs, B:self.rhs},
                                              assumptions=assumptions)
        

    # Later consider a form of double negation like
    # Not(SetNotEquiv(A, B)) giving SetEquiv(A, B)
    # Useful or not?
    # def derive_via_double_negation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     From A != FALSE, derive and return A assuming in_bool(A).
    #     Also see version in Not class.
    #     '''
    #     from proveit.logic import FALSE
    #     from proveit.logic.booleans._theorems_ import from_not_false
    #     if self.rhs == FALSE:
    #         return from_not_false.instantiate({A:self.lhs})
    #     raise ValueError("derive_via_double_negation does not apply to " + str(self) + " which is not of the form A != FALSE")

    # def conclude_via_double_negation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     Prove and return self of the form A != FALSE or FALSE != A assuming A.
    #     Also see version in Not class.
    #     '''
    #     from proveit.logic import FALSE
    #     from proveit.logic.booleans._theorems_ import not_equals_false
    #     if self.lhs == FALSE:
    #         # switch left and right sides and prove it that way.
    #         NotEquals(self.rhs, self.lhs).prove(assumptions)
    #         return self.prove()
    #     if self.rhs == FALSE:
    #         return not_equals_false.instantiate({A:self.lhs}, assumptions=assumptions)

    def definition(self):
        '''
        Return (A not_equiv B) = Not(A equiv B) where self represents
        (A not_equiv B).
        '''
        from ._axioms_ import set_not_equiv_def
        return set_not_equiv_def.instantiate({A:self.lhs, B:self.rhs})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (A not_equiv B) derive and return Not(A equiv B).
        '''
        from ._theorems_ import unfold_set_not_equiv
        return unfold_set_not_equiv.instantiate(
            {A:self.lhs, B:self.rhs}, assumptions=assumptions)
    
    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (A not_equiv B) from Not(A equiv B).
        '''
        from ._theorems_ import fold_set_not_equiv
        return fold_set_not_equiv.instantiate(
                {A:self.lhs, B:self.rhs}, assumptions=assumptions)
        
    # def evaluation(self, assumptions=USE_DEFAULTS):
    #     '''
    #     Given operands that may be evaluated to irreducible values that
    #     may be compared, or if there is a known evaluation of this
    #     inequality, derive and return this expression equated to
    #     TRUE or FALSE.
    #     '''
    #     definition_equality = self.definition()
    #     unfolded_evaluation = definition_equality.rhs.evaluation(assumptions)        
    #     return Equals(self, unfolded_evaluation.rhs).prove(assumptions)

    def derive_contradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A not_equiv B, and assuming (A equiv B),
        derive and return FALSE.
        '''
        from ._theorems_ import set_not_equiv_contradiction
        return set_not_equiv_contradiction.instantiate(
                {A:self.lhs, B:self.rhs}, assumptions=assumptions)
    
    # def affirm_via_contradiction(self, conclusion, assumptions=USE_DEFAULTS):
    #     '''
    #     From A not_equiv B, derive the conclusion, provided that
    #     the negated conclusion implies ((A not_equiv B) AND
    #     (A equiv B)), and the conclusion is a Boolean.
    #     Still being considered here.
    #     '''
    #     from proveit.logic.booleans.implication import affirm_via_contradiction
    #     return affirm_via_contradiction(self, conclusion, assumptions)

    # def deny_via_contradiction(self, conclusion, assumptions=USE_DEFAULTS):
    #     '''
    #     From x != y, derive the negated conclusion provided that the conclusion
    #     implies x != y and x = y, and the conclusion is a Boolean.
    #     '''
    #     from proveit.logic.booleans.implication import deny_via_contradiction
    #     return deny_via_contradiction(self, conclusion, assumptions)
                        
    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'not equiv' statement is in
        the set of BOOLEANS.
        '''
        from ._theorems_ import set_not_equiv_is_bool
        return set_not_equiv_is_bool.instantiate({A:self.lhs, B:self.rhs})

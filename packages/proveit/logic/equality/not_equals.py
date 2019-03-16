from proveit import Literal, Operation, USE_DEFAULTS
from .equals import Equals
from proveit.logic.irreducible_value import isIrreducibleValue
from proveit._common_ import x, y, A, X

class NotEquals(Operation):
    # operator of the NotEquals operation
    _operator_ = Literal(stringFormat='!=', latexFormat=r'\neq', context=__file__)
    
    def __init__(self, a, b):
        Operation.__init__(self, NotEquals._operator_, (a, b))
        self.lhs = self.operands[0]
        self.rhs = self.operands[1]
            
    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for
        this NotEquals operation.
        '''
        from proveit.logic.boolean._common_ import FALSE
        # automatically derive the reversed form which is equivalent
        yield self.deriveReversed # y != x from x != y
        if self.rhs==FALSE:
            yield self.deriveViaDoubleNegation # A from A != False and A in Booleans
        yield self.unfold # Not(x=y) from x != y
    
    def conclude(self, assumptions):
        from proveit.logic import FALSE
        if isIrreducibleValue(self.lhs) and isIrreducibleValue(self.rhs):
            # prove that two irreducible values are not equal
            return self.lhs.notEqual(self.rhs, assumptions)
        if self.lhs == FALSE or self.rhs == FALSE:
            try:
                # prove something is not false by proving it to be true
                return self.concludeViaDoubleNegation(assumptions)
            except:
                pass
        if hasattr(self.lhs, 'notEqual') and isIrreducibleValue(self.rhs):
            try:
                return self.lhs.notEqual(self.rhs, assumptions)
            except:
                pass
        try:
            return self.concludeAsFolded(assumptions)
        except:
            return Operation.conclude(assumptions) # try the default (reduction)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From x != y derive y != x.
        '''
        from ._theorems_ import notEqualsSymmetry
        return notEqualsSymmetry.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
        
    def deriveViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        '''
        From A != FALSE, derive and return A assuming inBool(A).
        Also see version in Not class.
        '''
        from proveit.logic import FALSE
        from proveit.logic.boolean._theorems_ import fromNotFalse
        if self.rhs == FALSE:
            return fromNotFalse.specialize({A:self.lhs})
        raise ValueError("deriveViaDoubleNegation does not apply to " + str(self) + " which is not of the form A != FALSE")

    def concludeViaDoubleNegation(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form A != FALSE or FALSE != A assuming A.
        Also see version in Not class.
        '''
        from proveit.logic import FALSE
        from proveit.logic.boolean._theorems_ import notEqualsFalse
        if self.lhs == FALSE:
            # switch left and right sides and prove it that way.
            NotEquals(self.rhs, self.lhs).prove(assumptions)
            return self.prove()
        if self.rhs == FALSE:
            return notEqualsFalse.specialize({A:self.lhs}, assumptions=assumptions)

    def definition(self):
        '''
        Return (x != y) = Not(x=y) where self represents (x != y).
        '''
        from ._axioms_ import notEqualsDef
        return notEqualsDef.specialize({x:self.lhs, y:self.rhs})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from ._theorems_ import unfoldNotEquals
        return unfoldNotEquals.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
    
    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Conclude (x != y) from Not(x = y).
        '''
        from ._theorems_ import foldNotEquals
        return foldNotEquals.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
        
    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        Given operands that may be evaluated to irreducible values that
        may be compared, or if there is a known evaluation of this
        inequality, derive and return this expression equated to
        TRUE or FALSE.
        '''
        definitionEquality = self.definition()
        unfoldedEvaluation = definitionEquality.rhs.evaluation(assumptions)        
        return Equals(self, unfoldedEvaluation.rhs).prove(assumptions)

    def deriveContradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From x != y, and assuming x = y, derive and return FALSE.
        '''
        from ._theorems_ import notEqualsContradiction
        return notEqualsContradiction.specialize({x:self.lhs, y:self.rhs}, assumptions=assumptions)
    
    def affirmViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From x != y, derive the conclusion provided that the negated conclusion
        implies x != y and x = y, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import affirmViaContradiction
        return affirmViaContradiction(self, conclusion, assumptions)

    def denyViaContradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From x != y, derive the negated conclusion provided that the conclusion
        implies x != y and x = y, and the conclusion is a Boolean.
        '''
        from proveit.logic.boolean.implication import denyViaContradiction
        return denyViaContradiction(self, conclusion, assumptions)
                        
    def deduceInBool(self):
        '''
        Deduce and return that this 'not equals' statement is in the set of BOOLEANS.
        '''
        from ._theorems_ import notEqualsInBool
        return notEqualsInBool.specialize({x:self.lhs, y:self.rhs})

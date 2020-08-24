from proveit import (Context, defaults, Literal, Operation,
                     ProofFailure, TransitiveRelation, USE_DEFAULTS)

class Divides(TransitiveRelation):
    '''
    Divides(x, y) represents the claim that x divides y (i.e. x|y)
    (equivalently, that x is a factor of y, y is a multiple of x,
    or y/x is an integer). The underlying axiomatic definition uses
    the y/x is an integer formulation and allows x and y to be any
    complex number as long as x ≠ 0.
    '''

    _operator_ = Literal(
    	  stringFormat='|', latexFormat=r'\rvert', context=__file__
    	  )

    # map left-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict() 
    
    def __init__(self, a, b):
        TransitiveRelation.__init__(self, Divides._operator_, a, b)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude the divisibility claim in various ways:
        (1) simple reflexivity (x=x);
        (2) simple 0/x for x ≠ 0;
        (3) via transitivity.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=() (thus averting len(None) errors)
        assumptions = defaults.checkedAssumptions(assumptions)

        from proveit.logic import TRUE, FALSE, Implies, Iff, inBool

        #-- -------------------------------------------------------- --#
        #-- Case (1): x|x with x ≠ 0 known or assumed                --#
        #-- -------------------------------------------------------- --#
        from proveit.logic import InSet, NotEquals
        from proveit.number import zero, Complexes
        if self.lhs==self.rhs:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                InSet(self.lhs, Complexes).proven(assumptions=assumptions)):
                # Trivial x|x with complex x ≠ 0
                return self.concludeViaReflexivity(assumptions)
            else:
                err_str =  (
                        "Divides.conclude() Failure. Unable to "
                        "automatically conclude by standard means. "
                        "Although lhs = rhs = {0}, either {0} is not "
                        "known to be unequal to 0 or {0} is not known "
                        "to be in the complex numbers (or both). "
                        "Try proving one or both of those claims first.".
                        format(self.lhs))
                raise ProofFailure(self, assumptions, err_str)

        #-- -------------------------------------------------------- --#
        #-- Case (2): x|0 with x ≠ 0 known or assumed                --#
        #-- -------------------------------------------------------- --#
        if self.rhs==zero:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                InSet(self.lhs, Complexes).proven(assumptions=assumptions)):
                # We have 0/x with complex x ≠ 0
                return self.concludeViaZeroFactor(assumptions)


    def concludeViaReflexivity(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x|x with x ≠ 0.
        '''
        from ._theorems_ import dividesReflexivity
        _x = dividesReflexivity.instanceVar
        assert self.lhs == self.rhs
        return dividesReflexivity.instantiate(
                {_x:self.lhs}, assumptions=assumptions)

    def concludeViaZeroFactor(self, assumptions=USE_DEFAULTS):
       '''
       Prove and return self of the form x|0 for x ≠ 0
       '''
       from ._theorems_ import nonZeroDividesZero
       _x = nonZeroDividesZero.instanceVar
       return nonZeroDividesZero.instantiate(
                {_x:self.lhs}, assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'Divides' expression is in
        the set of Booleans.
        '''
        from ._theorems_ import dividesInBool
        x, y = dividesInBool.instanceVars
        return dividesInBool.specialize(
        	  {x:self.operands[0], y:self.operands[1]}, assumptions=assumptions)
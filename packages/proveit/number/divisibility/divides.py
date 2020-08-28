from proveit import (asExpression, Context, defaults, Literal, Operation,
                     ProofFailure, TransitiveRelation, USE_DEFAULTS)

class DividesRelation(TransitiveRelation):

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)

    def lower(self):
        '''
        Returns the lower bound side of this inequality.
        '''
        return self.lhs

    def upper(self):
        '''
        Returns the upper bound side of this inequality.
        '''
        return self.rhs
    
    @staticmethod
    def WeakRelationClass():
        # Divides is weaker than DividesProper (yet to be defined)
        # analogous to <= being weaker than <
        return Divides # Divides is weaker than DividesProper

    @staticmethod
    def StrongRelationClass():
        # might later have a DividesProper here, which would
        # be like Divides(x, y) but requiring x != y
        return DividesProper # DividesProper is stronger than Divides               


class Divides(DividesRelation):
    '''
    Divides(x, y) represents the claim that x divides y (i.e. x|y)
    (equivalently, that x is a factor of y, y is a multiple of x,
    or y/x is an integer). The underlying axiomatic definition uses
    x|y = (y/x in Z), with no prerequisites on x and y. Extending
    DividesRelation allows the possibility (later) of having not only
    this weak relation class but also a strong relation class, perhaps
    DividesProper, yet to be defined.
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
        DividesRelation.__init__(self, Divides._operator_, a, b)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude the divisibility claim in various ways:
        (1) simple reflexivity (x|x);
        (2) simple x|0 for x ≠ 0;
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

        #-- -------------------------------------------------------- --#
        #-- Case (3): x|z with x|y and y|z known or assumed          --#
        #-- -------------------------------------------------------- --#
        # seek out the appropriate x|y and y|z and use transitivity
        # to get x|z
        # try:
        #     return self.concludeViaTransitivity(assumptions)
        # except:
        #     pass
        return self.concludeViaTransitivity(assumptions)

        raise ProofFailure(self, assumptions, 
                           "Unable to automatically conclude by "
                           "standard means.")


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

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From x|y (self) and y|z (other) derive and return x|z.
        Will also check for y|z (self) and x|y (other) to return x|z.
        '''
        from ._theorems_ import dividesTransitivity
        _x, _y, _z = dividesTransitivity.instanceParams
        other = asExpression(other)
        if not isinstance(other, Divides):
            raise ValueError(
                "Unsupported transitivity operand: Divides.applyTransitivity() "
                "method requires another Divides expression for transitivity "
                "to be applied. Instead, received the following input: {0}.".
                format(other))

        if self.rhs == other.lhs:
            return dividesTransitivity.instantiate(
                    {_x:self.lhs, _y:self.rhs, _z:other.rhs},
                    assumptions=assumptions)
        if self.lhs == other.rhs:
            return dividesTransitivity.instantiate(
                    {_x:other.lhs, _y:other.rhs, _z:self.rhs},
                    assumptions=assumptions)
        else:
            raise TransitivityException(
                self, assumptions,
                'Transitivity cannot be applied unless the lhs of one of '
                'Divides expressions is equal to the rhs of the other '
                'Divides expression. Instead we have: {0} vs {1}'.
                format(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'Divides' expression is in
        the set of Booleans.
        '''
        from ._theorems_ import dividesInBool
        _x, _y = dividesInBool.instanceParams
        return dividesInBool.specialize(
        	  {_x:self.operands[0], _y:self.operands[1]},
              assumptions=assumptions)

class DividesProper(DividesRelation):
    '''
    DividesProper(x, y) represents the claim that x divides y
    (i.e. x|y) but x != y. x|y is equivalent to saying that x is a
    factor of y, y is a multiple of x, or y/x is an integer).
    This class is still under development, with the class stub located
    here so that we have a 'strong relation' class version of Divides
    that can be called from the DividesRelation class, which in turn
    allows us to use the TransitiveRelation.concudeViaTransitivity()
    method.
    '''

    _operator_ = Literal(
          stringFormat='|', latexFormat=r'\rvert_{P}', context=__file__
          )

    # map left-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()    
    # map right-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict() 
    
    def __init__(self, a, b):
        DividesRelation.__init__(self, DividesProper._operator_, a, b)

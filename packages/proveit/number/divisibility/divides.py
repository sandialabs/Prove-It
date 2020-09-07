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
        # Divides is weaker than DividesProper (in development)
        # analogous to <= being weaker than <
        return Divides # Divides is weaker than DividesProper

    @staticmethod
    def StrongRelationClass():
        # DividesProper (in development) is stronger than Divides.
        # DividesProper(x, y) is like Divides(x, y) but requires x != y
        return DividesProper # DividesProper is stronger than Divides


class Divides(DividesRelation):
    '''
    Divides(x, y) represents the claim that x divides y (i.e. x|y)
    (equivalently, x is a factor of y, y is a multiple of x, or
    y/x is an integer). The axiomatic definition in Prove-It uses
    x|y = (y/x in Z), with no prerequisites on x and y. Extending
    DividesRelation allows us to have not only this weak relation
    class but also a strong relation class, DividesProper, the pair
    combined then allowing the calling of
    Divides.concludeViaTransitivity()
    utilizing the TransitiveRelation.concludeViaTransitivity() method.
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
        (3) simple x|xy or x|yx scenario
        (4) via transitivity.
        '''
        # Check validity of assumptions (and convert assumptions=None
        # to assumptions=(), thus averting len(None) errors).
        assumptions = defaults.checkedAssumptions(assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (1): x|x with x != 0 known or assumed               --#
        #-- -------------------------------------------------------- --#
        from proveit.logic import InSet, NotEquals
        from proveit.number import zero, Complexes
        err_str = "In Divides.conclude() we tried:\n"
        if self.lhs==self.rhs:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                InSet(self.lhs, Complexes).proven(assumptions=assumptions)):
                # Trivial x|x with complex x ≠ 0
                return self.concludeViaReflexivity(assumptions)
            else:
                err_str =  err_str + (
                        "Case: lhs = rhs. "
                        "Although lhs = rhs = {0}, either {0} is not known to "
                        "be non-zero or {0} is not known to be in the complex "
                        "numbers (or both). Try proving one or both of those "
                        "claims first.\n".format(self.lhs))
                # raise ProofFailure(self, assumptions, err_str)

        #-- -------------------------------------------------------- --#
        #-- Case (2): x|0 with x != 0 known or assumed               --#
        #-- -------------------------------------------------------- --#
        if self.rhs==zero:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                InSet(self.lhs, Complexes).proven(assumptions=assumptions)):
                # We have 0/x with complex x ≠ 0
                return self.concludeViaZeroFactor(assumptions)
            else:
                err_str = err_str + (
                        "Case: rhs = 0. "
                        "Although rhs = 0, either the lhs {0} is not known to "
                        "be non-zero or {0} is not known to be in the complex "
                        "numbers (or both). Try proving one or both of those "
                        "claims first.\n".format(self.lhs))

        #-- -------------------------------------------------------- --#
        #-- Case (3): very simple version of x|xy or x|yx            --#
        #-- -------------------------------------------------------- --#
        # return self.concludeViaFactor(assumptions)
        try:
            return self.concludeViaFactor(assumptions)
        except Exception as e:
            err_str = err_str + (
                    "Case: x|xy. This possible case returned the following "
                    "error message: {0} \n".format(e))
            pass

        #-- -------------------------------------------------------- --#
        #-- Case (4): x|z with x|y and y|z known or assumed          --#
        #-- -------------------------------------------------------- --#
        # Seek out the appropriate x|y and y|z and use transitivity
        # to get x|z, utilizing the concludeViaTransitivity() method
        # available for instances of TransitiveRelation
        try:
            return self.concludeViaTransitivity(assumptions)
        except Exception as e:
            err_str = err_str + (
                    "Case: transitivity search. In attempting to use "
                    "concludeViaTransitivity(), obtained the following "
                    "error message: {0}.".format(e))
            pass

        raise ProofFailure(self, assumptions, err_str)


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

    def concludeViaFactor(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x|xy for x ≠ 0 and y in Ints
        '''
        from proveit.number import Mult
        if isinstance(self.rhs, Mult):
            if len(self.rhs.operands) == 2:
                # should check to make sure none of the operands
                # are actually ExprRanges (later!)
                if self.lhs == self.rhs.operands[0]:
                    # apply left version
                    from ._theorems_ import leftFactorDivisibility
                    _x, _y = leftFactorDivisibility.instanceParams
                    return leftFactorDivisibility.instantiate(
                            {_x:self.lhs, _y:self.rhs.operands[1]},
                            assumptions=assumptions)
                elif self.lhs == self.rhs.operands[1]:
                    # apply right version
                    from ._theorems_ import rightFactorDivisibility
                    _x, _y = rightFactorDivisibility.instanceParams
                    return rightFactorDivisibility.instantiate(
                            {_x:self.lhs, _y:self.rhs.operands[0]},
                            assumptions=assumptions)
                else:
                    raise ValueError(
                        "concludeViaFactor only applies for an explicit "
                        "factor appearing on both sides of the Divides. "
                        "{0} does not appear in {1} as an explicit factor.".
                        format(self.lhs, self.rhs))
            else:
                raise NotImplementedError(
                    "concludeViaFactor implemented only for binary "
                    "multiplication.")
        else:
            raise ValueError(
                    "concludeViaFactor only applies for an explicit "
                    "Mult expression on the rhs of the Divides, "
                    "but received {0} on the right side.".
                    format(self.rhs))


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
          stringFormat='|', latexFormat=r'{\rvert_{P}}', context=__file__
          )

    # map left-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to "Divides" KnownTruths
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()

    def __init__(self, a, b):
        DividesRelation.__init__(self, DividesProper._operator_, a, b)

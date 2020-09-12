from proveit import (asExpression, Context, defaults, Literal, Operation,
                     ProofFailure, TransitiveRelation, USE_DEFAULTS)
from proveit.logic import Equals, InSet, NotEquals
from proveit.number import Exp, Mult, num
from proveit.number import zero, Complexes, Integers, NaturalsPos

class DividesRelation(TransitiveRelation):

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)

    def sideEffects(self, knownTruth):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt (where applicable) eliminateDividenExponent,
        eliminate_common_exponent, and eliminate_common_factor.
        '''
        for sideEffect in TransitiveRelation.sideEffects(self, knownTruth):
            yield sideEffect
        
        # For each of the following, use the default assumptions to
        # verify some conditions before yielding the side effect method
        # (i.e. check using .proven() without arguments)

        # for a|(b^n)
        if (isinstance(self.rhs, Exp) and
            InSet(self.lhs, Integers).proven() and
            InSet(self.rhs.base, Integers).proven() and
            InSet(self.rhs.exponent, Integers).proven()):
            yield self.eliminateDividendExponent

        # for (a^n)|(b^n)
        if (isinstance(self.lhs, Exp) and isinstance(self.rhs, Exp) and
            InSet(self.lhs.base, Integers).proven() and
            InSet(self.rhs.base, Integers).proven() and
            Equals(self.lhs.exponent, self.rhs.exponent).proven() and
            InSet(self.lhs.exponent, NaturalsPos).proven()):
            yield self.eliminate_common_exponent

        # for (ka)|(kb)
        if (isinstance(self.lhs, Mult) and len(self.lhs.operands)==2 and
            isinstance(self.rhs, Mult) and len(self.rhs.operands)==2):
            operands_intersection = (set(self.lhs.operands).
                                     intersection(set(self.lhs.operands)))
            if(len(operands_intersection)>0):
                yield self.eliminate_common_factor

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
        (4) x^n | y^n if x|y is known or assumed
        (5) x|y if (x^n)|(y^n) is known or assumed
        (6) via transitivity.
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
        #-- Case (4): x^n|y^n if x|y                                 --#
        #-- -------------------------------------------------------- --#
        if (isinstance(self.lhs, Exp) and isinstance(self.rhs, Exp)):
            if (InSet(self.lhs.base, Integers).proven(assumptions) and
                InSet(self.rhs.base, Integers).proven(assumptions) and
                Equals(self.lhs.exponent, self.rhs.exponent) and
                InSet(self.lhs.exponent, NaturalsPos).proven(assumptions) and
                Divides(self.lhs.base, self.rhs.base).proven(assumptions)):

                return (Divides(self.lhs.base, self.rhs.base).
                            introduce_common_exponent(
                                self.lhs.exponent, assumptions=assumptions))

            else:
                err_str = err_str + (
                        "Case: (x^n) | (y^n). One or more of the conditions "
                        "(such as domain requirements or x|y) were not "
                        "already proven. Check the conditions for the "
                        "common_exponent_introduction theorem in the "
                        "number/divisibility package.\n")

        else:
            err_str = err_str + (
                    "Case: (x^n) | (y^n). Does not appear applicable.\n")
        #-- -------------------------------------------------------- --#
        #-- Case (5): x|y if x^n|y^n (for some small pos nat n)      --#
        #-- -------------------------------------------------------- --#
        possible_exps = range(2,10)
        for e in possible_exps:
            # print("exp = {}".format(e))
            if (Divides(Exp(self.lhs, num(e)), Exp(self.rhs, num(e))).
                proven(assumptions)):
                # print("    Divides found for exp = {}".format(test_exp))
                return (Divides(Exp(self.lhs, test_exp),
                                Exp(self.rhs, test_exp)).
                        eliminate_common_exponent(assumptions=assumptions))

        err_str = err_str + (
                "Case: x|y where we already have (x^n)|(y^n). "
                "Does not appear applicable.\n")

        #-- -------------------------------------------------------- --#
        #-- Case (6): x|z with x|y and y|z known or assumed          --#
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

    def eliminateDividendExponent(self, assumptions=USE_DEFAULTS):
        '''
        From k|a^n (self), derive and return k|a. k, a, and n must all
        be integers. This method is called from the DividesRelation
        sideEffects() method.
        '''
        from ._theorems_ import divides_if_divides_power
        k_, a_, n_ = divides_if_divides_power.instanceParams
        return divides_if_divides_power.instantiate(
            {k_:self.lhs, a_:self.rhs.base, n_:self.rhs.exponent},
            assumptions=assumptions)

    def eliminate_common_exponent(self, assumptions=USE_DEFAULTS):
        '''
        From self of the form (k^n)|(a^n), derive and return k|a.
        k, a, must be integers, with n a positive integer. This method
        is called from the DividesRelation sideEffects() method.
        '''
        if (isinstance(self.lhs, Exp) and
            isinstance(self.rhs, Exp) and
            self.lhs.exponent == self.rhs.exponent):

            k = self.lhs.base
            a = self.rhs.base
            n = self.lhs.exponent

            if (InSet(k, Integers).proven(assumptions) and 
                InSet(a, Integers).proven(assumptions) and
                InSet(n, NaturalsPos).proven(assumptions)):

                from ._theorems_ import common_exponent_elimination
                _k, _a, _n = common_exponent_elimination.instanceParams
                return common_exponent_elimination.instantiate(
                        {_k:k, _a:a, _n:n}, assumptions=assumptions)
            else:
                err_msg = ("In using Divides.eliminate_common_exponent(), "
                           "the exponent ({0}) must already be known to be "
                           "a positive natural and each base ({1}, {2}) "
                           "must already been know to be an integer.".
                           format(n, k, a))
        else:
            err_msg = ("In using Divides.eliminate_common_exponent(), "
                       "the lhs {0} and rhs {1} must both be exponential.".
                       format(self.lhs, self.rhs))

        raise ValueError(err_msg)

    def introduce_common_exponent(self, exponent, assumptions=USE_DEFAULTS):
        '''
        From self of the form (k)|(a), with integers k and a, derive
        and return k^n|a^n where n = exponent is a positive natural.
        '''
        from ._theorems_ import common_exponent_introduction
        _k, _a, _n = common_exponent_introduction.instanceParams
        return common_exponent_introduction.instantiate(
                        {_k:self.lhs, _a:self.rhs, _n:exponent},
                        assumptions=assumptions)

    def eliminate_common_factor(self, assumptions=USE_DEFAULTS):
        '''
        From self of the form (k a)|(k b), derive and return a|b.
        k must be a non-zero complex number. This method
        is called from the DividesRelation sideEffects() method.
        Need to generalize this later for more than two operands on
        each side! Could use sets for detecting common factors.
        '''
        if (isinstance(self.lhs, Mult) and
            isinstance(self.rhs, Mult)):

            if (len(self.lhs.operands)==2 and
                len(self.rhs.operands)==2):

                lhs1 = self.lhs.operands[0]
                lhs2 = self.lhs.operands[1]
                rhs1 = self.rhs.operands[0]
                rhs2 = self.rhs.operands[1]

                if (lhs1 == rhs1 and InSet(lhs1, Complexes).proven() and
                    NotEquals(lhs1, zero).proven()):

                    from ._theorems_ import common_factor_elimination
                    from proveit._common_ import a, b, k
                    return common_factor_elimination.instantiate(
                        {a: lhs2, b: rhs2, k:lhs1 }, assumptions=assumptions)

                else:
                    err_msg = ("Error!")

            else:
                err_msg = ("In using Divides.eliminate_common_factor(), "
                           "each product can have only two multiplicands.")
        else:
            err_msg = ("In using Divides.eliminate_common_factor(), "
                       "the lhs {0} and rhs {1} must both be products.".
                       format(self.lhs, self.rhs))

        raise ValueError(err_msg)


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

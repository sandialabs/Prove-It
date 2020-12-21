from proveit import (as_expression, Theory, defaults, Literal, Operation,
                     ProofFailure, TransitiveRelation, USE_DEFAULTS)
from proveit.logic import Equals, InSet, NotEquals
from proveit.numbers import Exp, Mult, num
from proveit.numbers import zero, Complex, Integer, NaturalPos


class DividesRelation(TransitiveRelation):

    def __init__(self, operator, lhs, rhs):
        TransitiveRelation.__init__(self, operator, lhs, rhs)
        self.divisor = self.lhs
        self.dividend = self.rhs

    def side_effects(self, judgment):
        '''
        In addition to the TransitiveRelation side-effects, also
        attempt (where applicable) eliminate_dividen_exponent,
        eliminate_common_exponent, and eliminate_common_factor.
        '''
        from proveit.numbers import two

        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect

        # For each of the following, use the default assumptions to
        # verify some conditions before yielding the side effect method
        # (i.e. check using .proven() without arguments)

        # for 2|(b^n), derive 2|b.
        # (can be generalized to any prime number).
        if (isinstance(self.rhs, Exp) and
                self.lhs == two and
                InSet(self.rhs.base, Integer).proven() and
                InSet(self.rhs.exponent, Integer).proven()):
            yield self.eliminate_dividend_exponent

        # for (a^n)|(b^n)
        if (isinstance(self.lhs, Exp) and isinstance(self.rhs, Exp) and
                InSet(self.lhs.base, Integer).proven() and
                InSet(self.rhs.base, Integer).proven() and
                self.lhs.exponent == self.rhs.exponent and
                InSet(self.lhs.exponent, NaturalPos).proven()):
            yield self.eliminate_common_exponent

        # for (ka)|(kb)
        if (isinstance(self.lhs, Mult) and len(self.lhs.operands) == 2 and
                isinstance(self.rhs, Mult) and len(self.rhs.operands) == 2):
            operands_intersection = (set(self.lhs.operands).
                                     intersection(set(self.lhs.operands)))
            if(len(operands_intersection) > 0):
                yield self.eliminate_common_factor

    @staticmethod
    def WeakRelationClass():
        # Divides is weaker than DividesProper (in development)
        # analogous to <= being weaker than <
        return Divides  # Divides is weaker than DividesProper

    @staticmethod
    def StrongRelationClass():
        # DividesProper (in development) is stronger than Divides.
        # DividesProper(x, y) is like Divides(x, y) but requires x != y
        return DividesProper  # DividesProper is stronger than Divides


class Divides(DividesRelation):
    '''
    Divides(x, y) represents the claim that x divides y (i.e. x|y)
    (equivalently, x is a factor of y, y is a multiple of x, or
    y/x is an integer). The axiomatic definition in Prove-It uses
    x|y = (y/x in Z), with no prerequisites on x and y. Extending
    DividesRelation allows us to have not only this weak relation
    class but also a strong relation class, DividesProper, the pair
    combined then allowing the calling of
    Divides.conclude_via_transitivity()
    utilizing the TransitiveRelation.conclude_via_transitivity() method.
    '''

    _operator_ = Literal(
        string_format='|', latex_format=r'\rvert', theory=__file__
    )

    # map left-hand-sides to "Divides" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to "Divides" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

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
        assumptions = defaults.checked_assumptions(assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (1): x|x with x != 0 known or assumed               --#
        #-- -------------------------------------------------------- --#
        from proveit.logic import InSet, NotEquals
        from proveit.numbers import zero, Complex
        err_str = "In Divides.conclude() we tried:\n"
        if self.lhs == self.rhs:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                    InSet(self.lhs, Complex).proven(assumptions=assumptions)):
                # Trivial x|x with complex x ≠ 0
                return self.conclude_via_reflexivity(assumptions)
            else:
                err_str = err_str + (
                    "Case: lhs = rhs. "
                    "Although lhs = rhs = {0}, either {0} is not known to "
                    "be non-zero or {0} is not known to be in the complex "
                    "numbers (or both). Try proving one or both of those "
                    "claims first.\n".format(self.lhs))
                # raise ProofFailure(self, assumptions, err_str)

        #-- -------------------------------------------------------- --#
        #-- Case (2): x|0 with x != 0 known or assumed               --#
        #-- -------------------------------------------------------- --#
        if self.rhs == zero:
            if (NotEquals(self.lhs, zero).proven(assumptions=assumptions) and
                    InSet(self.lhs, Complex).proven(assumptions=assumptions)):
                # We have 0/x with complex x ≠ 0
                return self.conclude_via_zero_factor(assumptions)
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
        # return self.conclude_via_factor(assumptions)
        try:
            return self.conclude_via_factor(assumptions)
        except Exception as e:
            err_str = err_str + (
                "Case: x|xy. This possible case returned the following "
                "error message: {0} \n".format(e))
            pass

        #-- -------------------------------------------------------- --#
        #-- Case (4): x^n|y^n if x|y                                 --#
        #-- -------------------------------------------------------- --#
        if (isinstance(self.lhs, Exp) and isinstance(self.rhs, Exp)):
            if (InSet(self.lhs.base, Integer).proven(assumptions) and
                InSet(self.rhs.base, Integer).proven(assumptions) and
                Equals(self.lhs.exponent, self.rhs.exponent) and
                InSet(self.lhs.exponent, NaturalPos).proven(assumptions) and
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

        """
        # This case should be handled on the "side-effect" end.

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
        """

        #-- -------------------------------------------------------- --#
        #-- Case (6): x|z with x|y and y|z known or assumed          --#
        #-- -------------------------------------------------------- --#
        # Seek out the appropriate x|y and y|z and use transitivity
        # to get x|z, utilizing the conclude_via_transitivity() method
        # available for instances of TransitiveRelation
        try:
            return self.conclude_via_transitivity(assumptions)
        except Exception as e:
            err_str = err_str + (
                "Case: transitivity search. In attempting to use "
                "conclude_via_transitivity(), obtained the following "
                "error message: {0}.".format(e))
            pass

        raise ProofFailure(self, assumptions, err_str)

    def conclude_via_reflexivity(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x|x with x ≠ 0.
        '''
        from ._theorems_ import divides_reflexivity
        _x = divides_reflexivity.instance_var
        assert self.lhs == self.rhs
        return divides_reflexivity.instantiate(
            {_x: self.lhs}, assumptions=assumptions)

    def conclude_via_zero_factor(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x|0 for x ≠ 0
        '''
        from ._theorems_ import non_zero_divides_zero
        _x = non_zero_divides_zero.instance_var
        return non_zero_divides_zero.instantiate(
            {_x: self.lhs}, assumptions=assumptions)

    def conclude_via_factor(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x|xy for x ≠ 0 and y in Ints
        '''
        from proveit.numbers import Mult
        if isinstance(self.rhs, Mult):
            if len(self.rhs.operands) == 2:
                # should check to make sure none of the operands
                # are actually ExprRanges (later!)
                if self.lhs == self.rhs.operands[0]:
                    # apply left version
                    from ._theorems_ import left_factor_divisibility
                    _x, _y = left_factor_divisibility.instance_params
                    return left_factor_divisibility.instantiate(
                        {_x: self.lhs, _y: self.rhs.operands[1]},
                        assumptions=assumptions)
                elif self.lhs == self.rhs.operands[1]:
                    # apply right version
                    from ._theorems_ import right_factor_divisibility
                    _x, _y = right_factor_divisibility.instance_params
                    return right_factor_divisibility.instantiate(
                        {_x: self.lhs, _y: self.rhs.operands[0]},
                        assumptions=assumptions)
                else:
                    raise ValueError(
                        "conclude_via_factor only applies for an explicit "
                        "factor appearing on both sides of the Divides. "
                        "{0} does not appear in {1} as an explicit factor.".
                        format(self.lhs, self.rhs))
            else:
                raise NotImplementedError(
                    "conclude_via_factor implemented only for binary "
                    "multiplication.")
        else:
            raise ValueError(
                "conclude_via_factor only applies for an explicit "
                "Mult expression on the rhs of the Divides, "
                "but received {0} on the right side.".
                format(self.rhs))

    def eliminate_dividend_exponent(self, assumptions=USE_DEFAULTS):
        '''
        From k|a^n (self), derive and return k|a if k is prime
        and a and n are integers.  Currently, this is only implement
        for k=2.  This method is called from the
        DividesRelation.side_effects() method.
        '''
        from proveit.numbers import two
        from ._theorems_ import even__if__power_is_even
        if not isinstance(self.rhs, Exp):
            raise ValueError(
                "'eliminate_dividend_exponent' is only applicable "
                "when the dividend is raised to an integer power.")
        if self.lhs != two:
            raise NotImplementedError(
                "'eliminate_dividend_exponent' currently only implemented "
                "for a divisor of 2, but should eventually be "
                "generalized for any prime divisor.")
        a_, n_ = even__if__power_is_even.instance_params
        return even__if__power_is_even.instantiate(
            {a_: self.rhs.base, n_: self.rhs.exponent},
            assumptions=assumptions)

    def eliminate_common_exponent(self, assumptions=USE_DEFAULTS):
        '''
        From self of the form (k^n)|(a^n), derive and return k|a.
        k, a, must be integers, with n a positive integer. This method
        is called from the DividesRelation side_effects() method.
        '''
        if (isinstance(self.lhs, Exp) and
            isinstance(self.rhs, Exp) and
                self.lhs.exponent == self.rhs.exponent):

            k = self.lhs.base
            a = self.rhs.base
            n = self.lhs.exponent

            if (InSet(k, Integer).proven(assumptions) and
                InSet(a, Integer).proven(assumptions) and
                    InSet(n, NaturalPos).proven(assumptions)):

                from ._theorems_ import common_exponent_elimination
                _k, _a, _n = common_exponent_elimination.instance_params
                return common_exponent_elimination.instantiate(
                    {_k: k, _a: a, _n: n}, assumptions=assumptions)
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
        _k, _a, _n = common_exponent_introduction.instance_params
        return common_exponent_introduction.instantiate(
            {_k: self.lhs, _a: self.rhs, _n: exponent},
            assumptions=assumptions)

    def eliminate_common_factor(self, assumptions=USE_DEFAULTS):
        '''
        From self of the form (k a)|(k b), derive and return a|b.
        k must be a non-zero complex number. This method
        is called from the DividesRelation side_effects() method.
        Need to generalize this later for more than two operands on
        each side! Could use sets for detecting common factors.
        '''
        if (isinstance(self.lhs, Mult) and
                isinstance(self.rhs, Mult)):

            if (len(self.lhs.operands) == 2 and
                    len(self.rhs.operands) == 2):

                lhs1 = self.lhs.operands[0]
                lhs2 = self.lhs.operands[1]
                rhs1 = self.rhs.operands[0]
                rhs2 = self.rhs.operands[1]

                if (lhs1 == rhs1 and InSet(lhs1, Complex).proven() and
                        NotEquals(lhs1, zero).proven()):

                    from ._theorems_ import common_factor_elimination
                    from proveit._common_ import a, b, k
                    return common_factor_elimination.instantiate(
                        {a: lhs2, b: rhs2, k: lhs1}, assumptions=assumptions)

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

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From x|y (self) and y|z (other) derive and return x|z.
        Will also check for y|z (self) and x|y (other) to return x|z.
        '''
        from ._theorems_ import divides_transitivity
        _x, _y, _z = divides_transitivity.instance_params
        other = as_expression(other)
        if not isinstance(other, Divides):
            raise ValueError(
                "Unsupported transitivity operand: Divides.apply_transitivity() "
                "method requires another Divides expression for transitivity "
                "to be applied. Instead, received the following input: {0}.". format(other))

        if self.rhs == other.lhs:
            return divides_transitivity.instantiate(
                {_x: self.lhs, _y: self.rhs, _z: other.rhs},
                assumptions=assumptions)
        if self.lhs == other.rhs:
            return divides_transitivity.instantiate(
                {_x: other.lhs, _y: other.rhs, _z: self.rhs},
                assumptions=assumptions)
        else:
            raise TransitivityException(
                self, assumptions,
                'Transitivity cannot be applied unless the lhs of one of '
                'Divides expressions is equal to the rhs of the other '
                'Divides expression. Instead we have: {0} vs {1}'.
                format(self, other))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'Divides' expression is in
        the Boolean set.
        '''
        from ._theorems_ import divides_is_bool
        _x, _y = divides_is_bool.instance_params
        return divides_is_bool.instantiate(
            {_x: self.operands[0], _y: self.operands[1]},
            assumptions=assumptions)


class DividesProper(DividesRelation):
    '''
    DividesProper(x, y) represents the claim that x divides y
    (i.e. x|y) but x != y. x|y is equivalent to saying that x is a
    factor of y, y is a multiple of x, or y/x is an integer).
    This class is still under development, with the class stub located
    here so that we have a 'strong relation' class version of Divides
    that can be called from the DividesRelation class, which in turn
    allows us to use the TransitiveRelation.concude_via_transitivity()
    method.
    '''

    _operator_ = Literal(
        string_format='|', latex_format=r'{\rvert_{P}}', theory=__file__
    )

    # map left-hand-sides to "Divides" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to "Divides" Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

    def __init__(self, a, b):
        DividesRelation.__init__(self, DividesProper._operator_, a, b)

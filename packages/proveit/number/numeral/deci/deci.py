from proveit import Literal, USE_DEFAULTS, Operation, ExprRange
from proveit._common_ import a, b, c, d, k, m, n, x
from proveit.number.sets.number_set import NumberSet, NumberMembership
from proveit.number.numeral.numeral import NumeralSequence, Numeral
from proveit.number.numeral._common_ import zero, one, two, three, four, five, six, seven, eight, nine
DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

class DecimalSequence(NumeralSequence):
    # operator of the WholeDecimal operation.
    _operator_ = Literal(stringFormat='Decimal',context=__file__)   

    def __init__(self, *digits):
        NumeralSequence.__init__(self, DecimalSequence._operator_, *digits)
        for digit in self.digits:
            if isinstance(digit, Literal) and digit not in DIGITS:
                raise Exception('A DecimalSequence may only be composed of 0-9 digits')

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        """
        Tries to reduce each value in the Numeral Sequence to a single digit
        """
        from proveit import ExprRange
        from proveit.number import Add
        for digit in self.digits:
            if isinstance(digit, Add):
                # if at least one digit is an addition object, we can use the evaluate_add_digit method
                return self.evaluate_add_digit(assumptions=assumptions)
            if isinstance(digit, ExprRange):
                # if at least one digit is an ExprRange, we can try to reduce it to an ExprTuple
               # return self.reduce_exprRange(assumptions=assumptions)
                pass
    
    def asInt(self):
        return int(self.formatted('string'))

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        from proveit.number import Naturals, NaturalsPos
        from proveit.logic import InSet
        if number_set == Naturals:
            return self.deduceInNaturals(assumptions)
        elif number_set == NaturalsPos:
            return self.deduceInNaturalsPos(assumptions)
        else:
            try:
                # Do this to avoid infinite recursion -- if
                # we already know this numeral is in NaturalsPos
                # we should know how to prove that it is in any
                # number set that contains the naturals.
                if self.asInt() > 0:
                    InSet(self, NaturalsPos).prove(automation=False)
                else:
                    InSet(self, Naturals).prove(automation=False)
            except:
                # Try to prove that it is in the given number
                # set after proving that the numeral is in
                # Naturals and NaturalsPos.
                self.deduceInNaturals()
                if self.asInt() > 0:
                    self.deduceInNaturalsPos()
            #return InSet(self, number_set).conclude(assumptions)

    def deduceInNaturals(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import deci_sequence_in_naturals
        return deci_sequence_in_naturals.instantiate({n: self.operands.length(assumptions),
                                                      a: self.digits}, assumptions=assumptions)
        # if Numeral._inNaturalsStmts is None:
        #     from proveit.number.sets.integer._theorems_ import zeroInNats
        #     from proveit.number.numeral.deci._theorems_ import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
        #     Numeral._inNaturalsStmts = {0: zeroInNats, 1: nat1, 2: nat2, 3: nat3, 4: nat4, 5: nat5, 6: nat6, 7: nat7,
        #                                 8: nat8, 9: nat9}
        # return Numeral._inNaturalsStmts[self.n]

    def deduceInNaturalsPos(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import deci_sequence_in_naturalsPos
        return deci_sequence_in_naturalsPos.instantiate({n: self.operands.length(assumptions),
                                                         a: self.digits}, assumptions=assumptions)
        # from proveit import ProofFailure
        # if Numeral._inNaturalsPosStmts is None:
        #     from proveit.number.numeral.deci._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5
        #     from proveit.number.numeral.deci._theorems_ import posnat6, posnat7, posnat8, posnat9
        #     Numeral._inNaturalsPosStmts = {1: posnat1, 2: posnat2, 3: posnat3, 4: posnat4, 5: posnat5, 6: posnat6,
        #                                    7: posnat7, 8: posnat8, 9: posnat9}
        # if self.n <= 0:
        #     raise ProofFailure(self, [],
        #                        "Cannot prove %d in NaturalsPos" % self.n)
        # return Numeral._inNaturalsPosStmts[self.n]

    def reduce_exprRange(self, assumptions=USE_DEFAULTS):
        '''
        Tries to reduce a decimal sequence containing an ExprRange.
        For example, reduce #(3 4 2 .. 4 repeats .. 2 3) to 3422223
        '''
        from proveit import TransRelUpdater
        from proveit.core_expr_types.tuples._theorems_ import n_repeats_reduction
        from proveit.number.numeral.deci._theorems_ import deci_sequence_reduction_ER

        expr = self
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        for i, digit in enumerate(self.digits):
            if isinstance(digit, ExprRange) and isinstance(digit.body, Numeral):
                import proveit.number.numeral.deci

                _m = expr.digits[:i].length(assumptions)
                _n = digit.end_index
                _k = expr.digits[i + 1:].length(assumptions)
                _a = expr.digits[:i]
                _b = digit.body
                _d = expr.digits[i + 1:]

                #if digit.end_index.asInt() >= 10:
                    # Automatically reduce an Expression range of
                    # a single numeral to an Expression tuple
                    # (3 .. 4 repeats.. 3) = 3333
                    # #(2 3 4 (5 ..3 repeats.. 5) 6 7 8) = 234555678

                while _n.asInt() > 9:
                    _x = digit.body

                    _c = n_repeats_reduction.instantiate({n: _n, x: _x}, assumptions=assumptions).rhs

                    eq.update(deci_sequence_reduction_ER.instantiate({m: _m, n: _n, k: _k, a: _a, b: _b, c: _c,
                                                                      d: _d}, assumptions=assumptions))
                    _n = num(_n.asInt() - 1)

                #_n = digit.end_index
                len_thm = proveit.number.numeral.deci._theorems_ \
                    .__getattr__('reduce_%s_repeats' % _n)
                _x = digit.body

                _c = len_thm.instantiate({x: _x}, assumptions=assumptions).rhs

                eq.update(deci_sequence_reduction_ER.instantiate({m: _m, n: _n, k: _k, a: _a, b: _b, c: _c,
                                                                             d: _d}, assumptions=assumptions))

        return eq.relation

    def numAddEval(self, num2, assumptions=USE_DEFAULTS):
        '''
        evaluates the addition of two integers
        '''
        from ._theorems_ import md_only_nine_add_one, md_nine_add_one
        num1 = self
        if isinstance(num2, int):
            num2 = num(num2)
        if num2 == one:
            # if the second number (num2) is one, we set it equal to the first number and then assume the
            # first number to be one and the second number to not be one.  SHOULD BE DELETED once addition works
            # for numbers greater than one.
            num2 = num1
        elif num2 != one:
            raise NotImplementedError(
                    "Currently, numAddEval only works for the addition of Decimal "
                    "Sequences and one, not %s, %s" % (str(num1), str(num2)))
        if all(digit == nine for digit in num2.digits):
            # every digit is 9
            return md_only_nine_add_one.specialize({k: num2.digits.length(assumptions)}, assumptions=assumptions)
        elif num2.digits[-1] == nine:
            # the last digit is nine
            from proveit.number import Add
            count = 0
            idx = -1
            while num2.digits[idx] == nine or \
                    (isinstance(num2.digits[idx], ExprRange) and num2.digits[idx].body == nine):
                if isinstance(num2.digits[idx], ExprRange):
                    count += num2.digits[idx].end_index
                else:
                    count += 1
                idx -= 1
            length = num2.digits.length(assumptions)
            _m = num(length - count - 1)
            _k = num(count)
            _a = num2.digits[:-(count + 1)]
            _b = num2.digits[-(count + 1)]
            return md_nine_add_one.specialize({m: _m, k: _k, a: _a, b: _b}, assumptions=assumptions)
        else:
            # the last digit is not nine
            _m = num2.digits.length(assumptions)
            _k = num(0)
            _a = num2.digits[:-1]
            _b = num2.digits[-1]
        eq = md_nine_add_one.specialize({m: _m, k: _k, a: _a, b: _b}, assumptions=assumptions)
        return eq.innerExpr().rhs.operands[-1].evaluate(assumptions=assumptions)

    def evaluate_add_digit(self, assumptions=USE_DEFAULTS):
        """
        Evaluates each addition within the DecimalSequence
        """
        from proveit import TransRelUpdater
        from proveit.number import Add
        from ._theorems_ import deci_sequence_reduction

        expr = self
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        for i, digit in enumerate(self.digits):
            if isinstance(digit, Add):
                # only implemented for addition.

                _m = expr.digits[:i].length(assumptions=assumptions)
                _n = digit.operands.length(assumptions=assumptions)
                _k = expr.digits[i + 1:].length(assumptions=assumptions)
                # _a = expr.innerExpr().operands[:i]
                _b = digit.operands
                _c = digit.evaluation(assumptions=assumptions).rhs
                # _d = expr.innerExpr().operands[i + 1:]

                _a = expr.digits[:i]
                _d = expr.digits[i + 1:]

                expr = eq.update(deci_sequence_reduction.instantiate({m: _m, n: _n, k: _k, a: _a, b: _b, c: _c,
                                                                      d: _d}, assumptions=assumptions))
        return eq.relation

    def _formatted(self, formatType, operator=None, **kwargs):
        from proveit import ExprRange, varRange
        outstr = ''
        fence = False
        if operator is None:
            operator = ' ~ '
        if not all(isinstance(digit, Numeral) for digit in self.digits):
            outstr += r'\# ('
            fence = True
        for i, digit in enumerate(self.digits):
            if i != 0 and fence:
                add = operator
            else:
                add = ''
            if isinstance(digit, Operation):
                outstr += add + digit.formatted(formatType, fence=True)
            elif isinstance(digit, ExprRange):
                outstr += add + digit.formatted(formatType, operator=operator)
            else:
                outstr += add + digit.formatted(formatType)
        if fence:
            outstr += r')'
        return outstr


class DigitSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Digits', r'\mathbb{N}^{\leq 9}', context=__file__)

    def deduceMemberLowerBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import digitsLowerBound
        return digitsLowerBound.specialize({n: member}, assumptions=assumptions)

    def deduceMemberUpperBound(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import digitsUpperBound
        return digitsUpperBound.specialize({n: member}, assumptions=assumptions)

    def membershipSideEffects(self, knownTruth):
        '''
        Yield side-effects when proving 'n in Naturals' for a given n.
        '''
        member = knownTruth.element
        yield lambda assumptions: self.deduceMemberLowerBound(member, assumptions)
        yield lambda assumptions: self.deduceMemberUpperBound(member, assumptions)

    def membershipObject(self, element):
        return DeciMembership(element, self)


class DeciMembership(NumberMembership):
    '''
        Defines methods that apply to membership of a decimal sequence.
    '''
    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from ._theorems_ import nInDigits
        # if we know the element is 0-9, then we can show it is a digit
        try:
            return NumberMembership.conclude(self, assumptions=assumptions)
        except ProofFailure:
            return nInDigits.instantiate({n: self.element}, assumptions=assumptions)

        # if isinstance(self.element, numeral) and 0 <= self.element.asInt() <= 9:
        #     _n = self.element.asInt()
        #     thm = proveit.number.numeral.deci._theorems_ \
        #         .__getattr__('digit%s' % _n)
        #     return thm
        # else:
        #     return nInDigits.instantiate({n: self.element}, assumptions=assumptions)




def num(x):
    from proveit.number import Neg
    if x < 0:
        return Neg(num(abs(x)))
    if isinstance(x, int):
        if x < 10:
            if x == 0:
                return zero
            elif x == 1:
                return one
            elif x == 2:
                return two
            elif x == 3:
                return three
            elif x == 4:
                return four
            elif x == 5:
                return five
            elif x == 6:
                return six
            elif x == 7:
                return seven
            elif x == 8:
                return eight
            elif x == 9:
                return nine
        else:
            return DecimalSequence(*[num(int(digit)) for digit in str(x)])
    else:
        assert False, 'num not implemented for anything except integers currently. plans to take in strings or floats with specified precision'

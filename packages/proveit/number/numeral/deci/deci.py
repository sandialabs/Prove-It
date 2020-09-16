from proveit import Literal, USE_DEFAULTS, Operation
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
        from proveit.number import Add
        for digit in self.digits:
            if isinstance(digit, Add):
                # if at least one digit is an addition object, we can use the evaluate_add_digit method
                return self.evaluate_add_digit(assumptions=assumptions)
    
    def asInt(self):
        return int(self.formatted('string'))


    def numAddEval(self, num2, assumptions=USE_DEFAULTS):
        '''
        evaluates the addition of two integers
        '''
        from proveit._common_ import a, b, k, m
        from ._theorems_ import md_only_nine_add_one, md_nine_add_one
        num1 = self
        num2 = num(num2)
        if num2 is one:
            # if the second number (num2) is one, we set it equal to the first number and then assume the
            # first number to be one and the second number to not be one.  SHOULD BE DELETED once addition works
            # for numbers greater than one.
            num2 = num1
        elif num2 is not one:
            raise NotImplementedError(
                    "Currently, numAddEval only works for the addition of Decimal "
                    "Sequences and one, not %s, %s" % (str(num1), str(num2)))
        if all(digit is nine for digit in num2.digits):
            # every digit is 9
            return md_only_nine_add_one.specialize({k: num(len(num2.digits))}, assumptions=assumptions)
        elif num2.digits[-1] is nine:
            # the last digit is nine
            count = 0
            idx = -1
            while num2.digits[idx] is nine:
                count += 1
                idx -= 1
            length = len(num2.digits)
            _m = num(length - count - 1)
            _k = num(count)
            _a = num2.digits[:-(count + 1)]
            _b = num2.digits[-(count + 1)]
        else:
            # the last digit is not nine
            _m = num(len(num2.digits) - 1)
            _k = num(0)
            _a = num2.digits[:-1]
            _b = num2.digits[-1]
        eq = md_nine_add_one.specialize({m: _m, k: _k, a: _a, b: _b}, assumptions=assumptions)
        return eq.innerExpr().rhs.operands[-1].evaluate(assumptions=assumptions)

    def evaluate_add_digit(self, assumptions=USE_DEFAULTS):
        """
        Evaluates each addition within the DecimalSequence
        """
        from proveit import ExprRange
        from proveit.number import Add
        from proveit._common_ import a, b, c, d, k, m, n
        from ._theorems_ import deci_sequence_reduction
        current = self
        for i, digit in enumerate(self.digits):
            if isinstance(digit, Literal) or isinstance(digit, ExprRange):
                pass
            elif isinstance(digit, Add):
                # only implemented for addition.
                if current == self:
                    _m = num(i)
                    _n = num(len(digit.operands))
                    _k = num(len(self.digits) - i - 1)
                    _a = self.digits[:i]
                    _b = digit.operands
                    _c = digit.evaluation(assumptions=assumptions).rhs
                    _d = self.digits[i + 1:]
                else:
                    _m = num(i)
                    _n = num(len(digit.operands))
                    _k = num(len(self.digits) - i - 1)
                    _a = current.innerExpr().rhs.operands[:i]
                    _b = digit.operands
                    _c = digit.evaluation(assumptions=assumptions).rhs
                    _d = current.innerExpr().rhs.operands[i + 1:]

                current = deci_sequence_reduction.instantiate({m: _m, n: _n, k: _k, a: _a, b: _b, c: _c, d: _d},
                                                              assumptions=assumptions)
        return current

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

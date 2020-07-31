from proveit import Literal, USE_DEFAULTS
from proveit.number.numeral.numeral import NumeralSequence
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
    
    def asInt(self):
        return int(self.formatted('string'))

    @staticmethod
    def numAddEval(num1, num2, assumptions=USE_DEFAULTS):
        '''
        evaluates the addition of two integers
        '''
        from proveit._common_ import a, b, k, m
        from ._theorems_ import md_only_nine_add_one, md_nine_add_one
        num1 = num(num1)
        num2 = num(num2)
        if num2 is one:
            num2 = num1
        elif num2 is not one:
            raise NotImplementedError(
                    "Currently, numAddEval only works for the addition of Decimal "
                    "Sequences and one, not %d, %d"%(num1, num2))
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
        return md_nine_add_one.specialize({m: _m, k: _k, a: _a, b: _b}, assumptions=assumptions)



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

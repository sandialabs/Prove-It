from proveit import Literal, Operation
from proveit.number.numeral.numeral import NumeralSequence
from proveit.number.numeral._common_ import zero, one, two, three, four, five, six, seven, eight, nine
DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

class DecimalSequence(NumeralSequence):
    # operator of the WholeDecimal operation.
    _operator_ = Literal(stringFormat='Decimal',context=__file__)   

    def __init__(self, *digits):
        NumeralSequence.__init__(self, DecimalSequence._operator_, *digits)
        if not all(digit in DIGITS for digit in self.digits):
            raise Exception('A DecimalSequence may only be composed of 0-9 digits')
    
    def asInt(self):
        return int(self.formatted('string'))
        

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

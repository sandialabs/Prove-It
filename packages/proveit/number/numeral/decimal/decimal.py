from proveit import Literal, Operation
from proveit.number.numeral._common_ import zero, one, two, three, four, five, six, seven, eight, nine
ALL_DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

class WholeDecimal(Operation):
    # operator of the WholeDecimal operation.
    _operator_ = Literal(stringFormat='WholeDecimal',context=__file__)   

    def __init__(self, digits):
        Operation.__init__(self, WholeDecimal._operator_, digits)
        if len(digits) <= 1:
            raise Exception('A WholeDecimal should have two or more digits.  Single digit number should be represented as the corresponding Literal.')
        self.digits = digits
        if not all(digit in ALL_DIGITS for digit in self.digits):
            raise Exception('A WholeDecimal may only be composed of 0-9 digits')
    
    def asInt(self):
        return int(self.formatted('string'))
    
    def _formatted(self, formatType, **kwargs):
        return ''.join(digit.formatted(formatType) for digit in self.digits)
        

def num(x):
    from proveit.number import Neg, WholeDecimal
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
            return WholeDecimal([num(int(digit)) for digit in str(x)])
    else:
        assert False, 'num not implemented for anything except integers currently. plans to take in strings or floats with specified precision'

def isLiteralInt(expr):
    from proveit.number import Neg
    if expr in ALL_DIGITS:
        return True
    elif isinstance(expr, WholeDecimal):
        return True
    elif isinstance(expr, Neg) and isLiteralInt(expr.operand):
        return True
    return False
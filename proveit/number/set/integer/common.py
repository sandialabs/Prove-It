from proveit import Literal
from digit import zero, one, two, three, four, five, six, seven, eight, nine

ALL_DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

def num(x):
    from proveit.number import Neg
    from proveit.number.set.integer.decimal import WholeDecimal
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
                return 8
            elif x == 9:
                return 9
        else:
            return WholeDecimal([num(int(digit)) for digit in str(x)])
    else:
        assert False, 'num not implemented for anything except integers currently. plans to take in strings or floats with specified precision'

infinity = Literal(__package__,'infinity',r'\infty')

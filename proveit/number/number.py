from proveit.expression import Literal, LATEX
from proveit.number.arithmeticOps import Neg
from proveit.number.natural.decimal import WholeDecimal

pkg = __package__

e = Literal(pkg,'e')
i = Literal(pkg,'i')
pi = Literal(pkg,'pi',{LATEX:r'\pi'})

zero = Literal(pkg,'0')
one = Literal(pkg,'1')
two = Literal(pkg,'2')
three = Literal(pkg,'3')
four = Literal(pkg,'4')
five = Literal(pkg,'5')
six = Literal(pkg,'6')
seven = Literal(pkg,'7')
eight = Literal(pkg,'8')
nine = Literal(pkg,'9')

ALL_DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]

infinity = Literal(pkg,'infinity',{LATEX:r'\infty'})
minusOne = Neg(one)
minusTwo = Neg(two)

def num(x):
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

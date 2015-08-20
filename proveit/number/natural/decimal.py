from proveit.expression import Literal, Operation

pkg = __package__
ZERO = Literal(pkg, '0')
ONE = Literal(pkg, '1')
TWO = Literal(pkg, '2')
THREE = Literal(pkg, '3')
FOUR = Literal(pkg, '4')
FIVE = Literal(pkg, '5')
SIX = Literal(pkg, '6')
SEVEN = Literal(pkg, '7')
EIGHT = Literal(pkg, '8')
NINE = Literal(pkg, '9')
ALL_DIGITS = [ZERO, ONE, TWO, THREE, FOUR, FIVE, SIX, SEVEN, EIGHT, NINE]

class WholeDecimal(Operation):
    def __init__(self, digits):
        Operation.__init__(self, WHOLE_DECIMAL, digits)
        self.digits = digits
        if not all(digit in ALL_DIGITS for digit in self.digits):
            raise Exception('A WholeDecimal may only be composed of 0-9 digits')
        
    def formatted(self, formatType, fence=False):
        return ''.join(digit.formatted(formatType, False) for digit in self.digits)
        
WHOLE_DECIMAL = Literal(pkg, 'WHOLE_DECIMAL', operationMaker=lambda digits : WholeDecimal(digits))

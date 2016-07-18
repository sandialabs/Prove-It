from proveit import Literal, Operation


WHOLE_DECIMAL = Literal(__package__, 'WHOLE_DECIMAL')

class WholeDecimal(Operation):
    def __init__(self, digits):
        from proveit.number.set.integer.common import ALL_DIGITS
        Operation.__init__(self, WHOLE_DECIMAL, digits)
        if len(digits) <= 1:
            raise Exception('A WholeDecimal should have two or more digits.  Single digit number should be represented as the corresponding Literal.')
        self.digits = digits
        if not all(digit in ALL_DIGITS for digit in self.digits):
            raise Exception('A WholeDecimal may only be composed of 0-9 digits')
        
    def formatted(self, formatType, fence=False):
        return ''.join(digit.formatted(formatType, False) for digit in self.digits)
        

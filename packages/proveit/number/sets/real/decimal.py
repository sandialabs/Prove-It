from proveit import Literal, Operation
from proveit.number.set.integer.decimal import WholeDecimal

class DecimalFraction(Operation):
    # operator of the DecimalFraction operation.
    _operator_ = Literal(stringFormat='DecimalFraction',context=__file__)   
    
    def __init__(self, integer_part, fractional_part):
        Operation.__init__(self, DecimalFraction._operator_, [integer_part, fractional_part])
        self.integer_part = integer_part
        self.fractional_part = fractional_part
        if not all(isinstance(part, WholeDecimal) for part in (integer_part, fractional_part)):
            raise Exception('A DecimalFraction may only be composed of WholeNumber integer and fractional parts')
        
    def formatted(self, formatType, fence=False):
        return self.integer_part.formatted(formatType, False) + '.' + self.fractional_part.formatted(formatType, False)

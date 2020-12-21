from proveit import Literal, Operation
from proveit.numbers.set.integer.deci import WholeDecimal


class Decimal_fraction(Operation):
    # operator of the Decimal_fraction operation.
    _operator_ = Literal(string_format='Decimal_fraction', theory=__file__)

    def __init__(self, integer_part, fractional_part):
        Operation.__init__(
            self, Decimal_fraction._operator_, [
                integer_part, fractional_part])
        self.integer_part = integer_part
        self.fractional_part = fractional_part
        if not all(isinstance(part, WholeDecimal)
                   for part in (integer_part, fractional_part)):
            raise Exception(
                'A Decimal_fraction may only be composed of WholeNumber integer and fractional parts')

    def formatted(self, format_type, fence=False):
        return self.integer_part.formatted(
            format_type, False) + '.' + self.fractional_part.formatted(format_type, False)

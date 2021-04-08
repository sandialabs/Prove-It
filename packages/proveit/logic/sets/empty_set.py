from proveit import Literal
from proveit.logic.irreducible_value import IrreducibleValue


class EmptySetLiteral(Literal, IrreducibleValue):
    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='emptyset', latex_format=r'\emptyset',
            styles=styles)

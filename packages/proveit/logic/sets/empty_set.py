from proveit import Literal
from proveit.logic.irreducible_value import IrreducibleValue

class EmptySetLiteral(Literal, IrreducibleValue):
    def __init__(self):
        Literal.__init__(self, string_format='emptyset', latex_format=r'\emptyset')

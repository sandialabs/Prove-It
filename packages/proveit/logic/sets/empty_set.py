from proveit import Literal
from proveit.logic.irreducible_value import IrreducibleValue

class EmptySetLiteral(Literal, IrreducibleValue):
    def __init__(self):
        Literal.__init__(self, stringFormat='emptyset', latexFormat=r'\emptyset')

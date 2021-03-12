from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals, NotEquals, InSet


class ImaginaryLiteral(IrreducibleValue, Literal):
    _in_complexStmts = None  # initializes when needed

    def __init__(self):
        Literal.__init__(self, 'i', r'\mathsf{i}', theory=__file__)

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other == self:
            return Equals(self, self).prove()
        pass  # need axioms/theorems to prove inequality amongst different numerals

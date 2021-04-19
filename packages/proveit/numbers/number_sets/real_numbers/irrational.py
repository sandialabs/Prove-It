from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals, NotEquals, InSet


class IrrationalLiteral(IrreducibleValue, Literal):
    _in_real_posStmts = None  # initializes when needed
    _notZeroStmts = None  # initializes when needed
    _positiveStmts = None  # initializes when needed

    def __init__(self, string_format, latex_format=None, *, styles=None):
        Literal.__init__(self, string_format, latex_format, 
                         theory=__file__, styles=styles)

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other == self:
            return Equals(self, self).prove()
        pass  # need axioms/theorems to prove inequality amongst different numerals

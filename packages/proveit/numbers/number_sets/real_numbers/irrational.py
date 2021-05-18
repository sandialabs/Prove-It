from proveit import Literal, USE_DEFAULTS, prover
from proveit.logic import IrreducibleValue, Equals, NotEquals, InSet


class IrrationalLiteral(IrreducibleValue, Literal):
    _in_real_posStmts = None  # initializes when needed
    _notZeroStmts = None  # initializes when needed
    _positiveStmts = None  # initializes when needed

    def __init__(self, string_format, latex_format=None, *, styles=None):
        Literal.__init__(self, string_format, latex_format, 
                         theory=__file__, styles=styles)

    @prover
    def eval_equality(self, other, **defaults_config):
        if other == self:
            return Equals(self, self).prove()
        raise NotImplementedError("'eval_equality' not implemented for "
                                  "%s to compare with %s"
                                  %(self, other))

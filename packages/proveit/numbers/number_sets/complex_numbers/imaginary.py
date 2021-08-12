from proveit import Literal, prover
from proveit.logic import IrreducibleValue, Equals


class ImaginaryLiteral(IrreducibleValue, Literal):
    _in_complexStmts = None  # initializes when needed

    def __init__(self, *, styles=None):
        Literal.__init__(self, 'i', r'\mathsf{i}', 
                         theory=__file__, styles=styles)

    @prover
    def eval_equality(self, other, **defaults_config):
        if other == self:
            return Equals(self, self).prove()
        raise NotImplementedError("'eval_equality' not implemented for "
                                  "%s to compare with %s"
                                  %(self, other))
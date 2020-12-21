from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals


class IrrationalLiteral(IrreducibleValue, Literal):
    _in_real_posStmts = None  # initializes when needed
    _notZeroStmts = None  # initializes when needed
    _positiveStmts = None  # initializes when needed

    def __init__(self, string_format, latex_format=None):
        Literal.__init__(self, string_format, latex_format, theory=__file__)

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other == self:
            return Equals(self, self).prove()
        pass  # need axioms/theorems to prove inequality amongst different numerals

    def deduce_in_real_pos(self):
        if IrrationalLiteral._in_real_posStmts is None:
            from real.theorems import e_in_real_pos, pi_in_real_pos
            IrrationalLiteral._in_real_posStmts = {
                'e': e_in_real_pos, 'pi': pi_in_real_pos}
        return IrrationalLiteral._in_real_posStmts[self.name]

    def deduce_not_zero(self):
        if IrrationalLiteral._notZeroStmts is None:
            from real.theorems import e_not_zero, pi_not_zero
            IrrationalLiteral._notZeroStmts = {
                'e': e_not_zero, 'pi': pi_not_zero}
        return IrrationalLiteral._notZeroStmts[self.name]

    def deduce_positive(self):
        if IrrationalLiteral._positiveStmts is None:
            from real.theorems import e_is_positive, pi_is_positive
            IrrationalLiteral._positiveStmts = {
                'e': e_is_positive, 'pi': pi_is_positive}
        return IrrationalLiteral._positiveStmts[self.name]

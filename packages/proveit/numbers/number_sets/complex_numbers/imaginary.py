from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals

class ImaginaryLiteral(IrreducibleValue, Literal):
    _in_complexStmts = None # initializes when needed

    def __init__(self):
        Literal.__init__(self, 'i', r'\mathsf{i}', theory=__file__)

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
        
    def deduce_in_complex(self):
        if ComplexLiteral._in_complexStmts is None:
            from complex.theorems import i_in_complex
            ComplexLiteral._in_complexStmts = {'i':i_in_complex}
        return ComplexLiteral._in_complexStmts[self.name]    

    def deduce_not_zero(self):
        if ComplexLiteral._notZeroStmts is None:
            from complex.theorems import i_not_zero
            ComplexLiteral._notZeroStmts = {'i':i_not_zero}
        return ComplexLiteral._notZeroStmts[self.name]

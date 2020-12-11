from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals

class ImaginaryLiteral(IrreducibleValue, Literal):
    _inComplexStmts = None # initializes when needed

    def __init__(self):
        Literal.__init__(self, 'i', r'\mathsf{i}', theory=__file__)

    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
        
    def deduceInComplex(self):
        if ComplexLiteral._inComplexStmts is None:
            from complex.theorems import iInComplex
            ComplexLiteral._inComplexStmts = {'i':iInComplex}
        return ComplexLiteral._inComplexStmts[self.name]    

    def deduceNotZero(self):
        if ComplexLiteral._notZeroStmts is None:
            from complex.theorems import iNotZero
            ComplexLiteral._notZeroStmts = {'i':iNotZero}
        return ComplexLiteral._notZeroStmts[self.name]

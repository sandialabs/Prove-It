from proveit import Literal

class ImaginaryLiteral(Literal):
    _inComplexesStmts = None # initializes when needed

    def __init__(self):
        Literal.__init__(self, 'i', context=__file__)
    
    def deduceInComplexes(self):
        if ComplexLiteral._inComplexesStmts is None:
            from complex.theorems import iInComplexes
            ComplexLiteral._inComplexesStmts = {'i':iInComplexes}
        return ComplexLiteral._inComplexesStmts[self.name]    

    def deduceNotZero(self):
        if ComplexLiteral._notZeroStmts is None:
            from complex.theorems import iNotZero
            ComplexLiteral._notZeroStmts = {'i':iNotZero}
        return ComplexLiteral._notZeroStmts[self.name]

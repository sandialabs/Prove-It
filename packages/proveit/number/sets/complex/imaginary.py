from proveit import Literal

class ComplexLiteral(Literal):
    _inComplexesStmts = None # initializes when needed

    def __init__(self, pkg, name, formatMap = None):
        Literal.__init__(self, pkg, name, formatMap)
    
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

i = ComplexLiteral(__package__, 'i')

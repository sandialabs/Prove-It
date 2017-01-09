from proveit import Literal

class IrrationalLiteral(Literal):
    _inRealsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, pkg, stringFormat, latexFormat = None):
        Literal.__init__(self, pkg, stringFormat, latexFormat)
    
    def deduceInRealsPos(self):
        if IrrationalLiteral._inRealsPosStmts is None:
            from real.theorems import eInRealsPos, piInRealsPos
            IrrationalLiteral._inRealsPosStmts = {'e':eInRealsPos, 'pi':piInRealsPos}
        return IrrationalLiteral._inRealsPosStmts[self.name]

    def deduceNotZero(self):
        if IrrationalLiteral._notZeroStmts is None:
            from real.theorems import eNotZero, piNotZero
            IrrationalLiteral._notZeroStmts = {'e':eNotZero, 'pi':piNotZero}
        return IrrationalLiteral._notZeroStmts[self.name]
    
    def deducePositive(self):
        if IrrationalLiteral._positiveStmts is None:
            from real.theorems import eIsPositive, piIsPositive
            IrrationalLiteral._positiveStmts = {'e':eIsPositive, 'pi':piIsPositive}
        return IrrationalLiteral._positiveStmts[self.name]
    
e = IrrationalLiteral(__package__, 'e')
pi = IrrationalLiteral(__package__, 'pi', r'\pi')

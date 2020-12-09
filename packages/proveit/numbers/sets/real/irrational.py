from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals


class IrrationalLiteral(IrreducibleValue, Literal):
    _inRealPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, stringFormat, latexFormat = None):
        Literal.__init__(self, stringFormat, latexFormat, theory=__file__)

    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
        
    def deduceInRealPos(self):
        if IrrationalLiteral._inRealPosStmts is None:
            from real.theorems import eInRealPos, piInRealPos
            IrrationalLiteral._inRealPosStmts = {'e':eInRealPos, 'pi':piInRealPos}
        return IrrationalLiteral._inRealPosStmts[self.name]

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

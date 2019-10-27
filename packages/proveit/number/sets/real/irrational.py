from proveit import Literal, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals


class IrrationalLiteral(IrreducibleValue, Literal):
    _inRealsPosStmts = None # initializes when needed
    _notZeroStmts = None # initializes when needed
    _positiveStmts = None # initializes when needed
    
    def __init__(self, stringFormat, latexFormat = None):
        Literal.__init__(self, stringFormat, latexFormat, context=__file__)

    def evalEquality(self, other, assumptions=USE_DEFAULTS):
        if other==self:
            return Equals(self, self).prove()
        pass # need axioms/theorems to prove inequality amongst different numerals
        
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

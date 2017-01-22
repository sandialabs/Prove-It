from proveit import Operation, Literal, USE_DEFAULTS
from proveit.common import xMulti, y

LENGTH = Literal(__package__, stringFormat = 'length')

class Len(Operation):
    def __init__(self, *operands):
        Operation.__init__(self, LENGTH, operands)
        
    @classmethod
    def operatorOfOperation(subClass):
        return LENGTH

    def string(self, fence=False):
        return '|' + self.operands.string(fence=False) + '|'
    
    def latex(self, fence=False):
        return '|' + self.operands.latex(fence=False) + '|'
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        from proveit.logic import Equals
        from _axioms_ import exprListLengthDef
        from _theorems_ import zeroLenExprList
        if len(self.operands) == 0:
            return zeroLenExprList
        else:
            equiv = exprListLengthDef.specialize({xMulti:self.operands[:-1], y:self.operands[-1]})
            value = equiv.rhs.evaluate(assumptions).rhs
            return Equals(self, value).prove(assumptions)

from proveit import Operation, Literal, USE_DEFAULTS
from proveit._common_ import xMulti, y

class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(stringFormat='length', context=__file__)   
    
    def __init__(self, *operands):
        Operation.__init__(self, Len._operator_, operands)
        
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

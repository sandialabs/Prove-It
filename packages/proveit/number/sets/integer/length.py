from proveit import Operation, Literal, USE_DEFAULTS
from proveit._common_ import x, y

class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(stringFormat='length', context=__file__)   
    
    def __init__(self, operand):
        Operation.__init__(self, Len._operator_, operand)
        
    def string(self, **kwargs):
        if hasattr(self, 'operand'): return '|' + self.operand.string() + '|'
        return '|' + self.operands.string(fence=True) + '|'
    
    def latex(self, **kwargs):
        if hasattr(self, 'operand'): return '|' + self.operand.latex() + '|'
        return '|' + self.operands.latex(fence=True) + '|'
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        from proveit.logic import Equals
        from _axioms_ import listLenDef
        from _theorems_ import listLenZero, listLenOne, listLenTwo, listLenThree, listLenFour, listLenFive
        from _theorems_ import listLenSix, listLenSeven, listLenEight, listLenNine
        if len(self.operands) == 0:
            return listLenZero
        elif len(self.operands) == 1:
            return listLenOne
        elif len(self.operands) == 2:
            return listLenTwo
        elif len(self.operands) == 3:
            return listLenThree
        elif len(self.operands) == 4:
            return listLenFour
        elif len(self.operands) == 5:
            return listLenFive
        elif len(self.operands) == 6:
            return listLenSix
        elif len(self.operands) == 7:
            return listLenSeven
        elif len(self.operands) == 8:
            return listLenEight
        elif len(self.operands) == 9:
            return listLenNine            
        else:
            equiv = listLenDef.specialize({x:self.operands[:-1], y:self.operands[-1]})
            value = equiv.rhs.evaluate(assumptions).rhs
            return Equals(self, value).prove(assumptions)

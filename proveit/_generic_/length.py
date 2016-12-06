from proveit import Operation, Literal

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

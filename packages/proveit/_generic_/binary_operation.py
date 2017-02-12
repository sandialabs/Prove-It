from proveit import Operation
from fencing import maybeFenced

class BinaryOperation(Operation):
    def __init__(self, operator, A, B):
        Operation.__init__(self, operator, (A, B))
        self.leftOperand = self.operands[0]
        self.rightOperand = self.operands[1]

    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
        
    def _formatted(self, formatType, **kwargs):
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subLeftFence =  kwargs['subLeftFence'] if 'subLeftFence' in kwargs else True
        subRightFence =  kwargs['subRightFence'] if 'subRightFence' in kwargs else True
        # override this default as desired
        formattedLeft = self.leftOperand.formatted(formatType, fence=subLeftFence)
        formattedRight = self.rightOperand.formatted(formatType, fence=subRightFence)
        formattedOp = self.operator.formatted(formatType)
        innerStr = formattedLeft + ' ' + formattedOp + ' ' + formattedRight
        return maybeFenced(formatType, innerStr, fence=fence)

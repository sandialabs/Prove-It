from proveit.expression import Operation, Literal, STRING, LATEX
from proveit.multiExpression import ExpressionTensor, Block

pkg = __package__

class Matrix(Operation):
    def __init__(self, exprTensor):
        Operation.__init__(self, MATRIX, exprTensor)
        self.tensor = self.operands
        if not isinstance(self.tensor, ExpressionTensor):
            raise ImproperMatrix('Matrix must be given an ExpressionTensor for its operands')
        if len(self.tensor.shape) != 2:
            raise ImproperMatrix('Matrix must be given a 2-dimensional ExpressionTensor')
        self.nrows = self.tensor.shape[0]
        self.ncolumns = self.tensor.shape[1]
    
    def formatted(self, formatType, fence=True):
        if formatType == STRING:
            return Operation.formatted(formatType, fence=False)
        elif formatType == LATEX:
            return r'\left[' + self.operands.formatted(formatType) + '\right]'


MATRIX = Literal(pkg, 'MATRIX', operationMaker = lambda operands : Matrix(operands))


class ImproperMatrix:
    def __init__(self, msg):
        self.msg = msg
    def str(self):
        return self.msg
    
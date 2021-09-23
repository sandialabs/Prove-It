from proveit.expression import Operation, Literal, STRING, LATEX
from proveit.multi_expression import ExpressionTensor, Block

pkg = __package__


class Matrix(Operation):
    def __init__(self, expr_tensor, *, styles=None):
        Operation.__init__(self, MATRIX, expr_tensor, styles=styles)
        self.tensor = self.operands
        if not isinstance(self.tensor, ExpressionTensor):
            raise ImproperMatrix(
                'Matrix must be given an ExpressionTensor for its operands')
        if len(self.tensor.shape) != 2:
            raise ImproperMatrix(
                'Matrix must be given a 2-dimensional ExpressionTensor')
        self.nrows = self.tensor.shape[0]
        self.ncolumns = self.tensor.shape[1]

    def formatted(self, format_type, fence=True):
        if format_type == STRING:
            return Operation.formatted(format_type, fence=False)
        elif format_type == LATEX:
            return r'\left[' + self.operands.formatted(format_type) + '\right]'


MATRIX = Literal(
    pkg,
    'MATRIX',
    operation_maker=lambda operands: Matrix(operands))


class ImproperMatrix:
    def __init__(self, msg):
        self.msg = msg

    def str(self):
        return self.msg

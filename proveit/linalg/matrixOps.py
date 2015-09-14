from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation

pkg = __package__

class MatrixProd(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Matrix dot product of any number of operands.
        '''
        AssociativeOperation.__init__(self, MATRIX_PROD, *operands)

MATRIX_PROD = Literal(pkg, 'MATRIX_PROD', {STRING: r'.', LATEX: r' '}, operationMaker = lambda operands : MatrixProd(*operands))

class ScalarProd(BinaryOperation):
    def __init__(self, *operands):
        r'''
        Product between a scalar and a matrix.
        '''
        BinaryOperation.__init__(self, SCALAR_PROD, *operands)

SCALAR_PROD = Literal(pkg, 'SCALAR_PROD', {STRING: r'*', LATEX: r' '}, operationMaker = lambda operands : ScalarProd(*operands))

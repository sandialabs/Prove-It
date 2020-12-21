from proveit import Literal, Operation #, STRING, LATEX
# from proveit.logic import Equation
# from proveit.logic.generic_ops import AssociativeOperation, BinaryOperation
from proveit._common_ import x, alpha, beta

pkg = __package__

class MatrixProd(Operation):
    '''
    Matrix dot product of any number of operands.
    '''

    # the literal operator of the MatrixProd operation
    # perhaps use MATRIX_PROD for string?
    # latex_format try using \; in place of a blank space
    _operator_ = Literal(string_format=r'.', latex_format = r'\thinspace',
                         theory=__file__)

    def __init__(self, *operands):
        r'''
        Matrix dot product of any number of operands.
        '''
        Operation.__init__(self, MatrixProd._operator_, operands)
    
    def formatted(self, format_type, fence=False, sub_fence=True):
        # Temporary hack to get quantum bra and ket products to display properly.
        # This should eventually be done differently because we shouldn't need to
        # know anything about the quantum application here.
        from proveit.physics.quantum import Bra, Ket, RegisterBra, RegisterKet
        if len(self.operands) == 2 and (isinstance(self.operands[0], Bra) or isinstance(self.operands[0], RegisterBra)) and (isinstance(self.operands[1], Ket) or isinstance(self.operands[1], RegisterKet)):
            return self.operands[0].formatted(format_type) + self.operands[1].formatted(format_type, no_lvert=True)
        # return Operation.formatted(self, format_type, fence, sub_fence)
        return Operation._formatted(self, format_type=format_type, fence=fence, sub_fence=sub_fence)


class ScalarProd(Operation):
    '''
    Represents the product of a scalar and a matrix (or vector).
    For example, ScalarProd(a, A) returns a A, the product of a scalar
    'a' and the matrix A.
    '''
    # the literal operator of the MatrixProd operation
    # perhaps use SCALAR_PROD for string?
    # latex_format try using \; in place of a blank space
    _operator_ = Literal(string_format=r'*', latex_format = r'\thinspace',
                         theory=__file__)

    def __init__(self, scalar, scaled):
        r'''
        Product between a scalar and a matrix (or vector).
        '''
        Operation.__init__(self, ScalarProd._operator_, [scalar, scaled])
        self.scalar = scalar
        self.scaled = scaled

    # def do_reduced_simplification(self):
    #     '''
    #     For the trivial case a nested scalar product, derive and return this scalar product
    #     expression equated with a simplified form.
    #     '''
    #     from theorems import doubly_scaled_as_singly_scaled
    #     if isinstance(self.scaled, ScalarProd):
    #         eq = Equation()
    #         expr = self
    #         '''
    #         try:
    #             # try to simplify it more with recursion
    #             inner_simpl = self.scaled.simplication()
    #             dummy_var = self.safe_dummy_var()
    #             eq.update(inner_simpl.substitution(ScalarProd(self.scalar, dummy_var), dummy_var))
    #             expr = eq.eq_expr.rhs
    #         except:
    #             pass
    #         '''
    #         eq.update(doubly_scaled_as_singly_scaled.instantiate({x:expr.scaled.scaled}).instantiate({alpha:expr.scalar, beta:expr.scaled.scalar}))
    #         return eq.eq_expr
    #     else:
    #         raise ValueError('Only trivial simplification is implemented (nested scalar products)')

    # def factor(self, scalar):
    #     '''
    #     Factor the given scalar from the scaled quantity, combining it with the other scalar as multiplication.
    #     '''
    #     eq = Equation()
    #     # pull the factor from the "scaled" quantity
    #     scaled_factoring = self.scaled.factor(scalar)
    #     dummy_var = self.safe_dummy_var()
    #     eq.update(scaled_factoring.substitution(ScalarProd(self.scalar, dummy_var), dummy_var))
    #     # simplify the nested ScaledProd
    #     expr = eq.eq_expr.rhs
    #     eq.update(expr.simplification())
    #     return eq.eq_expr

# SCALAR_PROD = Literal(pkg, 'SCALAR_PROD', {STRING: r'*', LATEX: r' '}, operation_maker = lambda operands : ScalarProd(*operands))

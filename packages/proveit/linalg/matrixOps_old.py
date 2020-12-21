from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic import Equation
from proveit.basiclogic.generic_ops import AssociativeOperation, BinaryOperation
from proveit.common import x, alpha, beta

pkg = __package__

class MatrixProd(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Matrix dot product of any number of operands.
        '''
        AssociativeOperation.__init__(self, MATRIX_PROD, *operands)
    
    def formatted(self, format_type, fence=False, sub_fence=True):
        # Temporary hack to get quantum bra and ket products to display properly.
        # This should eventually be done differently because we shouldn't need to
        # know anything about the quantum application here.
        from proveit.physics.quantum import Bra, Ket, RegisterBra, RegisterKet
        if len(self.operands) == 2 and (isinstance(self.operands[0], Bra) or isinstance(self.operands[0], RegisterBra)) and (isinstance(self.operands[1], Ket) or isinstance(self.operands[1], RegisterKet)):
            return self.operands[0].formatted(format_type) + self.operands[1].formatted(format_type, no_lvert=True)
        return AssociativeOperation.formatted(self, format_type, fence, sub_fence)

MATRIX_PROD = Literal(pkg, 'MATRIX_PROD', {STRING: r'.', LATEX: r' '}, operation_maker = lambda operands : MatrixProd(*operands))

class ScalarProd(BinaryOperation):
    def __init__(self, *operands):
        r'''
        Product between a scalar and a matrix.
        '''
        BinaryOperation.__init__(self, SCALAR_PROD, *operands)
        self.scalar = operands[0]
        self.scaled = operands[1]

    def do_reduced_simplification(self):
        '''
        For the trivial case a nested scalar product, derive and return this scalar product
        expression equated with a simplified form.
        '''
        from theorems import doubly_scaled_as_singly_scaled
        if isinstance(self.scaled, ScalarProd):
            eq = Equation()
            expr = self
            '''
            try:
                # try to simplify it more with recursion
                inner_simpl = self.scaled.simplication()
                dummy_var = self.safe_dummy_var()
                eq.update(inner_simpl.substitution(ScalarProd(self.scalar, dummy_var), dummy_var))
                expr = eq.eq_expr.rhs
            except:
                pass
            '''
            eq.update(doubly_scaled_as_singly_scaled.instantiate({x:expr.scaled.scaled}).instantiate({alpha:expr.scalar, beta:expr.scaled.scalar}))
            return eq.eq_expr
        else:
            raise ValueError('Only trivial simplification is implemented (nested scalar products)')

    def factor(self, scalar):
        '''
        Factor the given scalar from the scaled quantity, combining it with the other scalar as multiplication.
        '''
        eq = Equation()
        # pull the factor from the "scaled" quantity
        scaled_factoring = self.scaled.factor(scalar)
        dummy_var = self.safe_dummy_var()
        eq.update(scaled_factoring.substitution(ScalarProd(self.scalar, dummy_var), dummy_var))
        # simplify the nested ScaledProd
        expr = eq.eq_expr.rhs
        eq.update(expr.simplification())
        return eq.eq_expr

SCALAR_PROD = Literal(pkg, 'SCALAR_PROD', {STRING: r'*', LATEX: r' '}, operation_maker = lambda operands : ScalarProd(*operands))

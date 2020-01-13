from proveit.expression import Literal, STRING, LATEX
from proveit.basiclogic import Equation
from proveit.basiclogic.genericOps import AssociativeOperation, BinaryOperation
from proveit.common import x, alpha, beta

pkg = __package__

class MatrixProd(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Matrix dot product of any number of operands.
        '''
        AssociativeOperation.__init__(self, MATRIX_PROD, *operands)
    
    def formatted(self, formatType, fence=False, subFence=True):
        # Temporary hack to get quantum bra and ket products to display properly.
        # This should eventually be done differently because we shouldn't need to
        # know anything about the quantum application here.
        from proveit.physics.quantum import Bra, Ket, RegisterBra, RegisterKet
        if len(self.operands) == 2 and (isinstance(self.operands[0], Bra) or isinstance(self.operands[0], RegisterBra)) and (isinstance(self.operands[1], Ket) or isinstance(self.operands[1], RegisterKet)):
            return self.operands[0].formatted(formatType) + self.operands[1].formatted(formatType, no_lvert=True)
        return AssociativeOperation.formatted(self, formatType, fence, subFence)

MATRIX_PROD = Literal(pkg, 'MATRIX_PROD', {STRING: r'.', LATEX: r' '}, operationMaker = lambda operands : MatrixProd(*operands))

class ScalarProd(BinaryOperation):
    def __init__(self, *operands):
        r'''
        Product between a scalar and a matrix.
        '''
        BinaryOperation.__init__(self, SCALAR_PROD, *operands)
        self.scalar = operands[0]
        self.scaled = operands[1]

    def doReducedSimplification(self):
        '''
        For the trivial case a nested scalar product, derive and return this scalar product
        expression equated with a simplified form.
        '''
        from theorems import doublyScaledAsSinglyScaled
        if isinstance(self.scaled, ScalarProd):
            eq = Equation()
            expr = self
            '''
            try:
                # try to simplify it more with recursion
                innerSimpl = self.scaled.simplication()
                dummyVar = self.safeDummyVar()
                eq.update(innerSimpl.substitution(ScalarProd(self.scalar, dummyVar), dummyVar))
                expr = eq.eqExpr.rhs
            except:
                pass
            '''
            eq.update(doublyScaledAsSinglyScaled.specialize({x:expr.scaled.scaled}).specialize({alpha:expr.scalar, beta:expr.scaled.scalar}))
            return eq.eqExpr
        else:
            raise ValueError('Only trivial simplification is implemented (nested scalar products)')

    def factor(self, scalar):
        '''
        Factor the given scalar from the scaled quantity, combining it with the other scalar as multiplication.
        '''
        eq = Equation()
        # pull the factor from the "scaled" quantity
        scaledFactoring = self.scaled.factor(scalar)
        dummyVar = self.safeDummyVar()
        eq.update(scaledFactoring.substitution(ScalarProd(self.scalar, dummyVar), dummyVar))
        # simplify the nested ScaledProd
        expr = eq.eqExpr.rhs
        eq.update(expr.simplification())
        return eq.eqExpr

SCALAR_PROD = Literal(pkg, 'SCALAR_PROD', {STRING: r'*', LATEX: r' '}, operationMaker = lambda operands : ScalarProd(*operands))

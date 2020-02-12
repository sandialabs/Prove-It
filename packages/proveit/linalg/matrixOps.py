from proveit import Literal, Operation #, STRING, LATEX
# from proveit.logic import Equation
# from proveit.logic.genericOps import AssociativeOperation, BinaryOperation
from proveit._common_ import x, alpha, beta

pkg = __package__

class MatrixProd(Operation):
    '''
    Matrix dot product of any number of operands.
    Modified 02/11/2020 by wdc: making the class extend Operation
    instead of AssociativeOperation
    '''

    # the literal operator of the MatrixProd operation
    # perhaps use MATRIX_PROD for string?
    # latexFormat try using \; in place of a blank space
    _operator_ = Literal(stringFormat=r'.', latexFormat = r'\;',
                         context=__file__)

    def __init__(self, *operands):
        r'''
        Matrix dot product of any number of operands.
        '''
        print("MatrixProd, operands = {}".format(operands))                     # for testing; delete later
        print("MatrixProd, *operands = {}".format(*operands))                   # for testing; delete later
        Operation.__init__(self, MatrixProd._operator_, *operands)
        print("MatrixProd, operands = {}".format(operands))                     # for testing; delete later
    
    def formatted(self, formatType, fence=False, subFence=True):
        # Temporary hack to get quantum bra and ket products to display properly.
        # This should eventually be done differently because we shouldn't need to
        # know anything about the quantum application here.
        from proveit.physics.quantum import Bra, Ket, RegisterBra, RegisterKet
        if len(self.operands) == 2 and (isinstance(self.operands[0], Bra) or isinstance(self.operands[0], RegisterBra)) and (isinstance(self.operands[1], Ket) or isinstance(self.operands[1], RegisterKet)):
            return self.operands[0].formatted(formatType) + self.operands[1].formatted(formatType, no_lvert=True)
        # return Operation.formatted(self, formatType, fence, subFence)
        return Operation._formatted(self, formatType=formatType, fence=fence, subFence=subFence)

# MATRIX_PROD = Literal(pkg, 'MATRIX_PROD', {STRING: r'.', LATEX: r' '}, operationMaker = lambda operands : MatrixProd(*operands))

class ScalarProd(Operation):
    '''
    Product between a scalar and a matrix.
    Modified 02/11/2020 by wdc: making the class extend Operation
    instead of BinaryOperation
    '''
    # the literal operator of the MatrixProd operation
    # perhaps use SCALAR_PROD for string?
    # latexFormat try using \; in place of a blank space
    _operator_ = Literal(stringFormat=r'*', latexFormat = r'\;',
                         context=__file__)

    def __init__(self, *operands):
        r'''
        Product between a scalar and a matrix.
        '''
        print("ScalarProd, operands = {}".format(operands))                     # for testing; delete later
        Operation.__init__(self, ScalarProd._operator_, *operands)
        print("ScalarProd, operands = {}".format(operands))                     # for testing; delete later
        self.scalar = operands[0][0]
        self.scaled = operands[0][1]

    # def doReducedSimplification(self):
    #     '''
    #     For the trivial case a nested scalar product, derive and return this scalar product
    #     expression equated with a simplified form.
    #     '''
    #     from theorems import doublyScaledAsSinglyScaled
    #     if isinstance(self.scaled, ScalarProd):
    #         eq = Equation()
    #         expr = self
    #         '''
    #         try:
    #             # try to simplify it more with recursion
    #             innerSimpl = self.scaled.simplication()
    #             dummyVar = self.safeDummyVar()
    #             eq.update(innerSimpl.substitution(ScalarProd(self.scalar, dummyVar), dummyVar))
    #             expr = eq.eqExpr.rhs
    #         except:
    #             pass
    #         '''
    #         eq.update(doublyScaledAsSinglyScaled.specialize({x:expr.scaled.scaled}).specialize({alpha:expr.scalar, beta:expr.scaled.scalar}))
    #         return eq.eqExpr
    #     else:
    #         raise ValueError('Only trivial simplification is implemented (nested scalar products)')

    # def factor(self, scalar):
    #     '''
    #     Factor the given scalar from the scaled quantity, combining it with the other scalar as multiplication.
    #     '''
    #     eq = Equation()
    #     # pull the factor from the "scaled" quantity
    #     scaledFactoring = self.scaled.factor(scalar)
    #     dummyVar = self.safeDummyVar()
    #     eq.update(scaledFactoring.substitution(ScalarProd(self.scalar, dummyVar), dummyVar))
    #     # simplify the nested ScaledProd
    #     expr = eq.eqExpr.rhs
    #     eq.update(expr.simplification())
    #     return eq.eqExpr

# SCALAR_PROD = Literal(pkg, 'SCALAR_PROD', {STRING: r'*', LATEX: r' '}, operationMaker = lambda operands : ScalarProd(*operands))

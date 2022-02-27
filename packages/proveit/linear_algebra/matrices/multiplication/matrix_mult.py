from proveit import Literal, Operation, equality_prover
# from proveit.logic import Equation
# from proveit.logic.generic_ops import AssociativeOperation, BinaryOperation
from proveit import b, m, x, A, alpha, beta, theta, rho
from proveit.logic import Equals
from proveit.numbers import Exp

class MatrixMult(Operation):
    '''
    Matrix dot product of any number of operands.
    '''

    # the literal operator of the MatrixProd operation
    # perhaps use MATRIX_PROD for string?
    # latex_format try using \; in place of a blank space
    _operator_ = Literal(string_format=r'.', latex_format=r'\thinspace',
                         theory=__file__)

    def __init__(self, *operands, styles=None):
        r'''
        Matrix dot product of any number of operands.
        '''
        Operation.__init__(self, MatrixMult._operator_, operands,
                           styles=styles)

    @equality_prover('equated', 'equate')
    def deduce_equality(self, equality, **defaults_config):
        '''
        We can handle the special case of proving an eigen
        exponentiation application:
            A^m x = b^m x
            if A x = b x.
        or
            A^m x = exp(i m theta) x
            if A x = exp(i theta) x
        or
            A^m x = exp(2 pi i m theta) x
            if A x = exp(2 pi i theta) x
        '''
        from proveit.numbers import Mult, two, pi, e, i
        from proveit.linear_algebra import ScalarMult
        if not isinstance(equality, Equals):
            raise ValueError("The 'equality' should be an Equals expression")
        if equality.lhs != self:
            raise ValueError("The left side of 'equality' should be 'self'")
        def raise_not_implemented():
            raise NotImplementedError(
                "MatrixMult.deduce_equality is only implemented for "
                "proving an eigen exponentiation application of the form "
                "A^m x = b^m x, not %s"%equality)
        if self.operands.is_double() and isinstance(equality.rhs, ScalarMult):
            from proveit.linear_algebra.matrices.exponentiation import (
                    MatrixExp, eigen_exp_application,
                    unital_eigen_exp_application,
                    unital2pi_eigen_exp_application)
            Am, x_lhs = self.operands
            bm, x_rhs = equality.rhs.operands
            if (x_lhs==x_rhs and isinstance(Am, MatrixExp) 
                  and isinstance(bm, Exp)):
                _m = Am.exponent
                _A = Am.base
                _x = x_lhs
                if bm.base == e and isinstance(bm.exponent, Mult):
                    if bm.exponent.operands.entries[:3] == (two, pi, i):
                        # Use the 2 pi i convention.
                        front_factors = (two, pi, i)
                    else:
                        # No 2 pi i convention, just i.
                        front_factors = (i,)
                    try:
                        # Do factorization to get it in the desired
                        # form.
                        factorization1 = bm.exponent.factorization(
                                front_factors, pull='left',
                                group_factors = False,
                                group_remainder = True,
                                preserve_all=True)
                        if hasattr(factorization1.rhs.operands[-1],
                                   'factorization'):
                            factorization2 = (
                                    factorization1.rhs.inner_expr()
                                    .operands[-1].factorization(
                                            _m, pull='left', 
                                            group_remainder = True,
                                            preserve_all=True))
                        else:
                            factorization2 = factorization1
                    except ValueError:
                        # If the factorication didn't work, assume the
                        # form is not correct.
                        raise_not_implemented()
                    factorization = factorization1.apply_transitivity(
                            factorization2)
                    phase_factor = factorization.rhs.operands[-1].operands[-1]
                    repl_map = {m:_m, A:_A, x:_x}
                    replacements = [factorization.derive_reversed()]
                    if len(front_factors) == 3:
                        repl_map[rho] = phase_factor
                        return unital2pi_eigen_exp_application.instantiate(
                                repl_map, replacements=replacements)
                    else:
                        repl_map[theta] = phase_factor
                        return unital_eigen_exp_application.instantiate(
                                repl_map, replacements=replacements)
                elif Am.exponent == bm.exponent:
                    _b = bm.base
                    return eigen_exp_application.instantiate(
                            {m:_m, b:_b, A:_A, x:_x})
        raise_not_implemented()
                

    '''
    def formatted(self, format_type, fence=False, sub_fence=True):
        # Temporary hack to get quantum bra and ket products to display properly.
        # This should eventually be done differently because we shouldn't need to
        # know anything about the quantum application here.
        from proveit.physics.quantum import Bra, Ket, RegisterBra, RegisterKet
        if (self.operands.num_entries() == 2 and (
                isinstance(self.operands[0], Bra) 
                or isinstance(self.operands[0],RegisterBra)) and (
                    isinstance(self.operands[1], Ket) or 
                    isinstance(self.operands[1], RegisterKet))):
            return self.operands[0].formatted(
                format_type) + self.operands[1].formatted(format_type, no_lvert=True)
        # return Operation.formatted(self, format_type, fence, sub_fence)
        return Operation._formatted(
            self,
            format_type=format_type,
            fence=fence,
            sub_fence=sub_fence)
    '''

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

from proveit import defaults, equality_prover, Literal, Operation
from proveit import f, x, y, alpha, S  # a_etc, x_etc, y_etc, z_etc,
from proveit.logic import Equals
from proveit.numbers import one, subtract
from proveit.core_expr_types import Len
from proveit.linear_algebra.matrix_ops import ScalarProd

pkg = __package__


class TensorProd(Operation):
    r'''
    Class to represent the tensor product of any number of operands.
    Example usage: TensorProd(x, y, z) represents the tensor product
    x \otimes y \otimes z.
    '''
    # the literal operator of the TensorProd operation
    _operator_ = Literal(string_format=r'otimes', latex_format=r'{\otimes}',
                         theory=__file__)

    def __init__(self, *operands, styles=None):
        Operation.__init__(self, TensorProd._operator_, operands,
                           styles=styles)
        self.factors = self.operands

    @equality_prover('factorized', 'factor')
    def factorization(self, scalar, **defaults_config):
        '''
        Factor the given scalar from one of the tensor product
        multiplicands and return the original tensor product equal to
        the factored version. For example,
            TensorProd(a, cb, d).factorization(c)
        returns
            |- TensorProd(a, ScalarProd(c, b), d).factorization(c) =
               c TensorProd(a, b, d)
        Note that this works only for explicit ScalarProd components
        within the TensorProd structure. Plans are to generalize this
        to not require an explicit ScalarProd object (instead allowing
        the more general Mult object).
        '''
        from . import factor_scalar_from_tensor_prod
        for k, operand in enumerate(self.operands):
            if isinstance(operand, ScalarProd) and operand.scalar == scalar:
                _m, _n, _x, _y, _z, _alpha = (
                    factor_scalar_from_tensor_prod.all_instance_vars())
                # organize and compute the instantiation subs
                _m_sub = Len(self.operands[:k]).computed()
                _n_sub = subtract(subtract(
                    Len(self.operands).computed(), _m_sub), one)
                _x_sub = self.operands[:k]
                _y_sub = operand.scaled
                _z_sub = self.operands[k + 1:]
                _alpha_sub = scalar
                # instantiate and return
                return factor_scalar_from_tensor_prod.instantiate(
                    {_m: _m_sub, _n: _n_sub, _x: _x_sub, _y: _y_sub,
                    _z: _z_sub, _alpha: _alpha_sub})
        raise ValueError(
            "Targeted scalar {0} not found in any of the tensor product "
            "factors {1}".format(scalar, self.operands))

    # @equality_prover('distributed', 'distribute')
    # def distribution(self, factor_idx, **defaults_config):
    #     '''
    #     Distribute over the factor at the given index.
    #     '''
    #     from . import (distribute_tensor_prod_over_sum,
    #             distribute_tensor_prod_over_summation)
    #     from proveit.numbers import Add, Sum
    #     factor = self.factors[factor_idx]
    #     if isinstance(factor, Add):
    #         return distribute_tensor_prod_over_sum.instantiate(
    #             {x_etc: self.factors[:factor_idx], y_etc: factor.terms, z_etc: self.factors[factor_idx + 1:]})
    #     elif isinstance(factor, Sum):
    #         domain = factor.domain
    #         summand = factor.summand
    #         index = factor.index
    #         return distribute_tensor_prod_over_summation.instantiate({x_etc: self.factors[:factor_idx], Operation(
    #             f, index): summand, S: domain, y: index, z_etc: self.factors[factor_idx + 1:]})
    #     else:
    #         raise Exception(
    #             "Don't know how to distribute tensor product over " + str(factor.__class__) + " factor")

    @equality_prover('distributed', 'distribute')
    def distribution(self, factor_idx, **defaults_config):
        '''
        Distribute over the factor at the given index.
        '''
        from . import (distribute_tensor_prod_over_sum,
                       distribute_tensor_prod_over_summation)
        from proveit.numbers import Add, Sum
        factor = self.factors[factor_idx]
        if isinstance(factor, Add):
            _i, _j, _k, _x, _y, _z = (
                    distribute_tensor_prod_over_sum.all_instance_vars())
            _i_sub = Len(self.operands[:factor_idx]).computed()
            _j_sub = Len(self.operands[factor_idx].operands).computed()
            _k_sub = subtract(subtract(Len(self.operands).computed(),
                    _i_sub), one)
            _x_sub = self.factors[:factor_idx]
            _y_sub = factor.terms
            _z_sub = self.factors[factor_idx+1:]
            return distribute_tensor_prod_over_sum.instantiate(
                {_i: _i_sub, _j: _j_sub, _k: _k_sub,
                 _x: _x_sub, _y: _y_sub, _z: _z_sub})
        elif isinstance(factor, Sum):
            index = factor.index
            _m, _n, _f, _S, _x, _z = (
                distribute_tensor_prod_over_summation.all_instance_vars())
            _y = y # that's the index var in the summation in the thm
            _m_sub = Len(self.factors[:factor_idx]).computed()
            _n_sub = subtract(subtract(Len(self.operands).computed(),
                     _m_sub), one)
            _f_sub = factor.summand
            _S_sub = factor.domain
            _x_sub = self.factors[:factor_idx]
            _y_sub = factor.index
            _z_sub = self.factors[factor_idx + 1:]
            return distribute_tensor_prod_over_summation.instantiate(
                {_m: _m_sub, _n: _n_sub, _x: _x_sub,
                Operation(f, index, styles=None): _f_sub, _S: _S_sub,
                _y: _y_sub, _z: _z_sub})
        else:
            raise ValueError(self, defaults.assumptions,
                "Don't know how to distribute tensor product over " +
                str(factor.__class__) + " factor")

    # 2/11/2020 temporarily commented out by wdc until we determine the
    # equivalents for a_etc, etc
    # def equate_factors(self, tensor_equality):
    #     from theorems import tensor_prod_equiv_by_elimination
    #     if not isinstance(tensor_equality, Equals):
    #         raise ValueError('tensor_equality should be an Equals expression')
    #     if not isinstance(tensor_equality.lhs, TensorProd) or not isinstance(tensor_equality.rhs, TensorProd):
    #         raise ValueError("tensor_equality should be an Equals expression of tensor products")
    #     if len(tensor_equality.lhs.factors) != len(tensor_equality.rhs.factors):
    #         raise ValueError("tensor_equality should be an Equals expression of tensor products with the same number of factors")
    #     if self == tensor_equality.rhs:
    #         # reverse the equality so "self" is on the left
    #         tensor_equality = tensor_equality.derive_reversed()
    #     if not self == tensor_equality.lhs:
    #         raise ValueError("tensor_equality should be an Equals expression of tensor products with 'self' on one side of the equality")
    #     for k, (factor1, factor2) in enumerate(zip(tensor_equality.lhs.factors, tensor_equality.rhs.factors)):
    #         if factor1 != factor2:
    #             if tensor_equality.lhs.factors[:k] != tensor_equality.rhs.factors[:k] or tensor_equality.lhs.factors[k+1:] != tensor_equality.rhs.factors[k+1:]:
    #                 raise ValueError("tensor_equality should be an Equals expression of tensor products that are the same except for only one factor")
    # return
    # tensor_prod_equiv_by_elimination.instantiate({a_etc:tensor_equality.lhs.factors[:k],
    # x:factor1, y:factor2, z_etc:tensor_equality.lhs.factors[k+1:]})


class TensorExp(Operation):
    '''
    '''

    # the literal operator of the TensorExp operation
    _operator_ = Literal(
            string_format=r'otimes', latex_format=r'{\tiny\otimes}',
            theory=__file__)

    def __init__(self, base, exponent, *, styles=None):
        r'''
        Tensor exponentiation to any natural number exponent.
        '''
        Operation.__init__(self, TensorExp._operator_, (base, exponent),
                           styles=styles)
        self.base = self.operands[0]
        self.exponent = self.operands[1]

    def _formatted(self, format_type, fence=True):
        # changed from formatted to _formatted 2/14/2020 (wdc)
        formatted_base = self.base.formatted(format_type, fence=True)
        formatted_exp = self.exponent.formatted(format_type, fence=True)
        if format_type == 'latex':
            return formatted_base + r'^{\otimes ' + formatted_exp + '}'
        elif format_type == 'string':
            return formatted_base + '^{otimes ' + formatted_exp + '}'

    @equality_prover('do_reduced_simplified', 'do_reduced_simplify')
    def do_reduced_simplification(self, **defaults_config):
        '''
        For the trivial cases of a one exponent, derive and return
        this tensor-exponentiated expression equated with a simplified
        form. Assumptions may be necessary to deduce necessary
        conditions for the simplification. For example, 
        TensorExp(x, one).do_reduced_simplification()
        '''
        from proveit.numbers import zero, one
        from . import tensor_exp_one
        if self.exponent == one:
            return tensor_exp_one.instantiate({x: self.base})
        raise ValueError('Only trivial simplification is implemented '
                         '(tensor exponent of one). Submitted tensor '
                         'exponent was {}.'.format(self.exponent))

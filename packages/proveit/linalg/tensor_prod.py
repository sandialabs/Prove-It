from proveit import Literal, Operation
from proveit.logic import Equals
from proveit import f, x, y, alpha, S  # a_etc, x_etc, y_etc, z_etc,
from proveit.linalg.matrix_ops import ScalarProd

pkg = __package__


class TensorProd(Operation):
    '''
    Class to represent the tensor product of any number of operands.
    Modified 02/11/2020 by wdc: making the class extend Operation
    instead of AssociativeOperation
    '''
    # the literal operator of the TensorProd operation
    _operator_ = Literal(string_format=r'otimes', latex_format=r'{\otimes}',
                         theory=__file__)

    def __init__(self, *operands, styles=None):
        Operation.__init__(self, TensorProd._operator_, operands,
                           styles=styles)
        self.factors = self.operands

    def factor(self, scalar):
        '''
        Factor the given scalar from one of the tensor product scalars.
        '''
        from theorems import factor_scalar_from_tensor_prod
        for k, operand in enumerate(self.operands):
            if isinstance(operand, ScalarProd) and operand.scalar == scalar:
                return factor_scalar_from_tensor_prod.instantiate(
                    {x_etc: self.operands[:k], y: operand.scaled, z_etc: self.operands[k + 1:]}).instantiate({alpha: scalar})
        raise ValueError(
            'Scalar not found in any of the tensor product factors')

    def distribute(self, factor_idx):
        '''
        Distribute over the factor at the given index.
        '''
        from theorems import distribute_tensor_prod_over_sum, distribute_tensor_prod_over_summation
        from proveit.numbers import Add, Sum
        factor = self.factors[factor_idx]
        if isinstance(factor, Add):
            return distribute_tensor_prod_over_sum.instantiate(
                {x_etc: self.factors[:factor_idx], y_etc: factor.terms, z_etc: self.factors[factor_idx + 1:]})
        elif isinstance(factor, Sum):
            domain = factor.domain
            summand = factor.summand
            index = factor.index
            return distribute_tensor_prod_over_summation.instantiate({x_etc: self.factors[:factor_idx], Operation(
                f, index): summand, S: domain, y: index, z_etc: self.factors[factor_idx + 1:]})
        else:
            raise Exception(
                "Don't know how to distribute tensor product over " + str(factor.__class__) + " factor")

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

# TENSOR_PROD = Literal(pkg, 'TENSOR_PROD', {STRING: r'otimes', LATEX: r'\otimes'}, operation_maker = lambda operands : TensorProd(*operands))


class TensorExp(Operation):
    '''
    '''

    # the literal operator of the TensorExp operation
    _operator_ = Literal(string_format=r'otimes', latex_format=r'{\otimes}',
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

    def do_reduced_simplification(self, assumptions=frozenset()):
        '''
        For the trivial cases of a one exponent, derive and return
        this tensor-exponentiated expression equated with a simplified
        form. Assumptions may be necessary to deduce necessary
        conditions for the simplification.
        '''
        from proveit.numbers.common import zero, one
        from axioms import tensor_exp_one
        if self.exponent == one:
            return tensor_exp_one.instantiate({x: self.base})
            raise ValueError('Only trivial simplification is implemented '
                             '(tensor exponent of one).')


# TENSOR_EXP = Literal(pkg, 'TENSOR_EXP', {STRING: r'^otimes', LATEX: r'^{\otimes}'}, operation_maker = lambda operands : TensorExp(*operands))

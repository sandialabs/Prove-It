from proveit import (Judgment, defaults, relation_prover, equality_prover, 
                     Literal, Operation, Lambda,
                     prover, TransRelUpdater, SimplificationDirectives)
from proveit import a, b, c, d, e, f, i, j, k, A, K, Q, U, V, W, alpha
from proveit.logic import Equals, InClass
from proveit.abstract_algebra.generic_methods import (
        apply_association_thm, apply_disassociation_thm)
from proveit.linear_algebra import (VecSpaces, ScalarMult, VecAdd, VecSum,
                                    deduce_as_vec_space)

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

    _simplification_directives_ = SimplificationDirectives(
            ungroup = True, factor_scalars=True)

    def __init__(self, *operands, styles=None):
        Operation.__init__(self, TensorProd._operator_, operands,
                           styles=styles)
        self.factors = self.operands

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this TensorProd
        expression assuming the operands have been simplified.
        
        Currently deals only with:
        (1) simplifying a TensorProd(x) (i.e. a TensorProd with a
            single operand x) to x itself. For example,
            TensorProd(x) = x.
        (2) Ungrouping nested tensor products.
        (3) Factoring out scalars.
        '''

        if self.operands.is_single():
            from . import unary_tensor_prod_def
            _V = VecSpaces.known_vec_space(self.operand)
            _K = VecSpaces.known_field(_V)
            return unary_tensor_prod_def.instantiate(
                {K:_K, V:_V, A:self.operands[0]}, preserve_all=True)

        # for convenience updating our equation:
        expr = self
        eq = TransRelUpdater(expr)
        
        if TensorProd._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested additions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                # print("n, length", n, length)
                if isinstance(operand, TensorProd):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, preserve_all=True))
                length = expr.operands.num_entries()
                _n += 1
        
        if TensorProd._simplification_directives_.factor_scalars:
            # Next, pull out scalar factors
            for _k, operand in enumerate(expr.operands):
                if isinstance(operand, ScalarMult):
                    # Just pull out the first one we see and let
                    # recursive simplifications take care of any more.
                    expr = eq.update(expr.scalar_factorization(_k))
                    break
        
        # Future processing possible here.
        return eq.relation

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Deduce that the tensor product of vectors is in a vector space
        which is the tensor product of corresponding vectors spaces.
        '''
        from . import tensor_prod_is_in_tensor_prod_space
        _a = self.operands
        _i = _a.num_elements()
        _K = VecSpaces.get_field(field)
        vec_spaces = VecSpaces.known_vec_spaces(self.operands, field=_K)
        return tensor_prod_is_in_tensor_prod_space.instantiate(
                {K: _K, i: _i, V: vec_spaces, a: _a})      
        
    @relation_prover
    def deduce_as_vec_space(self, **defaults_config):
        '''
        Deduce that the tensor product of vector spaces is a vector
        space (the space containing tensor products over any vectors
        within the corresponding vector spaces).
        '''
        from . import tensor_prod_of_vec_spaces_is_vec_space
        _V = self.operands
        _i = _V.num_elements()
        _K = None
        for operand in self.operands:
            class_membership = deduce_as_vec_space(operand)
            field = class_membership.expr.domain.field
            if _K is None:
                _K = field
            elif _K != field:
                raise ValueError("Vector spaces in tensor product have "
                                 "different fields, %s ≠ %s"
                                 %(_K, field))
        return tensor_prod_of_vec_spaces_is_vec_space.instantiate(
                {K: _K, i: _i, V: _V})

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, *, field=None, 
                    **defaults_config):
        '''
        Given vector operands, deduce that this expression is equal 
        to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (a ⊗ b ⊗ ... ⊗ y ⊗ z) = 
            (a ⊗ b ... ⊗ (l ⊗ ... ⊗ m) ⊗ ... ⊗ y ⊗ z)
        
        For this to work, the operands must be known to be in
        vector spaces of a common field.  If the field is not specified,
        then VecSpaces.default_field is used.
        '''
        from . import tensor_prod_association
        _V = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(_V)
        eq = apply_association_thm(
            self, start_idx, length, tensor_prod_association,
            repl_map_extras={K:_K, V:_V}).derive_consequent()
        return eq.with_wrapping_at()

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, *, field=None, 
                       **defaults_config):
        '''
        Given vector operands, deduce that this expression is equal 
        to a form in which the operand
        at index idx is no longer grouped together.
        For example, (a ⊗ b ... ⊗ (l ⊗ ... ⊗ m) ⊗ ... ⊗ y⊗ z) 
            = (a ⊗ b ⊗ ... ⊗ y ⊗ z)
        
        For this to work, the operands must be known to be in
        vector spaces of a common field.  If the field is not specified,
        then VecSpaces.default_field is used.
        '''
        from . import tensor_prod_disassociation
        _V = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(_V)
        eq = apply_disassociation_thm(
                self, idx, tensor_prod_disassociation,
                repl_map_extras={K:_K, V:_V}).derive_consequent()
        return eq.with_wrapping_at()

    @equality_prover('distributed', 'distribute')
    def distribution(self, idx, *, field=None,
                     **defaults_config):
        '''
        Given a TensorProd operand at the (0-based) index location
        'idx' that is a vector sum or summation, prove the distribution
        over that TensorProd factor and return an equality to the 
        original TensorProd. For example, we could take the TensorProd
            tens_prod = TensorProd(a, b+c, d)
        and call tens_prod.distribution(1) to obtain:
            |- TensorProd(a, b+c, d) =
               TensorProd(a, b, d) + TensorProd(a, c, d)
        '''
        from . import (tensor_prod_distribution_over_add,
                       tensor_prod_distribution_over_summation)
        _V = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(_V)
        sum_factor = self.operands[idx]
        _a = self.operands[:idx]
        _c = self.operands[idx+1:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        if isinstance(sum_factor, VecAdd):
            _b = sum_factor.operands
            _V = VecSpaces.known_vec_space(self, field=field)
            _j = _b.num_elements()
            impl = tensor_prod_distribution_over_add.instantiate(
                {K:_K, i:_i, j:_j, k:_k, V:_V, a:_a, b:_b, c:_c})
            return impl.derive_consequent().with_wrapping_at()
        elif isinstance(sum_factor, VecSum):
            _b = sum_factor.indices
            _j = _b.num_elements()
            _f = Lambda(sum_factor.indices, sum_factor.summand)
            _Q = Lambda(sum_factor.indices, sum_factor.condition)
            impl = tensor_prod_distribution_over_summation.instantiate(
                    {K:_K, f:_f, Q:_Q, i:_i, j:_j, k:_k, 
                     V:_V, a:_a, b:_b, c:_c})
            return impl.derive_consequent().with_wrapping_at()
        else:
            raise ValueError(
                "Don't know how to distribute tensor product over " +
                str(sum_factor.__class__) + " factor")

    @equality_prover('scalar_factorized', 'factor_scalar')
    def scalar_factorization(self, idx=None, *, field=None,
                             **defaults_config):
        '''
        Prove the factorization of a scalar from one of the tensor 
        product operands and return the original tensor product equal 
        to the factored version.  If idx is provided, it will specify 
        the (0-based) index location of the ScalarMult operand with the
        multiplier to factor out.  If no idx is provided, the first 
        ScalarMult operand will be targeted.
        
        For example,
            TensorProd(a, ScalarMult(c, b), d).factorization(1)
        returns
            |- TensorProd(a, ScalarMult(c, b), d) =
               c TensorProd(a, b, d)
        
        As a prerequisite, the operands must be known to be vectors in
        vector spaces over a common field which contains the scalar
        multiplier being factored.  If the field is not specified,
        then VecSpaces.default_field is used.
        '''
        from . import factor_scalar_from_tensor_prod
        if idx is None:
            for _k, operand in enumerate(self.operands):
                if isinstance(operand, ScalarMult):
                    idx = _k
                    break
        elif idx < 0:
            # use wrap-around indexing
            idx = self.operand.num_entries() + idx
        if not isinstance(self.operands[idx], ScalarMult):
            raise TypeError("Expected the 'operand' and 'operand_idx' to be "
                            "a ScalarMult")            
        _V = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(_V)
        _alpha = self.operands[idx].scalar
        _a = self.operands[:idx]
        _b = self.operands[idx].scaled
        _c = self.operands[idx+1:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        impl = factor_scalar_from_tensor_prod.instantiate(
                {K:_K, alpha:_alpha, i:_i, k:_k, V:_V, a:_a, b:_b, c:_c})
        return impl.derive_consequent().with_wrapping_at()

    @staticmethod
    def _check_tensor_equality(tensor_equality, allow_unary=False):
        '''
        Check that the tensor_equality has the appropriate form.
        '''
        if isinstance(tensor_equality, Judgment):
            tensor_equality = tensor_equality.expr
        if not isinstance(tensor_equality, Equals):
            raise ValueError("tensor_equality should be an Equals expression; "
                             " instead received: {}.".format(tensor_equality))
        if (not isinstance(tensor_equality.lhs, TensorProd) or
            not isinstance(tensor_equality.rhs, TensorProd)):
            if allow_unary:
                # If we are allowing the sides to by unary tensor 
                # products, make it so.
                tensor_equality = Equals(TensorProd(tensor_equality.lhs),
                                         TensorProd(tensor_equality.rhs))
            else:
                raise ValueError(
                        "tensor_equality should be an Equals expression of "
                        "tensor products; "
                        "instead received: {}.".format(tensor_equality))
        if (tensor_equality.lhs.factors.num_elements() !=
            tensor_equality.rhs.factors.num_elements()):
            raise ValueError(
                    "tensor_equality should be an Equals expression of tensor "
                    "products with the same number of factors; "
                    "instead received: {}.".format(tensor_equality))
        return tensor_equality

    @staticmethod
    @prover
    def remove_vec_on_both_sides_of_equals(tensor_equality, idx,
                                           rhs_idx = None, *,
                                           field = None,
                                           **defaults_config):
        '''
        From an equality with tensor products of vectors on
        both sides, derive a similar equality but with the vector 
        operand removed at the particular given zero-based index (idx).
        A different index may be specified for the right side as the 
        left side by setting rhs_idx (i.e., if entries don't line up 
        due to differences of ExprRange entries), but the default will
        be to use the same.
        '''
        from . import remove_vec_on_both_sides_of_equality
        # First check various characteristics of the tensor_equality
        TensorProd._check_tensor_equality(tensor_equality)
        if idx < 0:
            # use wrap-around indexing
            idx = tensor_equality.num_entries() + idx
        if rhs_idx is None:
            rhs_idx = idx # use the same index on both sides by default
        _a = tensor_equality.lhs.operands[:idx]
        _b = tensor_equality.lhs.operands[idx]
        _c = tensor_equality.lhs.operands[idx+1:]
        _d = tensor_equality.rhs.operands[:rhs_idx]
        _e = tensor_equality.rhs.operands[rhs_idx]
        _f = tensor_equality.rhs.operands[rhs_idx+1:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        vec_space = VecSpaces.known_vec_space(tensor_equality.lhs, 
                                              field=field)
        _K = VecSpaces.known_field(vec_space)
        _U = VecSpaces.known_vec_spaces(_a, field=_K)
        _V = VecSpaces.known_vec_space(_b, field=_K)
        _W = VecSpaces.known_vec_spaces(_c, field=_K)
        impl = remove_vec_on_both_sides_of_equality.instantiate(
                {K:_K, i:_i, k:_k, U:_U, V:_V, W:_W, 
                 a:_a, b:_b, c:_c, d:_d, e:_e, f:_f})
        return impl.derive_consequent().with_mimicked_style(tensor_equality)

    @staticmethod
    @prover
    def insert_vec_on_both_sides_of_equals(tensor_equality, idx, vec,
                                           rhs_idx = None, *,
                                           field = None, 
                                           **defaults_config):
        '''
        From an equality with tensor products of vectors on
        both sides, derive a similar equality but with a vector 
        operand inserted at the particular given zero-based index (idx).
        A different index may be specified for the right side as the 
        left side by setting rhs_idx (i.e., if entries don't line up 
        due to differences of ExprRange entries), but the default will
        be to use the same.
        '''
        from . import insert_vec_on_both_sides_of_equality
        # First check various characteristics of the tensor_equality
        tensor_equality = TensorProd._check_tensor_equality(
                tensor_equality, allow_unary=True)
        if idx < 0:
            # use wrap-around indexing
            idx = tensor_equality.num_entries() + idx
        if rhs_idx is None:
            rhs_idx = idx # use the same index on both sides by default
        _a = tensor_equality.lhs.operands[:idx]
        _b = vec
        _c = tensor_equality.lhs.operands[idx:]
        _d = tensor_equality.rhs.operands[:rhs_idx]
        _e = tensor_equality.rhs.operands[rhs_idx:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        vec_space = VecSpaces.known_vec_space(tensor_equality.lhs, 
                                              field=field)
        _K = VecSpaces.known_field(vec_space)
        _U = VecSpaces.known_vec_spaces(_a, field=_K)
        _V = VecSpaces.known_vec_space(_b, field=_K)
        _W = VecSpaces.known_vec_spaces(_c, field=_K)
        impl = insert_vec_on_both_sides_of_equality.instantiate(
                {K:_K, i:_i, k:_k, U:_U, V:_V, W:_W, 
                 a:_a, b:_b, c:_c, d:_d, e:_e})
        return impl.derive_consequent().with_mimicked_style(tensor_equality)


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

from proveit import (Judgment, defaults, ExprRange, relation_prover, 
                     equality_prover, auto_equality_prover,
                     Literal, Operation, Lambda, 
                     UnsatisfiedPrerequisites,
                     prover, TransRelUpdater, SimplificationDirectives)
from proveit import a, b, c, d, e, f, i, j, k, A, K, Q, U, V, W, alpha
from proveit.logic import Equals, InClass, SetMembership, SubsetEq
from proveit.numbers import one
from proveit.abstract_algebra.generic_methods import (
        apply_association_thm, apply_disassociation_thm)
from proveit.linear_algebra import (
        VecSpaces, ScalarMult, VecOperation, VecAdd, VecSum,
        deduce_as_vec_space, deduce_canonically_equal)

pkg = __package__


class TensorProd(VecOperation):
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

    def membership_object(self, element):
        # This is a little bit odd, where a TensorProd can
        # itself be an element of a TensorProd
        from .tensor_prod_membership import TensorProdMembership
        return TensorProdMembership(element, self)

    def _build_canonical_form(self):
        '''
        Returns the canonical form of this TensorProd, pulling out
        and combining all scalars.
        '''
        from proveit.numbers import Mult
        scalars = []
        canonical_factors = []
        for factor in self.factors:
            factor = factor.canonical_form()
            if isinstance(factor, ScalarMult):
                scalars.append(factor.scalar)
                factor = factor.scaled
            if isinstance(factor, TensorProd):
                canonical_factors.extend(factor.factors)
            else:
                canonical_factors.append(factor)
        if len(scalars) == 0:
            return TensorProd(*canonical_factors)
        return ScalarMult(Mult(*scalars), 
                          TensorProd(*canonical_factors)).canonical_form()

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
                if isinstance(operand, TensorProd):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, preserve_all=True))
                length = expr.operands.num_entries()
                _n += 1
        
        if TensorProd._simplification_directives_.factor_scalars:
            # Next, pull out scalar factors
            try:
                VecSpaces.known_vec_space(self)
            except (ValueError, UnsatisfiedPrerequisites):
                # Don't pull out scalar factors if the operands aren't
                # known to be in vector spaces (e.g., maybe the operands
                # are vectors spaces themselves).
                return eq.relation
            expr = eq.update(expr.scalars_factorization())
        
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
        membership = tensor_prod_is_in_tensor_prod_space.instantiate(
                {K: _K, i: _i, V: vec_spaces, a: _a})      
        if vec_space is not None and membership.domain != vec_space:
            sub_rel = SubsetEq(membership.domain, vec_space)
            return sub_rel.derive_superset_membership(self)
        return membership
        
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
            if isinstance(operand, ExprRange):
                assumption = operand.parameter_condition()
                assumptions = (
                            defaults.assumptions + (assumption ,))
                class_membership = deduce_as_vec_space(
                        operand.body, assumptions=assumptions)
            else:
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
        Given vector operands, or all CartExp operands, deduce that
        this expression is equal to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, calling
        (a ⊗ b ⊗ ... ⊗ y ⊗ z).association(l, m-l+1)
        would return
        |- (a ⊗ b ⊗ ... ⊗ y ⊗ z) = 
            (a ⊗ b ... ⊗ (l ⊗ ... ⊗ m) ⊗ ... ⊗ y ⊗ z)
        Or calling (R3 ⊗ R3 ⊗ R3).associate(1, 2) would return
        |- (R3 ⊗ R3 ⊗ R3) = (R3 ⊗ (R3 ⊗ R3))
        
        For this to work in the vectors case, the vector operands must
        be known to be in vector spaces of a common field.  If the
        field is not specified, then VecSpaces.default_field is used.
        For this to work in the case of CartExp operands, all operands
        must be (recursively) CartExps and each must be known to be
        a vector space.
        '''
        # ORIGINAL BELOW before augmenting for CartExp cases
        # from . import tensor_prod_association
        # _V = VecSpaces.known_vec_space(self, field=field)
        # _K = VecSpaces.known_field(_V)
        # eq = apply_association_thm(
        #     self, start_idx, length, tensor_prod_association,
        #     repl_map_extras={K:_K, V:_V}).derive_consequent()
        # return eq.with_wrapping_at()

        if not TensorProd.all_ops_are_cart_exp(self):
            from . import tensor_prod_association
            _vspace = VecSpaces.known_vec_space(self, field=field)
            _K = VecSpaces.known_field(_vspace)
            _U = VecSpaces.known_vec_spaces(self.factors[:start_idx], 
                                            field=_K)
            _V = VecSpaces.known_vec_spaces(
                self.factors[start_idx:start_idx+length], field=_K)
            _W = VecSpaces.known_vec_spaces(
                self.factors[start_idx+length:], field=_K)
            eq = apply_association_thm(
                self, start_idx, length, tensor_prod_association,
                repl_map_extras={K:_K, U:_U, V:_V, W:_W})
            return eq.with_wrapping_at()
        else:
            from . import tensor_prod_vec_space_association
            if field is None:
                _K = VecSpaces.known_field(self.operands[0])
            else:
                _K = field
            eq = apply_association_thm(
                self, start_idx, length, tensor_prod_vec_space_association,
                repl_map_extras={K:_K})
            return eq.with_wrapping_at()

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, *, field=None, 
                       **defaults_config):
        '''
        Given vector operands, or all CartExp operands, deduce that
        this expression is equal to a form in which operand at index
        idx is no longer grouped together.
        For example, calling
        (a ⊗ b ⊗ ... (l ⊗ ... ⊗ m) ... ⊗ y ⊗ z).association(l-1)
        would return
        |- (a ⊗ b ⊗ ... (l ⊗ ... ⊗ m) ... ⊗ y ⊗ z) = 
            (a ⊗ b ⊗ ... ⊗ l ⊗ ... ⊗ m ⊗ ... ⊗ y ⊗ z)
        Or calling (R3 ⊗ (R3 ⊗ R3)).disassociate(1) would return
        |- (R3 ⊗ (R3 ⊗ R3)) = (R3 ⊗ R3 ⊗ R3) 
        
        For this to work in the vectors case, the vector operands must
        be known to be in vector spaces of a common field.  If the
        field is not specified, then VecSpaces.default_field is used.
        For this to work in the case of CartExp operands, all operands
        must be (recursively) CartExps and each must be known to be
        a vector space.
        '''
        # ORIGINAL BELOW before augmenting for CartExp cases
        # from . import tensor_prod_disassociation
        # _V = VecSpaces.known_vec_space(self, field=field)
        # _K = VecSpaces.known_field(_V)
        # eq = apply_disassociation_thm(
        #         self, idx, tensor_prod_disassociation,
        #         repl_map_extras={K:_K, V:_V}).derive_consequent()
        # return eq.with_wrapping_at()

        if not TensorProd.all_ops_are_cart_exp(self):
            from . import tensor_prod_disassociation
            _vspace = VecSpaces.known_vec_space(self, field=field)
            _K = VecSpaces.known_field(_vspace)
            _U = VecSpaces.known_vec_spaces(self.factors[:idx], 
                                            field=_K)
            nested_group = self.operands[idx]
            if not isinstance(nested_group, TensorProd):
                raise ValueError(
                    "Cannot disassociate index %d from %s."
                    %(idx, self))
            _V = VecSpaces.known_vec_spaces(
                nested_group.factors, field=_K)
            _W = VecSpaces.known_vec_spaces(
                self.factors[idx+1:], field=_K)
            eq = apply_disassociation_thm(
                    self, idx, tensor_prod_disassociation,
                    repl_map_extras={K:_K, U:_U, V:_V, W:_W})
            return eq.with_wrapping_at()
        else:
            from . import tensor_prod_vec_space_disassociation
            if field is None:
                _K = VecSpaces.known_field(self.operands[0])
            else:
                _K = field
            eq = apply_disassociation_thm(
                    self, idx, tensor_prod_vec_space_disassociation,
                    repl_map_extras={K:_K})
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
            # use preserve_all=True in the following instantiation
            # because the instantiation is an intermediate step;
            # otherwise auto_simplification can over-do things
            impl = tensor_prod_distribution_over_add.instantiate(
                {K:_K, i:_i, j:_j, k:_k, V:_V, a:_a, b:_b, c:_c},
                preserve_all=True)
            return impl.derive_consequent().with_wrapping_at()
        elif isinstance(sum_factor, VecSum):
            _b = sum_factor.indices
            _j = _b.num_elements()
            _f = Lambda(sum_factor.indices, sum_factor.summand)
            _Q = Lambda(sum_factor.indices, sum_factor.condition)
            # use preserve_all=True in the following instantiation
            # because the instantiation is an intermediate step;
            # otherwise auto_simplification can over-do things
            impl = tensor_prod_distribution_over_summation.instantiate(
                    {K:_K, f:_f, Q:_Q, i:_i, j:_j, k:_k, 
                     V:_V, a:_a, b:_b, c:_c}, preserve_all=True)
            return impl.derive_consequent().with_wrapping_at()
        else:
            raise ValueError(
                "Don't know how to distribute tensor product over " +
                str(sum_factor.__class__) + " factor")

    @auto_equality_prover('scalars_factorized', 'factor_scalars')
    def scalars_factorization(self, *, field=None, **defaults_config):
        '''
        Equate this TensorProd with a form that has all of the
        scalar factors pulled out in front.
        '''
        expr = self
        eq = TransRelUpdater(expr)
        
        scalar_mult_indices = []        
        for _k, operand in enumerate(expr.operands):
            if isinstance(operand, ScalarMult):
                scalar_mult_indices.append(_k)

        if len(scalar_mult_indices) == 0:
            return eq.relation # no scalars to factor out.
        
        last_scalar_mult_idx = scalar_mult_indices[-1]
        for _k in scalar_mult_indices:
            if isinstance(expr, ScalarMult):
                expr = expr.inner_expr().scaled
            expr = eq.update(expr.scalar_factorization(_k, field=field))
        
        return eq.relation
        
    @auto_equality_prover('scalar_factorized', 'factor_scalar')
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
        _vspace = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(_vspace)
        _alpha = self.operands[idx].scalar
        _a = self.operands[:idx]
        _b = self.operands[idx].scaled
        _c = self.operands[idx+1:]
        _i = _a.num_elements()
        _k = _c.num_elements()
        _U = VecSpaces.known_vec_spaces(_a, field=_K)
        _V = VecSpaces.known_vec_space(_b, field=_K)
        _W = VecSpaces.known_vec_spaces(_c, field=_K)
        inst = factor_scalar_from_tensor_prod.instantiate(
            {K:_K, alpha:_alpha, i:_i, k:_k, U:_U, V:_V, W:_W,
             a:_a, b:_b, c:_c})
        return inst.with_wrapping_at()
    
    def readily_factorable(self, factor, *, pull):
        '''
        Return True if 'factor' may be easily factored from this
        VecAdd, pulling either to the 'left' or the 'right'.
        If pulling to the 'left', the factor must be at the front
        of any tensor product of vectors.  If pulling to the 'right', 
        the factor must be at the back of any tensor product of vectors.
        '''
        from proveit.linear_algebra import readily_factorable

        # Put the 'self' and the candidate factor in canonical form 
        # which will put scalars in the front.
        canonical_self = self.canonical_form()
        if canonical_self.factors.num_entries()==0:
            return False # Empty tensor product cannot be factored.
        canonical_factor = factor.canonical_form()
        if isinstance(canonical_factor, ScalarMult):
            if not isinstance(canonical_self, ScalarMult):
                # Nothing to factor the scalar from.
                return False
            if not readily_factorable(canonical_self.scalar,
                                      canonical_factor.scalar):
                # Can't factor the scalar part.
                return False
            canonical_factor = canonical_factor.scaled
        if isinstance(canonical_self, ScalarMult):
            # We've addressed any scalar part.
            canonical_self = canonical_self.scaled
        if isinstance(canonical_factor, TensorProd):
            num_factors = canonical_factor.factors.num_entries()            
            if pull == 'left':
                # Try to match the first factors.
                factors_to_match = canonical_self.factors[:num_factors]
            else:
                # Try to match the last factors.
                factors_to_match = canonical_self.factors[-num_factors:]
            return factors_to_match == canonical_factor.factors
        elif pull == 'left':
            # Try to match the first factor.
            return canonical_self.factors[0] == canonical_factor
        elif pull == 'right':
            # Try to match the last factor.
            return canonical_self.factors[-1] == canonical_factor
        else:
            raise ValueError("'pull' must be 'left' or 'right', not %s"
                             %pull)

    @auto_equality_prover('factorized', 'factor')
    def factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, **defaults_config):
        '''
        Factor 'the_factor' from the left of this TensorProd if 
        pull='left' or from the right of the TensorProd if pull='right'.
        The tensor product cannot commute but scalar factors can
        and will shift as necessary.  If group_factors is True,
        'factor' will be grouped (associated).  If group_remainder is
        True, the remainder will be grouped (associated).
        '''
        from proveit.numbers import (
                one, remove_common_factors, compose_product, compose_fraction)
        from proveit.linear_algebra.scalar_multiplication.scalar_mult import (
                extract_scalar_and_scaled)

        # Put the factor in its canonical form and separate out any
        # of its scalar factors.
        factor_scalar, factor_scaled = extract_scalar_and_scaled(the_factor)
        self_cf = self.canonical_form()

        if self_cf == the_factor.canonical_form():
            # Trivial case of factoring the entire ScalarMult.
            return deduce_canonically_equal(self, the_factor, field=field)

        canonical_tensor_prod = (
                self_cf.scaled if isinstance(self_cf, ScalarMult) else
                self_cf)
        assert isinstance(canonical_tensor_prod, TensorProd)
        num_tensor_entries = canonical_tensor_prod.factors.num_entries()
        
        def raise_not_factorable():
            raise ValueError("Unable to factor %s from %s"%(the_factor, self))
        canonical_factor_scaled = factor_scaled.canonical_form()
        if isinstance(canonical_factor_scaled, TensorProd):
            num_to_factor = fanonical_factor_scaled.factors.num_entries()
            if num_to_factor > num_tensor_entries:
                raise_not_factorable() 
            canonical_factors = canonical_factor_scaled.factors.entries
        else:
            num_to_factor = 1
            canonical_factors = (canonical_factor_scaled,)
                
        if pull=='left':
            if (canonical_tensor_prod.factors[:num_to_factor].entries
                    != canonical_factors):
                raise_not_factorable()
            pull_side_factors = self.factors[:num_to_factor]
            far_side_factors = self.factors[num_to_factor:]
        elif pull=='right':
            if (canonical_tensor_prod.factors[num_to_factor:].entries
                    != canonical_factors):
                raise_not_factorable()
            pull_side_factors = reversed(self.factors[num_to_factor:])
            far_side_factors = reversed(self.factors[:num_to_factor])
        else:
            raise ValueError("'pull' must either be 'left' or 'right'.")
                    
        # Find the scalar factors that need to be moved.
        leftover_scalars = []
        for factor in pull_side_factors:
            if isinstance(factor, ScalarMult):
                leftover_scalar = remove_common_factors(factor.scalar, 
                                                        factor_scalar)
                if leftover_scalar != one:
                    leftover_scalars.append(leftover_scalar)
                factor_scalar = remove_common_factors(
                        factor_scalar, factor.scalar)
        # Determine 'remainder' factors.
        remainder_factors = []
        for factor in far_side_factors:
            if isinstance(factor, ScalarMult):
                scalar = remove_common_factors(factor.scalar, 
                                               factor_scalar)
                if scalar == one:
                    remainder_factors.append(factor.scaled)
                else:
                    remainder_factors.append(
                            ScalarMult(scalar, factor.scaled))
                factor_scalar = remove_common_factors(
                        factor_scalar, factor.scalar)
            else:
                remainder_factors.append(factor)
        leftover_scalar = compose_product(*leftover_scalars)
        if factor_scalar != one:
            leftover_scalar = compose_fraction(leftover_scalar, 
                                               factor_scalar)
        assert len(remainder_factors) > 0, (
                "Otherwise, the canonical forms would be equal")
        if leftover_scalar != one:
            if len(remainder_factors)==0:
                raise ValueError(
                        "Vectors must be pulled to the 'right' "
                        "unless it is a portion of a TensorProd")
            the_factors = [the_factor]
            if len(remainder_factors) > 1:
                remainder_factors = [ScalarMult(
                        leftover_scalar, TensorProd(*remainder_factors))]
            elif len(remainder_factors) == 1:
                remainder_factors = [ScalarMult(leftover_scalar,
                                                remainder_factors[0])]
        else:
            the_factors = [the_factor]
            if not group_factors and isinstance(the_factor, TensorProd):
                the_factors = the_factors.factors
            if group_remainder and len(remainder_factors)>1:
                remainder_factors = [TensorProd(*remainder_factors)]
        if pull=='left':
            desired = TensorProd(*the_factors, *remainder_factors)
        else:
            desired = TensorProd(*remainder_factors, *the_factors)
        return deduce_canonically_equal(self, desired, field=field)

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

    @staticmethod
    def all_ops_are_cart_exp(obj):
        '''
        Determine recursively if the expression object obj is a
        CartExp or an expression whose operands are all CartExps or
        themselves expressions whose operands are all CartExps, etc.,
        returning True if so, otherwise returning False.
        Let R3 = CartExp(Real, three) and C3 = CartExp(Complex, three).
        Then, for example, if x = TensorProd(R3, R3), we would have
        x.all_ops_are_cart_exp() = True.
        If x = TensorProd(R3, TensorProd(C3, TensorProd(C3, R3))), we
        would have x.all_ops_are_cart_exp() = True.
        But x = TensorProd(a, b) or x = TensorProd(y, R3), then
        x.all_ops_are_cart_exp() = False
        '''
        from proveit.logic import CartExp
        if isinstance(obj, CartExp):
            return True
        elif not hasattr(obj, 'operands'):
            return False
        else:
            return all([TensorProd.all_ops_are_cart_exp(op)
                        for op in obj.operands])

    @prover
    def compute_norm(self, field=None, **defaults_config):
        '''
        Proves ‖a ⊗ b ⊗ ... ⊗ y ⊗ z‖ = ‖a‖·‖b‖·...·‖y‖·‖z‖.
        '''
        from proveit.logic import EvaluationError
        from . import norm_of_tensor_prod, norm_preserving_tensor_prod
        _a = self.operands
        _i = _a.num_elements()
        _K = VecSpaces.get_field(field)
        vec_spaces = VecSpaces.known_vec_spaces(self.operands, field=_K)
        
        # See if all of the operand normalizations evaluate to one.
        all_norm_one = True
        try:
            for operand in self.operands:
                if isinstance(operand, ExprRange):
                    with defaults.temporary() as tmp_defaults:
                        tmp_defaults.assumptions = defaults.assumptions + (
                                operand.parameter_condition(),)
                        body_norm = operand.body.compute_norm()
                        if body_norm.rhs.evaluated() != one:
                            all_norm_one = False
                            break
                else:
                    if operand.compute_norm().rhs.evaluated() != one:
                        all_norm_one = False
                        break
        except (EvaluationError, NotImplementedError):
            all_norm_one = False
            pass
        if all_norm_one:
            thm = norm_preserving_tensor_prod
        else:
            thm = norm_of_tensor_prod
        return thm.instantiate({K: _K, i: _i, V: vec_spaces, a: _a})            
        

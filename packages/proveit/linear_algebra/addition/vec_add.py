from proveit import (defaults, Literal, ExprRange, ExprTuple, ProofFailure,
                     SimplificationDirectives,
                     UnsatisfiedPrerequisites, prover, relation_prover,
                     equality_prover, TransRelUpdater)
from proveit import a, b, c, i, j, k, n, v, x, y, K, V
from proveit.logic import Equals, InSet
from proveit.numbers import zero, one, Add
from proveit.abstract_algebra import GroupAdd
from proveit.linear_algebra import VecSpaces, VecOperation
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, apply_association_thm,
        apply_disassociation_thm, group_commutation, group_commute,
        generic_permutation, deduce_equality_via_commutation)


class VecAdd(GroupAdd, VecOperation):
    '''
    The VecAdd operation is the default for the addition of vectors
    in a vector space.
    '''
    
    _operator_ = Literal(string_format='+', theory=__file__)
    
    _simplification_directives_ = SimplificationDirectives()

    def __init__(self, *operands, styles=None):
        GroupAdd.__init__(self, VecAdd._operator_,
                          operands, styles=styles)
        self.terms = self.operands

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this ScalarMult
        expression assuming the operands have been simplified.
        
        Handles doubly-nested scalar multiplication.
        '''
        from proveit.numbers import Complex
        if all(InSet(operand, Complex).proven() for operand in self.operands):
            # If the operands are all complex numbers, this will
            # VecAdd will reduce to number Add.
            return self.number_add_reduction()
        return GroupAdd.shallow_simplification(
                self, must_evaluate=must_evaluate)

    def _build_canonical_form(self):
        '''
        Returns a form of this operation in which the operands are 
        in a deterministically sorted order used to determine equal 
        expressions given commutativity of this operation under
        appropriate conditions.
        '''
        return VecAdd(*sorted([operand.canonical_form() for operand 
                              in self.operands.entries], key=hash))

    @equality_prover('number_add_reduced', 'number_add_reduce')
    def number_add_reduction(self, **defaults_config):
        from . import scalar_add_extends_number_add
        _a = self.operands
        _i = _a.num_elements()
        return scalar_add_extends_number_add.instantiate({a:_a, i:_i})

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Prove that this linear combination of vectors is in a vector
        space.  The vector space may be specified or inferred via known
        memberships.  A field for the vector space must be specified.
        '''
        from proveit.linear_algebra import ScalarMult
        
        terms = self.terms
        if vec_space is None:
            vec_space = VecSpaces.common_known_vec_space(terms, field=field)
        field = VecSpaces.known_field(vec_space)
        all_scaled = all((isinstance(term, ScalarMult)
                          or (isinstance(term, ExprRange) and
                              isinstance(term.body, ScalarMult)))
                         for term in terms)
        if all_scaled:
            # Use a linear combination theorem since everything
            # is scaled.
            from proveit.linear_algebra.scalar_multiplication import (
                    binary_lin_comb_closure, lin_comb_closure)
            if terms.is_double():
                # Special linear combination binary case
                _a, _b = terms[0].scalar, terms[1].scalar
                _x, _y = terms[0].scaled, terms[1].scaled
                return binary_lin_comb_closure.instantiate(
                        {K:field, V:vec_space, a:_a, b:_b, x:_x, y:_y})
            else:
                # General linear combination case
                _a = []
                _x = []
                for term in terms:
                    if isinstance(term, ExprRange):
                        _a.append(ExprRange(term.parameter, term.body.scalar,
                                            term.true_start_index, term.true_end_index))
                        _x.append(ExprRange(term.parameter, term.body.scaled,
                                            term.true_start_index, term.true_end_index))
                    else:
                        _a.append(term.scalar)
                        _x.append(term.scaled)
                _n = terms.num_elements()
                return lin_comb_closure.instantiate(
                        {n:_n, K:field, V:vec_space, a:_a, x:_x})
        else:
            # Use a vector addition closure theorem.
            from . import binary_closure, closure
            if terms.is_double():
                # Special binary case
                return binary_closure.instantiate(
                        {K:field, V:vec_space, x:terms[0], y:terms[1]})
            else:
                # General case
                _n = terms.num_elements()
                return closure.instantiate(
                        {n:_n, K:field, V:vec_space, x:terms})

    @equality_prover('moved', 'move')
    def permutation_move(self, init_idx=None, final_idx=None,
                         **defaults_config):
        '''
        Deduce that this VecAdd expression is equal to a Set
        in which the element at index init_idx has been moved to
        final_idx. For example, a+b+c+d = a+c+b+d via
        init_idx = 1 (i.e. 'b') and final_idx = -2. In traditional
        cycle notation, this corresponds to an index-based cycle
        (init_idx, init_idx+1, ..., final_idx) where
        0 ≤ init_idx ≤ final_idx ≤ n - 1 for a set of size n.
        '''
        from . import (binary_permutation, leftward_permutation,
                                 rightward_permutation)
        terms = self.terms
        vec_space = VecSpaces.common_known_vec_space(terms)
        field = VecSpaces.known_field(vec_space)
        return apply_commutation_thm(
            self, init_idx, final_idx, binary_permutation,
            leftward_permutation, rightward_permutation,
            repl_map_extras={K:field, V:vec_space})

    @equality_prover('swapped', 'swap')
    def permutation_swap(self, idx01=None, idx02=None, **defaults_config):
        '''
        Deduce that this VecAdd expression is equal to a VecAdd in which
        the elements at indices idx01 and idx02 have swapped locations.
        For example,
        (a+b+c+d+e).permutation_swap(2, 4) would return
        |– (a+b+c+d+e) = (a+b+e+d+c)
        '''
        # Before processing, quickly check that:
        # (1) user has specified both idx values;
        # (2) and the idx values are plausible.
        if idx01 is None or idx02 is None:
            raise ValueError("Set.permutation_swap() method expecting the "
                             "individual index locations of the two elements "
                             "to swap, idx01 = {0} and idx02 = {1}".
                             format(idx01, idx02))
        if idx01 is not None and idx02 is not None:
            valid_indices_list = list(range(0, self.operands.num_entries()))
            self._check_subset_indices_weak(valid_indices_list, [idx01, idx02])

        new_order = list(range(0, self.operands.num_entries()))
        new_order[idx01], new_order[idx02] = new_order[idx02], new_order[idx01]

        return self.permutation(new_order=new_order)

    @equality_prover('permuted', 'permute')
    def permutation(self, new_order=None, cycles=None, **defaults_config):
        '''
        Deduce that this VecAdd expression is equal to a Set in which
        the elements at indices 0, 1, …, n-1 have been reordered as
        specified EITHER by the new_order list OR by the cycles list
        parameter. For example,
            (a+b+c+d).permutation_general(new_order=[0, 2, 3, 1])
        and
            (a+b+c+d).permutation_general(cycles=[(1, 2, 3)])
        would both return |- (a+b+c+d) = (a+c+d+b).
        '''
        return generic_permutation(self, new_order, cycles)

    def readily_factorable(self, factor, *, pull):
        '''
        Return True if 'factor' may be easily factored from this
        VecAdd, pulling either to the 'left' or the 'right'.
        If pulling to the 'left', the factor must be at the front
        of any tensor product of vectors.  If pulling to the 'right', 
        the factor must be at the back of any tensor product of vectors.
        '''
        from proveit.linear_algebra import readily_factorable
        if self == factor:
            return True
        for term in self.terms:
            if not readily_factorable(term, factor, pull=pull):
                return False
        return True

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, **defaults_config):
        '''
        Factor 'the_factor' from this sum of vectors.
        
        A scalar factor may be pulled to the 'left', a vector factor
        may be pulled to the 'right', or a portion of a tensor product
        may be pulled to either side.  These are examples for each
        of these cases respectively:
            (a b) x + (a c) y + a z = a (b x + c y + z)
            (a x + b x + c x) = (a + b + c) x
            (a x⊗y⊗z + b y⊗y⊗z + c z⊗y⊗z) = (a x + b y + c z)⊗(y⊗z)
            (a x⊗y⊗z + b y⊗y⊗z + c z⊗y⊗z) = (a x + b y + c z)⊗y⊗z
        
        For the tensor product case, the factors may be grouped or
        not (as shown in the last two examples above, respectively).
        In other cases, grouping will happen regardless.
        The remainders will be grouped regardless for the VecAdd
        case (we ave 'group_remainder' as a parameter just for recursion
        compatibility).
        '''
        from proveit.linear_algebra import TensorProd
        expr = self
        eq = TransRelUpdater(expr)

        if expr.terms.num_entries()==0:
            raise ValueError("Cannot factor from an empty VecAdd")

        group_term_factors = group_factors or (
                not isinstance(the_factor, TensorProd))
        for _i in range(expr.terms.num_entries()):
            term = expr.terms[_i]
            if hasattr(term, 'factorization'):
                expr = eq.update(expr.inner_expr().terms[_i].factorization(
                    the_factor, pull=pull, field=field,
                    group_factors=group_term_factors,
                    group_remainder=True, preserve_all=True))
            else:
                if term.scalar != the_factor:
                    raise ValueError(
                        "Factor, %s, is not present in the term at "
                        "index %d of %s!" %
                        (the_factor, _i, self))
        eq.update(expr.shallow_factorization(
                the_factor, pull=pull, group_factors=group_factors,
                group_remainder=group_remainder, field=field))
        return eq.relation

    @equality_prover('shallow_factorized', 'shallow_factor')
    def shallow_factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, **defaults_config):
        '''
        Perform a factorization at this level (no recursive 
        factorization).  Also see 'factorization' which does include
        recursive factorization.
        '''
        from proveit.linear_algebra import (
                ScalarMult, TensorProd)
        
        _V = vec_space = VecSpaces.common_known_vec_space(
                self.terms, field=field)
        _K = VecSpaces.known_field(vec_space)
        if all(isinstance(term, ScalarMult) and term.scalar == the_factor
               for term in self.terms):
            from proveit.linear_algebra.scalar_multiplication import (
                    factorization_from_vectors)
            # Factoring a scalar.  For example,
            #   a x + a y + a z = a (x + y + z)
            assert pull=='left', ("Scalars must be pulled to the 'left' "
                                  "when factoring from vectors")
            _k = the_factor
            _a = ExprTuple(*[term.scaled for term in self.terms])
            _i = _a.num_elements()
            return factorization_from_vectors.instantiate(
                    {V: _V, K: _K, i: _i, k: _k, a: _a})
        elif all((isinstance(term, ScalarMult) and term.scaled == the_factor
                  or term==the_factor) for term in self.terms):
            # Factoring a vector.  For example, 
            #   (a x + b x + c x) = (a + b + c) x
            from proveit.linear_algebra.scalar_multiplication import (
                    factorization_from_scalars)
            assert pull=='right', ("Vectors must be pulled to the 'right' "
                                   "when factoring from scaled versions")
            _v = the_factor
            _a = []
            replacements = list(defaults.replacements)
            for term in self.terms:
                if term == the_factor:
                    _a.append(one)
                    replacements.append(
                            ScalarMult(one, term).scalar_one_elimination())
                else:
                    assert isinstance(term, ScalarMult) and (
                            term.scaled == _v)
                    _a.append(term.scalar)
            _a = ExprTuple(*_a)
            _i = _a.num_elements()
            return factorization_from_scalars.instantiate(
                    {V: _V, K: _K, i: _i, v: _v, a: _a},
                    replacements=replacements)
        else:
            # The only remaining possibility is factoring a vector
            # to one side of a tensor product.  Examples:
            #   (a x⊗y⊗z + b y⊗y⊗z + c z⊗y⊗z) = (a x + b y + c z)⊗y⊗z
            #   (a z⊗x + b z⊗y + c z⊗z) = z ⊗ (a x + b y + c z)
            #   (a x⊗z + a b y⊗z + a c z⊗z) = (x + b y + c z) ⊗ (a z) 
            #   (a z⊗x + a b z⊗y + a c z⊗z) = (a z) ⊗ (x + b y + c z)
            from proveit.linear_algebra.tensors import (
                    tensor_prod_factorization_from_add)
    
            if not group_factors and isinstance(the_factor, TensorProd):
                num_factor_entries = the_factor.operands.num_entries()
                factor_entries = the_factor.operands.entries
            else:
                num_factor_entries = 1
                factor_entries = (the_factor,)
            if pull == 'left':
                for term in self.terms:
                    if not isinstance(term, TensorProd) or (
                            tuple(term.factors[:num_factor_entries]) != 
                            factor_entries):
                        raise ValueError(
                                "%s not immediately factorable from "
                                "the left of %s"%(the_factor, term))
                _k = zero # right side is empty
                # the actual factor operands
                _a = ExprTuple(*factor_entries)
                # middle has the remainders
                _b = ExprTuple(*[term.factors[-1] for term in self.terms])
                # the other side is empty
                _c = ()
                _i = _a.num_elements()
            elif pull == 'right':
                for term in self.terms:
                    if not isinstance(term, TensorProd) or (
                            tuple(term.factors[-num_factor_entries:]) !=
                            factor_entries):
                        raise ValueError(
                                "%s not immediately factorable from "
                                "the right of %s"%(the_factor, term))
                _i = zero  # left side is empty
                # left side is empty
                _a = ()
                # middle has the remainders
                _b = ExprTuple(*[term.factors[0] for term in self.terms])
                # right side has the factor
                _c = ExprTuple(*factor_entries)
                _k = _c.num_elements()
            _j = _b.num_elements()
            return tensor_prod_factorization_from_add.instantiate(
                    {V: _V, K: _K, i: _i, j: _j, k: _k,
                     a: _a, b: _b, c: _c}).derive_consequent()

    @prover
    def compute_norm(self, **defaults_config):
        '''
        Proves ‖x + y‖ = sqrt(‖x‖^2 + ‖y‖^2) if the inner product 
        of x and y is zero.
        '''
        from proveit.linear_algebra import InnerProd, ScalarMult
        from . import norm_of_sum_of_orthogonal_pair
        if self.operands.is_double():
            _a, _b = self.operands
            _x = _a.scaled if isinstance(_a, ScalarMult) else _a
            _y = _b.scaled if isinstance(_b, ScalarMult) else _b
            if Equals(InnerProd(_x, _y), zero).proven():
                vec_space = VecSpaces.known_vec_space(_a)
                field = VecSpaces.known_field(vec_space)
                return norm_of_sum_of_orthogonal_pair.instantiate(
                        {K:field, V:vec_space, a:_a, b:_b})                    
        raise NotImplementedError(
                "VecAdd.compute_norm is only implemented for an "
                "orthogonal pair of vectors")

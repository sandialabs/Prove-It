from proveit import (defaults, free_vars, Literal, Function, Lambda, 
                     ExprTuple,
                     SimplificationDirectives,
                     relation_prover, equality_prover,
                     TransRelUpdater, UnsatisfiedPrerequisites)
from proveit import a, b, c, f, i, j, k, v, K, Q, V
from proveit.logic import InSet
from proveit.numbers import zero, one, Interval, Mult
from proveit.abstract_algebra import GroupSum 
from proveit.linear_algebra import VecSpaces, VecOperation

class VecSum(GroupSum, VecOperation):
    '''
    Denote general summation over a set of elements of any field in 
    analogy to number summation.
    '''
    
    # operator of the Sum operation.
    _operator_ = Literal(string_format='Sum',  latex_format=r'\sum',
                         theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            pull_out_index_indep_factors=True)

    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, VecSum._operator_, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)

    def _build_canonical_form(self):
        '''
        Returns a canonical form of this VecSum with any 
        index-independent scalar factors pulled out in front.
        '''
        from proveit.linear_algebra import ScalarMult
        canonical_summand = self.summand.canonical_form()
        if isinstance(canonical_summand, ScalarMult):
            # Pull any index-independent scalar factors in front.
            scalar = canonical_summand.scalar
            index_dep_scalar_factors = []
            index_indep_scalar_factors = []
            if free_vars(scalar).isdisjoint(self.indices):
                index_dep_scalar_factors = []
                index_indep_scalar_factors = [scalar]
            elif isinstance(scalar, Mult):
                for scalar_factor in scalar.factors:
                    if free_vars(scalar_factor).isdisjoint(self.indices):
                        index_indep_scalar_factors.append(scalar_factor)
                    else:
                        index_dep_scalar_factors.append(scalar_factor)
            else:                
                index_dep_scalar_factors = [scalar]
                index_indep_scalar_factors = []
            if len(index_indep_scalar_factors) > 0:
                # Pulling out some index-independent scalar factors.
                if len(index_dep_scalar_factors) > 0:
                    # Keeping some index-dependent scalar factors
                    # within the VecSum.
                    canonical_summand = ScalarMult(
                            Mult(*index_dep_scalar_factors),
                            canonical_summand.scaled).canonical_form()
                else:
                    canonical_summand = canonical_summand.scaled
                # Build/return the ScalarMult with the VecSum.
                vec_sum = VecSum(self.indices, canonical_summand,
                      conditions=self.conditions.canonical_form())
                return ScalarMult(
                        Mult(*index_dep_scalar_factors),
                        vec_sum).canonical_form()
        # Build the canonical VecSum.
        return VecSum(self.indices, canonical_summand,
                      conditions=self.conditions.canonical_form())

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this VecSum
        expression assuming the operands have been simplified.
        For the trivial case of summing over only one item (currently
        implemented just for a Interval where the endpoints are equal),
        derive and return this vector summation expression equated with
        the simplified form of the single term.
        Also reduce the VecSum to a number Sum if applicable.
        '''
        from proveit.numbers import Complex
        from . import vec_sum_single
        if (isinstance(self.domain,Interval) and
                self.domain.lower_bound == self.domain.upper_bound):
            # Reduce singular summation.
            if hasattr(self, 'index'):
                return vec_sum_single.instantiate(
                    {Function(v, self.index): self.summand,
                     a: self.domain.lower_bound})
        inner_assumptions = defaults.assumptions + self.conditions.entries
        if hasattr(self.summand, 'deduce_in_number_set'):
            # Maybe we can reduce the VecSum to a number Sum.
            self.summand.deduce_in_number_set(
                    Complex, assumptions=inner_assumptions)
        if InSet(self.summand, Complex).proven(assumptions=inner_assumptions):
            # If the operands are all complex numbers, this
            # VecAdd will reduce to number Add.
            return self.number_sum_reduction()
        if VecSum._simplification_directives_.pull_out_index_indep_factors:
            return self.factors_extraction()
        return GroupSum.shallow_simplification(
                self, must_evaluate=must_evaluate)

    @equality_prover('number_sum_reduced', 'number_sum_reduce')
    def number_sum_reduction(self, **defaults_config):
        from . import scalar_sum_extends_number_sum
        _b = self.indices
        _f = Lambda(_b, self.summand)
        _Q = Lambda(_b, self.condition)
        _j = _b.num_elements()
        impl = scalar_sum_extends_number_sum.instantiate(
                {j:_j, b:_b, f:_f, Q:_Q})
        return impl.derive_consequent()

    @equality_prover('vec_sum_eliminated', 'vec_sum_eliminate')
    def vec_sum_elimination(self, field=None, **defaults_config):
        '''
        For a VecSum in which the summand does not depend on the 
        summation index, return an equality between this VecSum and
        the equivalent expression in which the VecSum is eliminated.
        For example, suppose self = VecSum(i, v, Interval(2, 4)).
        Then self.vec_sum_elimination() would return
        |- self = 3*v
        where the 3*v is actually ScalarMult(3, v).
        The method works only for a VecSum over a single summation
        index, and simply returns self = self if the VecSum elimination
        is not possible due to the summand being dependent on the
        index of summation.
        '''

        expr = self
        eq = TransRelUpdater(expr)

        if free_vars(expr.summand).isdisjoint(expr.indices):
            vec_space_membership = expr.summand.deduce_in_vec_space(
                field=field,
                assumptions = defaults.assumptions + expr.conditions.entries)
            _V_sub = vec_space_membership.domain
            _K_sub = VecSpaces.known_field(_V_sub)
            _j_sub = expr.condition.domain.lower_bound
            _k_sub = expr.condition.domain.upper_bound
            _v_sub = expr.summand
            from proveit.linear_algebra.addition import vec_sum_of_constant_vec
            eq.update(vec_sum_of_constant_vec.instantiate(
                    {V: _V_sub, K: _K_sub, j: _j_sub, k: _k_sub, v: _v_sub}))

        else:
            print("VecSum cannot be eliminated. The summand {0} appears "
                  "to depend an index of summation {1}".
                  format(expr.summand, expr.indices))

        return eq.relation

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field=None,
                            **defaults_config):
        '''
        Prove that this vector summation is in a vector space.
        '''
        from . import summation_closure
        if vec_space is None:
            with defaults.temporary() as tmp_defaults:
                tmp_defaults.assumptions = (defaults.assumptions + 
                                            self.conditions.entries)
                vec_space = VecSpaces.known_vec_space(self.summand, 
                                                      field=field)

        _V = vec_space
        _K = VecSpaces.known_field(_V)
        _b = self.indices
        _j = _b.num_elements()
        _f = Lambda(self.indices, self.summand)
        if not hasattr(self, 'condition'):
            print(self)
        _Q = Lambda(self.indices, self.condition)
        return summation_closure.instantiate(
                {j:_j, K:_K, f:_f, Q:_Q, V:_V, b:_b}).derive_consequent()

    @equality_prover('shifted', 'shift')
    def shifting(self, shift_amount, **defaults_config):
        '''
        Shift the summation indices by the shift_amount, and shift
        the summand by a corresponding compensating amount, deducing
        and returning the equivalence of this summation with the
        index-shifted version.
        This shift() method is implemented only for a VecSum with a
        single index and only when the domain is an integer Interval.
        Eventually this should also be implemented for domains of
        Natural, NaturalPos, etc.
        Example: Let S = VecSum(i, Vec(k), Interval(0, 10)).
        Then S.shift(one) will return the equality
        |- S = VecSum(i, Vec(k-1), Interval(1, 11)),
        where we are using Vec(i) to denote some vector as a function
        of the index i (it might for example be a Ket(i) or similar
        object).
        '''
        if not hasattr(self, 'index'):
            raise NotImplementedError(
                "VecSum.shifting() only implemented for vector summations "
                "with a single index over an Integer Interval. The sum {0} "
                "has indices {1}.".format(self, self.indices))
        # The following constraint can eventually be modified to deal
        # with a domain like all Natural … but for now limited to
        # integer Interval domain.
        if not isinstance(self.domain, Interval):
            raise NotImplementedError(
                "VecSum.shifting() only implemented for vector summations "
                "with a single index over an Integer Interval. The sum {0} "
                "has domain {1}."
                .format(self, self.domain))

        from . import vec_sum_index_shift

        _v, _a, _b, _c = vec_sum_index_shift.all_instance_params()
        _i = vec_sum_index_shift.instance_expr.instance_expr.lhs.index

        _i_sub = self.index
        _a_sub = self.domain.lower_bound
        _b_sub = self.domain.upper_bound
        _c_sub = shift_amount

        _v_op, _v_op_sub = Function(_v, self.index), self.summand

        return vec_sum_index_shift.instantiate(
            {_v_op: _v_op_sub, _i: _i_sub, _a: _a_sub, _b: _b_sub, _c: _c_sub})

    @equality_prover('partitioned', 'partition')
    def partitioning(self, split_index, side='after', **defaults_config):
        r'''
        Partition or split a vector summation over one integral
        Interval {a ... c} into two vector summations and return the
        equality between the original and the VecAdd sum of the two
        new vector summations.
        If side == 'after', it splits into a vector summation over
        {a ... split_index} plus a vector summation over
        {split_index+1 ... c}.
        If side == 'before', it splits into a vector summation over
        {a ... split_index-1} plus a vector summation over
        {split_index ... c},
        deducing and returning the equivalence of the original vector
        summation with the split version. When the simplify_idx is True,
        a shallow simplification is applied to the new indices (for
        example, a new index of i = 4 + 1 may be expressed as i = 5).
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This partitioning() method is implemented only for a VecSum with
        a single index and only when the domain is an integer Interval.
        Eventually this should also be implemented for domains of
        Natural, NaturalPos, etc.
        As special cases, split_index==a with side == 'after' splits
        off the first single term.  Also, split_index==c with
        side == 'before' splits off the last single term.
        Example usage: Let S = VecSum(i, Vec(i+2), Interval(0, 10)).
        Then S.partition(four, side='after') will return
        |- S = VecSum(i, Vec(i+2), Interval(0, 4)) +
               VecSum(i, i+2, Interval(5, 10))
        '''
        # The following constraint can eventually be modified to allow
        # a domain like Natural or NaturalPos, but for now limited
        # to integer Interval domain.
        if (not isinstance(self.domain, Interval) or
                not hasattr(self, 'index')):
            raise NotImplementedError(
                "VecSum.partition() only implemented for summations with "
                "a single index over an integer Interval. The sum {} has "
                "indices {} and domain {}."
                .format(self, self.indices, self.domain))

        # Special cases: splitting off last or first item
        if side == 'before' and self.domain.upper_bound == split_index:
            return self.partitioning_last()
        if side == 'after' and self.domain.lower_bound == split_index:
            return self.partitioning_first()

        _i_sub = self.index
        _a_sub = self.domain.lower_bound
        _b_sub = split_index
        _c_sub = self.domain.upper_bound
        _v_op, _v_op_sub = Function(v, self.index), self.summand

        from . import vec_sum_split_after, vec_sum_split_before
        sum_split = (
            vec_sum_split_after if side == 'after' else vec_sum_split_before)
        return sum_split.instantiate(
                {_v_op: _v_op_sub, a: _a_sub, b: _b_sub, c: _c_sub, i: _i_sub})

    @equality_prover('partitioned_last', 'partition_last')
    def partitioning_last(self, **defaults_config):
        '''
        Split a vector summation over an integral Interval {a ... c}
        into a vector sum of: a new summation over the integral
        Interval {a ... (c-1)} and the final term evaluated at the
        upper bound, deducing and returning the equivalence of the
        original vector summation with the new split version.
        The default uses auto_simplify=True to apply a shallow
        simplification to the new indices (for example,
        a new index of i = 4 + 1 may be expressed as i = 5) and to the
        upper term that has been peeled off by itself.
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This partitioning_last() method is implemented only for a VecSum
        with a single index and only when the domain is an integer
        Interval. Eventually this should also be implemented for
        domains of Natural, NaturalPos, etc.
        VecSum.partitioning_last() is called from VecSum.partitioning()
        for special cases.
        Example usage: Let S = VecSum(i, Vec(i+2), Interval(0, 10)).
        Then S.partitioning_last() will return the equality judgment
        |- S = VecSum(i, i+2, Interval(0, 9)) + Vec(12)
        '''
        if isinstance(self.domain, Interval) and hasattr(self, 'index'):

            from . import vec_sum_split_last

            _v, _a, _b = vec_sum_split_last.all_instance_params()
            _i = vec_sum_split_last.instance_expr.instance_expr.lhs.index

            _i_sub = self.index
            _a_sub = self.domain.lower_bound
            _b_sub = self.domain.upper_bound
            _v_op, _v_op_sub = Function(_v, self.index), self.summand

            return vec_sum_split_last.instantiate(
                {_v_op: _v_op_sub, _a: _a_sub, _b: _b_sub, _i: _i_sub})

        raise UnsatisfiedPrerequisites(
                "VecSum.partitioning_last() only implemented for vector"
                "summations with a single index over an integer Interval. "
                "The VecSum {0} has index or indices {1} and domain {2}."
                .format(self, self.indices, self.domain))

    @equality_prover('partitioned_first', 'partition_first')
    def partitioning_first(self, **defaults_config):
        '''
        Split a vector summation over an integral Interval {a ... c}
        into a vector sum of: the first term in the sum and a new
        summation over the integral Interval {(a+1) ... c}, deducing
        and returning the equivalence of the original vector summation
        with the new split version. The default uses auto_simplify=True
        to apply a shallow simplification to the new indices (for example,
        a new index of i = 4 + 1 may be expressed as i = 5) and to the
        lower term that has been peeled off by itself.
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This partitioning_first() method is implemented only for a
        VecSum with a single index and only when the domain is an
        integer Interval. Eventually this should also be implemented for
        domains of Natural, NaturalPos, etc. VecSum.partitioning_first()
        is called from VecSum.partitioning() for special cases.
        Example usage: Let S = VecSum(i, Vec(i+2), Interval(0, 10)).
        Then S.partitioning_first() will return the equality judgment
        |- S = Vec(0) + VecSum(i, i+2, Interval(1, 10))
        '''
        if isinstance(self.domain, Interval) and hasattr(self, 'index'):

            from . import vec_sum_split_first

            _v, _a, _b = vec_sum_split_first.all_instance_params()
            _i = vec_sum_split_first.instance_expr.instance_expr.lhs.index

            _i_sub = self.index
            _a_sub = self.domain.lower_bound
            _b_sub = self.domain.upper_bound
            _v_op, _v_op_sub = Function(_v, self.index), self.summand

            return vec_sum_split_first.instantiate(
                {_v_op: _v_op_sub, _a: _a_sub, _b: _b_sub, _i: _i_sub})

        raise NotImplementedError(
                "VecSum.partitioning_first() only implemented for vector "
                "summations with a single index over an integer Interval. "
                "The VecSum {0} has index or indices {1} and domain {2}."
                .format(self, self.indices, self.domain))

    def readily_factorable(self, factor, *, pull):
        '''
        Return True if 'factor' may be easily factored from this
        VecSum, pulling either to the 'left' or the 'right'.
        The 'factor' must be independent of the summation indices
        in order to factor it out.
        If pulling to the 'left', the factor must be at the front
        of any tensor product of vectors.  If pulling to the 'right', 
        the factor must be at the back of any tensor product of vectors.
        '''
        from proveit.linear_algebra import readily_factorable
        if self == factor:
            return True
        if not free_vars(factor).isdisjoint(self.indices):
            # We cannot pull out 'factor' because it is 
            # index-dependent.
            return False
        return readily_factorable(self.summand, factor, pull=pull)

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, **defaults_config):
        '''
        Factor 'the_factor' from this summation over vectors.
        
        An index-independent scalar factor may be pulled to the 'left', 
        an index-independent vector factor may be pulled to the 'right',
        an index-indepedent portion of a tensor product may be pulled
        to either side, or a vector summation may be pulled from
        an index-independent remainder in a reverse fashion.
        
        Respective examples:
            \sum_i a x_i = a \sum x_i
            \sum a_i x = (\sum a_i) x
            (\sum_i a_i x_i⊗y⊗z) = (\sum_i a_i x_i)⊗(y⊗z)
                                 = (\sum_i a_i x_i)⊗y⊗z
            (\sum_i b_i a z⊗x_i) = (a z) ⊗ (\sum_i b_i x_i)
        In any of these examples, the factor being pulled could
        be the index-independent parts or the summation.
 
        For the tensor product case, the factors may be grouped or not.
        In other cases, grouping will happen regardless.
        The remainders will be grouped regardless for the VecSum
        case (we ave 'group_remainder' as a parameter just for recursion
        compatibility).
        '''
        from proveit.numbers import compose_fraction
        from proveit.linear_algebra import ScalarMult
        if not pull in ('left', 'right'):
            raise ValueError("'pull' must be 'left' or 'right', not %s"
                             %pull)
        
        if isinstance(the_factor, ScalarMult):
            factor_scalar = the_factor.scalar
            factor_scaled = the_factor.scaled
        else:
            factor_scalar = one
            factor_scaled = the_factor            
        if isinstance(factor_scaled, VecSum) and factor_scaled.indices==self.indices:
            # Factoring out the summation part.
            expr = self
            eq = TransRelUpdater(expr)
            expr = eq.update(expr.inner_expr().summand.factorization(
                    factor_scaled.summand, pull=pull, 
                    group_factors=True, group_remainder=True, 
                    field=field, preserve_all=True))
            # Switch the roles now.
            reverse_pull = 'left' if pull=='right' else 'left'
            _idx = 0 if reverse_pull=='left' else -1
            remainder = expr.summand.operands[_idx]
            expr = eq.update(expr.shallow_factorization(
                             remainder, pull=reverse_pull, 
                             group_factors=(group_remainder and 
                                            factor_scalar==one),
                             group_remainder=True, field=field,
                             _check_index_independence=False,
                             preserve_all=(factor_scalar==one)))
            if factor_scalar != one:
                expr = eq.update(expr.factorization(
                        the_factor, pull=pull, group_factors=group_factors,
                        group_remainder=group_remainder, field=field))
                
            return eq.relation
        
        # Make sure that 'the_factor' is independent of any
        # summation index.
        if not free_vars(the_factor).isdisjoint(self.indices):
            raise ValueError("Cannot factor %s from %s because it is not "
                             "independent of the indices"%(the_factor, 
                                                           self))
        # Factor the summand.
        summand_factorization = self.inner_expr().summand.factorization(
                the_factor, pull=pull, group_factors=group_factors,
                group_remainder=True, field=field, preserve_all=True)
        return summand_factorization.apply_transitivity(
                 summand_factorization.rhs.shallow_factorization(
                         the_factor, pull=pull, group_factors=group_factors,
                         group_remainder=group_remainder, field=field,
                         _check_index_independence=False))

    @equality_prover('shallow_factorized', 'shallow_factor')
    def shallow_factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, _check_index_independence=True,
            **defaults_config):
        '''
        Perform a factorization at this level (no recursive 
        factorization).  Also see 'factorization' which does include
        recursive factorization.
        '''
        from proveit.linear_algebra import ScalarMult, TensorProd

        if _check_index_independence:
            # Make sure there that 'the_factor' is independent of any
            # summation index.
            if not free_vars(the_factor).isdisjoint(self.indices):
                raise ValueError("Cannot factor %s from %s because it is not "
                                 "independent of the indices"%(the_factor, 
                                                               self))

        _V = vec_space = VecSpaces.known_vec_space(self, field=field)
        _K = VecSpaces.known_field(vec_space)
        summand = self.summand
        _j = self.indices.num_elements()
        _Q = Lambda(self.indices, self.condition)
        if isinstance(summand, ScalarMult) and (
                summand.scalar == the_factor):
            from proveit.linear_algebra.scalar_multiplication import (
                    factorization_from_vec_sum)
            # Factoring out a scalar from the sum.  For example,
            #   \sum_i a x_i = a \sum x_i
            assert pull=='left', ("Scalars must be pulled to the 'left' "
                                  "when factoring from vectors")
            _k = the_factor
            _f = Lambda(self.indices, summand.scaled)
            return (factorization_from_vec_sum.instantiate(
                    {K:_K, f:_f, Q:_Q, j:_j, V:_V, k:_k})
                    .derive_consequent().with_wrapping_at())
        elif isinstance(summand, ScalarMult) and (
                summand.scaled == the_factor):
            # Factoring out a vector from the sum.  For example,
            #   \sum a_i x = (\sum a_i) x
            from proveit.linear_algebra.scalar_multiplication import (
                    scalar_sum_factorization)
            assert pull=='right', ("Vectors must be pulled to the 'right' "
                                   "when factoring from scaled versions")
            _v = the_factor
            _f = Lambda(self.indices, summand.scalar)
            return (scalar_sum_factorization.instantiate(
                    {K:_K, f:_f, Q:_Q, j:_j, V:_V, v:_v})
                   .derive_consequent().with_wrapping_at())
            
        else:
            # The only remaining possibility is factoring a vector
            # to one side of a tensor product within the summand. Examples:
            #   (\sum_i a_i x_i⊗y⊗z) = (\sum_i a_i x_i)⊗y⊗z
            #   (\sum_i a_i z⊗x_i) = z ⊗ (\sum_i a_i x_i)
            #   (\sum_i a b_i x_i⊗z)  = (\sum_i b_i x_i) ⊗ (a z) 
            #   (\sum_i b_i a z⊗x_i) = (a z) ⊗ (\sum_i b_i x_i)
            from proveit.linear_algebra.tensors import (
                    tensor_prod_factorization_from_summation)
    
            if not group_factors and isinstance(the_factor, TensorProd):
                num_factor_entries = the_factor.operands.num_entries()
                factor_entries = the_factor.operands.entries
            else:
                num_factor_entries = 1
                factor_entries = (the_factor,)
            _b = self.indices
            _j = _b.num_elements()
            if pull == 'left':
                if not isinstance(summand, TensorProd) or (
                        tuple(summand.factors[:num_factor_entries]) != 
                        factor_entries):
                    raise ValueError(
                            "%s not immediately factorable from "
                            "the left of %s"%(the_factor, summand))
                _k = zero # right side is empty
                # the actual factor operands
                _a = ExprTuple(*factor_entries)
                # middle has the remainder summation
                summand_remainders = self.summand.factors[num_factor_entries:]
                # the other side is empty
                _c = ()
                _i = _a.num_elements()
            elif pull == 'right':
                if not isinstance(summand, TensorProd) or (
                        tuple(summand.factors[-num_factor_entries:]) !=
                        the_factor):
                    raise ValueError(
                            "%s not immediately factorable from "
                            "the right of %s"%(the_factor, summand))
                _i = zero  # left side is empty
                # left side is empty
                _a = ()
                # middle has the remainder summation
                summand_remainders = self.summand.factors[:num_factor_entries]
                # right side has the factor
                _c = ExprTuple(*factor_entries)
                _k = _c.num_elements()
            if len(summand_remainders) != 1:
                    raise ValueError(
                            "%s does not factor from %s as a 'shallow' "
                            "factorization. Use 'factorization' instead"%
                            (the_factor, self))
            _f = Lambda(self.indices, summand_remainders[0])
            return tensor_prod_factorization_from_summation.instantiate(
                    {K:_K, f:_f, Q:_Q, V:_V, i:_i, j:_j, k:_k,
                     a:_a, b:_b, c:_c}).derive_consequent().with_wrapping_at()

    @equality_prover('factors_extracted', 'factors_extract')
    def factors_extraction(self, field=None, **defaults_config):
        '''
        Derive an equality between this VecSum and the result
        when all possible leading scalar factors have been extracted
        and moved to the front of the VecSum (for example, in the
        case where the summand of the VecSum is a ScalarMult) and
        all possible tensor product factors have been moved outside
        the VecSum (in front if possible, or afterward if necessary).
        For example, we could take the VecSum
            vec_sum = VecSum(ScalarMult(a, TensorProd(x, f(i), y))),
        where the index of summation is i, and call
            vec_sum.factor_extraction() to obtain:
            |- vec_sum = 
               ScalarMult(a, TensorProd(x, VecSum(f(i)), y))
        Note that any factors inside the summand that depend on the
        index of summation cannot be pulled out from inside the VecSum,
        and thus pose limitations on the result.
        Note that this method only works when self has a single
        index of summation, and only when self has a summand that is
        a ScalarMult or TensorProd.
        Later versions of this method should provide mechanisms to
        specify factors to extract from, and/or leave behind in, the
        VecSum.
        '''
        expr = self
        assumptions = defaults.assumptions + expr.conditions.entries
        assumptions_with_conditions = (
                defaults.assumptions + expr.conditions.entries)

        # for convenience in updating our equation:
        # this begins with eq.relation as expr = expr
        eq = TransRelUpdater(expr)

        # If the summand is a ScalarMult, perform a
        # shallow_simplification(), which will remove nested
        # ScalarMults and multiplicative identities. This is
        # intended to simplify without changing too much the
        # intent of the user. This might even transform the
        # ScalarMult object into something else.
        from proveit.linear_algebra import ScalarMult, TensorProd
        if isinstance(expr.summand, ScalarMult):
            expr = eq.update(
                    expr.inner_expr().summand.shallow_simplification())
        if isinstance(expr.summand, ScalarMult):
            # had to re-check, b/c the shallow_simplification might
            # have transformed the ScalarMult into the scaled object
            tensor_prod_summand = False # not clearly useful; review please
            the_scalar = expr.summand.scalar
            
        elif isinstance(expr.summand, TensorProd):
            tensor_prod_summand = True # not clearly useful; review please

        if isinstance(expr.summand, ScalarMult):
            if free_vars(expr.summand.scalar).isdisjoint(expr.indices):
                # it doesn't matter what the scalar is; the whole thing
                # can be pulled out in front of the VecSum
                from proveit.linear_algebra.scalar_multiplication import (
                    distribution_over_vec_sum)
                summand_in_vec_space = expr.summand.deduce_in_vec_space(
                        field=field, assumptions=assumptions_with_conditions)
                _V_sub = summand_in_vec_space.domain
                _K_sub = VecSpaces.known_field(_V_sub)
                _b_sub = expr.indices
                _j_sub = _b_sub.num_elements()
                _f_sub = Lambda(expr.indices, expr.summand.scaled)
                _Q_sub = Lambda(expr.indices, expr.condition)
                _k_sub = expr.summand.scalar
                imp = distribution_over_vec_sum.instantiate(
                        {V: _V_sub, K: _K_sub, b: _b_sub, j: _j_sub,
                         f: _f_sub, Q: _Q_sub, k: _k_sub},
                         assumptions=assumptions_with_conditions,
                         preserve_all=True)
                expr = eq.update(imp.derive_consequent(
                    assumptions=assumptions_with_conditions).derive_reversed())
            else:
                # The scalar portion is dependent on summation index.
                # If the scalar itself is a Mult of things, go through
                # and pull to the front of the Mult all individual
                # factors that are not dependent on the summation index.
                if isinstance(expr.summand.scalar, Mult):
                    # Repeatedly pull index-independent factors #
                    # to the front of the Mult factors          #

                    # prepare to count the extractable and
                    # unextractable factors
                    _num_factored = 0
                    _num_unfactored = len(expr.summand.scalar.operands.entries)

                    # go through factors from back to front
                    _prev_expr = expr
                    for the_factor in reversed(
                            expr.summand.scalar.operands.entries):

                        if free_vars(the_factor).isdisjoint(expr.indices):
                            expr = eq.update(
                                expr.inner_expr().summand.scalar.factorization(
                                    the_factor,
                                    assumptions=assumptions_with_conditions,
                                    preserve_all=True))
                            _num_factored += 1
                            _num_unfactored -= 1

                    # group the factorable factors
                    # if _num_factored > 0:
                    if _num_factored > 1 and _num_unfactored > 0:
                        expr = eq.update(
                            expr.inner_expr().summand.scalar.association(
                                0, _num_factored,
                                assumptions=assumptions_with_conditions,
                                preserve_all=True))
                    # group the unfactorable factors
                    if _num_unfactored > 1 and _num_factored > 0:
                        expr = eq.update(
                            expr.inner_expr().summand.scalar.association(
                                1, _num_unfactored,
                                assumptions=assumptions_with_conditions,
                                preserve_all=True))

                    # finally, extract any factorable scalar factors
                    if _num_factored > 0:
                        from proveit.linear_algebra.scalar_multiplication import (
                                distribution_over_vec_sum_with_scalar_mult)
                        # Mult._simplification_directives_.ungroup = False
                        # _V_sub = VecSpaces.known_vec_space(expr, field=field)
                        summand_in_vec_space = (
                                expr.summand.deduce_in_vec_space(
                                        field = field,
                                        assumptions =
                                        assumptions_with_conditions))
                        _V_sub = summand_in_vec_space.domain
                        _K_sub = VecSpaces.known_field(_V_sub)
                        _b_sub = expr.indices
                        _j_sub = _b_sub.num_elements()
                        _f_sub = Lambda(expr.indices, expr.summand.scaled)
                        _Q_sub = Lambda(expr.indices, expr.condition)
                        _c_sub = Lambda(expr.indices,
                                        expr.summand.scalar.operands[1])
                        _k_sub = expr.summand.scalar.operands[0]
                        # when instantiating, we set preserve_expr=expr;
                        # otherwise auto_simplification disassociates inside
                        # the Mult.
                        impl = distribution_over_vec_sum_with_scalar_mult.instantiate(
                                {V:_V_sub, K:_K_sub, b: _b_sub, j: _j_sub,
                                 f: _f_sub, Q: _Q_sub, c:_c_sub, k: _k_sub},
                                 preserve_expr=expr,
                                assumptions=assumptions_with_conditions,
                                preserve_all=True)
                        expr = eq.update(impl.derive_consequent(
                                assumptions=assumptions_with_conditions).
                                derive_reversed())

                else:
                    # The scalar component is dependent on summation
                    # index but is not a Mult.
                    # Revert everything and return self = self.
                    #print("Found summation index {0} in the scalar {1} "
                    #      "and the scalar is not a Mult object.".
                    #  format(summation_index, expr.summand.scalar))
                    eq = TransRelUpdater(self)

        # ============================================================ #
        # VECTOR FACTORS                                               #
        # ============================================================ #
        # After the scalar factors (if any) have been dealt with,
        # proceed with the vector factors in any remaining TensorProd
        # in the summand.
        # Notice that we are not guaranteed at this point that we even
        # have a TensorProd to factor, and if we do have a TensorProd
        # we have not identified the non-index-dependent factors to 
        # extract.
        # After processing above for scalar factors, we might now have
        # (1) expr = VecSum (we didn't find scalar factors to extract),
        # inside of which we might have a ScalarMult or a TensorProd;
        # or (2) expr = ScalarMult (we found some scalar factors to
        # extract), with a VecSum as the scaled component.

        if isinstance(expr, VecSum) and (
                isinstance(expr.summand, TensorProd) or
                (isinstance(expr.summand, ScalarMult) and
                 isinstance(expr.summand.scaled, TensorProd))):
            expr = eq.update(expr.tensor_prod_factoring())
        elif isinstance(expr, ScalarMult) and (
                isinstance(expr.scaled, VecSum) and
                (isinstance(expr.scaled.summand, TensorProd) or
                 (isinstance(expr.scaled.summand, ScalarMult) and
                  isinstance(expr.scaled.summand.scaled, TensorProd)))):
            expr = eq.update(expr.inner_expr().scaled.tensor_prod_factoring())

        return eq.relation

    @equality_prover('tensor_prod_factored', 'tensor_prod_factor')
    def tensor_prod_factoring(self, idx=None, idx_beg=None, idx_end=None,
                              field=None, **defaults_config):
        '''
        For a VecSum with a TensorProd summand or ScalarMult summand
        with a scaled attribute being a TensorProd, factor out from
        the VecSum the TensorProd vectors other than the ones indicated
        by the (0-based) idx, or idx_beg and idx_end pair and return
        an equality between the original VecSum and the new TensorProd.
        For example, we could take the VecSum defined by
        vec_sum = VecSum(TensorProd(x, f(i), y, z))
        and call vec_sum.tensor_prod_factoring(idx_beg=1, idx_end=2)
        to obtain:

            |- VecSum(TensorProd(x, f(i), y, z)) = 
               TensorProd(x, VecSum(TensorProd(f(i), y)), z)

        This method should work even if the summand is a nested
        ScalarMult. Note that any vectors inside the TensorProd that
        depend on the index of summation cannot be pulled out of the
        VecSum and thus will cause the method to fail if not chosen
        to remain inside the VecSum. If all idx args are 'None',
        method will factor out all possible vector factors, including
        the case where all factors could be removed and the VecSum
        eliminated entirely.
        Note that this method only works when self has a single
        index of summation.
        '''
        expr = self
        the_summand = self.summand

        eq = TransRelUpdater(expr)

        # Check that 
        #    (1) the_summand is a TensorProd
        # or (2) the_summand is a ScalarMult;
        # otherwise, this method does not apply
        from proveit.linear_algebra import ScalarMult, TensorProd
        if isinstance(the_summand, ScalarMult):
            # try shallow simplification first to remove nested
            # ScalarMults and multiplicative identities
            expr = eq.update(expr.inner_expr().summand.shallow_simplification())
            the_summand = expr.summand
        indices = expr.indices
        if isinstance(the_summand, TensorProd):
            tensor_prod_expr = the_summand
            tensor_prod_summand = True
            tensor_prod_factors_list = list(
                    the_summand.operands.entries)
        elif (isinstance(the_summand, ScalarMult)
              and isinstance(the_summand.scaled, TensorProd)):
            tensor_prod_expr = the_summand.scaled
            tensor_prod_summand = False
            tensor_prod_factors_list = list(
                    the_summand.scaled.operands.entries)
        else:
            raise ValueError(
                "tensor_prod_factoring() requires the VecSum summand "
                "to be a TensorProd or a ScalarMult (with its 'scaled' "
                "attribute a TensorProd); instead the "
                "summand is {}".format(self.instance_expr))

        if idx is None and idx_beg is None and idx_end is None:
            # prepare to take out all possible factors, including
            # the complete elimination of the VecSum if possible
            if free_vars(expr.summand).isdisjoint(indices):
                # summand does not depend on indices of summation
                # so we can eliminate the VecSum entirely
                return expr.vec_sum_elimination(field=field)
            if not free_vars(tensor_prod_expr).isdisjoint(indices):
                # identify the extractable vs. non-extractable
                # TensorProd factors (and there must be at least
                # one such non-extractable factor)
                
                idx_beg = -1
                idx_end = -1
                for _i in range(len(expr.summand.operands.entries)):
                    if not free_vars(tensor_prod_expr.operands[_i]).isdisjoint(
                            indices):
                        if idx_beg == -1:
                            idx_beg = _i
                            idx_end = idx_beg
                        else:
                            idx_end = _i
            else:
                # The alternative is that the summand is
                # a ScalarMult with the scalar (but not the scaled)
                # being dependent on the index of summation. It's not
                # obvious what's best to do in this case, but we set
                # things up to factor out all but the last of the
                # TensorProd factors (so we'll factor out at least
                # 1 factor)
                idx_beg = len(tensor_prod_expr.operands.entries) - 1
                idx_end = idx_beg


        # Check that the provided idxs are within bounds
        # (it should refer to an actual TensorProd operand)

        num_vec_factors = len(tensor_prod_factors_list)
        if idx is not None and idx >= num_vec_factors:
            raise ValueError(
                    "idx value {0} provided for tensor_prod_factoring() "
                    "method is out-of-bounds; the TensorProd summand has "
                    "{1} factors: {2}, and thus possibly indices 0-{3}".
                    format(idx, len(tensor_prod_factors_list),
                           tensor_prod_factors_list,
                           len(tensor_prod_factors_list)-1))
        if idx_beg is not None and idx_end is not None:
            if (idx_end < idx_beg or idx_beg >= num_vec_factors or
                idx_end >= num_vec_factors):
                raise ValueError(
                    "idx_beg value {0} or idx_end value {1} (or both) "
                    "provided for tensor_prod_factoring() "
                    "method is/are out-of-bounds; the TensorProd summand "
                    "has {2} factors: {3}, and thus possibly indices 0-{3}".
                    format(idx_beg, idx_end, num_vec_factors,
                           tensor_prod_factors_list,num_vec_factors-1))
        if idx is not None:
            # take single idx as the default
            idx_beg = idx
            idx_end = idx

        # Check that the TensorProd factors to be factored out do not
        # rely on the VecSum index of summation
        for _i in range(num_vec_factors):
            if _i < idx_beg or _i > idx_end:
                the_factor = tensor_prod_factors_list[_i]
                if not free_vars(the_factor).isdisjoint(indices):
                    raise ValueError(
                            "TensorProd factor {0} cannot be factored "
                            "out of the given VecSum summation because "
                            "it is a function of a summation index {1}.".
                            format(the_factor, indices))
        
        # Everything checks out as best we can tell, so prepare to
        # import and instantiate the appropriate theorem,
        # depending on whether:
        # (1) the_summand is a TensorProd, or
        # (2) the_summand is a ScalarMult (with a TensorProd 'scaled')
        if tensor_prod_summand:
            from proveit.linear_algebra.tensors import (
                tensor_prod_distribution_over_summation)
        else:
            from proveit.linear_algebra.tensors import (
                tensor_prod_distribution_over_summation_with_scalar_mult)
        if idx_beg != idx_end:
            # need to associate the elements and change idx value
            # but process is slightly different in the two cases
            if tensor_prod_summand:
                expr = eq.update(expr.inner_expr().summand.association(
                        idx_beg, idx_end-idx_beg+1, preserve_all=True))
                tensor_prod_expr = expr.summand
            else:
                expr = eq.update(expr.inner_expr().summand.scaled.association(
                        idx_beg, idx_end-idx_beg+1, preserve_all=True))
                tensor_prod_expr = expr.summand.scaled
        idx = idx_beg

        from proveit import K, f, Q, i, j, k, V, a, b, c, s
        # actually, maybe it doesn't matter and we can deduce the 
        # vector space regardless: (Adding this temp 12/26/21)
        vec_space_membership = expr.summand.deduce_in_vec_space(
            field=field,
            assumptions = defaults.assumptions + expr.conditions.entries)
        _V_sub = vec_space_membership.domain
        # Substitutions regardless of Case
        _K_sub = VecSpaces.known_field(_V_sub)
        _b_sub = expr.indices
        _j_sub = _b_sub.num_elements()
        _Q_sub = Lambda(expr.indices, expr.condition)
        # Case-specific substitutions, using updated tensor_prod_expr:
        _a_sub = tensor_prod_expr.operands[:idx]
        _c_sub = tensor_prod_expr.operands[idx+1:]
        _f_sub = Lambda(expr.indices, tensor_prod_expr.operands[idx])
        if not tensor_prod_summand:
            _s_sub = Lambda(expr.indices, expr.summand.scalar)
        # Case-dependent substitutions:
        _i_sub = _a_sub.num_elements()
        _k_sub = _c_sub.num_elements()

        if tensor_prod_summand:
            impl = tensor_prod_distribution_over_summation.instantiate(
                    {K:_K_sub, f:_f_sub, Q:_Q_sub, i:_i_sub, j:_j_sub,
                     k:_k_sub, V:_V_sub, a:_a_sub, b:_b_sub, c:_c_sub},
                     preserve_expr=expr)
        else:
            impl = (tensor_prod_distribution_over_summation_with_scalar_mult.
                   instantiate(
                    {K:_K_sub, f:_f_sub, Q:_Q_sub, i:_i_sub, j:_j_sub,
                     k:_k_sub, V:_V_sub, a:_a_sub, b:_b_sub, c:_c_sub,
                     s: _s_sub}, preserve_expr=expr))

        expr = eq.update(impl.derive_consequent(
                assumptions = defaults.assumptions + expr.conditions.entries).
                derive_reversed())

        return eq.relation

def get_all_operands(obj_list):
    '''
    For the list obj_list of objects, recursively
    determine and return a list of all operands, including
    the original list objects. For example,
    get_all_operands([Add(i, Mult(j, 3))])
    returns [i + j*3, i, j*3, j, 3].
    '''
    operand_list = []
    for elem in obj_list:
        if hasattr(elem, 'operands'):
            operand_list = (
                    operand_list +
                    [elem] +
                    get_all_operands(list(elem.operands.entries)))
        else:
            operand_list = operand_list + [elem]

    return operand_list 

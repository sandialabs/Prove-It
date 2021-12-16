from proveit import (defaults, free_vars, Literal, Function, Lambda, 
                     relation_prover, equality_prover,
                     TransRelUpdater, UnsatisfiedPrerequisites)
from proveit import a, b, c, f, i, j, k, v, K, Q, V
from proveit.logic import InSet
from proveit.numbers import Interval
from proveit.abstract_algebra import GroupSum 
from proveit.linear_algebra import VecSpaces

class VecSum(GroupSum):
    '''
    Denote general summation over a set of elements of any field in 
    analogy to number summation.
    '''
    
    # operator of the Sum operation.
    _operator_ = Literal(string_format='Sum',  latex_format=r'\sum',
                         theory=__file__)
        
    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, VecSum._operator_, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)

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
            # If the operands are all complex numbers, this will
            # VecAdd will reduce to number Add.
            return self.number_sum_reduction()
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
        summation_index = expr.index
        summand_conditions = expr.conditions
        assumptions = defaults.assumptions + summand_conditions.entries

        # for convenience updating our equation:
        # this begins with expr = expr
        eq = TransRelUpdater(expr)

        # instead of beginning with a shallow_simplification on the
        # summand regardless of its class, perform a shallow_simplification
        # only if the summand is a ScalarMult, which will remove nested
        # ScalarMults and multiplicative identities. That seems a simple
        # simplification without changing too much the intent of the
        # user.
        from proveit.linear_algebra import ScalarMult, TensorProd
        if isinstance(expr.summand, ScalarMult):
            tensor_prod_summand = False
            the_scalar = expr.summand.scalar
            expr = eq.update(
                    expr.inner_expr().summand.shallow_simplification())
        elif isinstance(expr.summand, TensorProd):
            tensor_prod_summand = True

        ###############################################################
        # A kludgy piece here - when dealing with the ScalarMult
        # version of the summand, it still helps to form the analogous
        # Non-scalar version of the already-associated expression and
        # call the VecSpaces.known_vec_space() on it. Something
        # mysterious going on there that isn't being handled when
        # calling the known_vec_space() on the ScalarMult version.
        # if tensor_prod_summand:
        #     _V_sub = VecSpaces.known_vec_space(expr, field=field)
        # else:
        #     temp_tensor_prod_version = VecSum(
        #         expr.index, expr.summand.scaled, domain=expr.domain)
        #     _V_sub = VecSpaces.known_vec_space(
        #             temp_tensor_prod_version, field=field)
        #     print("_V_sub successful!")
        #     print("Called on:")
        #     display(temp_tensor_prod_version)
            # but later the system doesn't seem to be able to
            # tell that a component of the tensor product is in
            # a vector space! Very sad!

        # temporarily try/confirm -- can we simply do this instead?
        # regardless of whether we have a ScalarMult or TensorProd
        # summand?
        _V_sub = VecSpaces.known_vec_space(expr, field=field)

        ###############################################################

        if isinstance(expr.summand, ScalarMult):
            if summation_index not in free_vars(expr.summand.scalar):
                # it doesn't matter what the scalar is; the whole thing
                # can be pulled out in front of the VecSum
                from proveit.linear_algebra.scalar_multiplication import (
                    distribution_over_vec_sum)
                # playing with the following
                _V_sub = VecSpaces.known_vec_space(
                        expr, field=field) # change expr.summand.scaled to expr?
                # end playing
                _K_sub = VecSpaces.known_field(_V_sub)
                _b_sub = expr.indices
                _j_sub = _b_sub.num_elements()
                _f_sub = Lambda(expr.indices, expr.summand.scaled)
                _Q_sub = Lambda(expr.indices, expr.condition)
                _k_sub = expr.summand.scalar
                imp = distribution_over_vec_sum.instantiate(
                        {V: _V_sub, K: _K_sub, b: _b_sub, j: _j_sub,
                         f: _f_sub, Q: _Q_sub, k: _k_sub},
                         assumptions=assumptions)
                expr = eq.update(imp.derive_consequent().derive_reversed())
            else:
                # The scalar portion is dependent on summation index;
                # if the scalar itself is a Mult of things, go through
                # and pull out individual factors that are not dependent
                # on the summation index
                from proveit.numbers import Mult
                if isinstance(expr.summand.scalar, Mult):
                    # start by flattening the Mult if possible: Not needed?
                    expr = eq.update(expr.inner_expr().summand.scalar.shallow_simplification())

                    # Repeatedly pull index-independent factors to the
                    # front of the Mult factors

                    # prepare to count the extractable and
                    # unextractablecount factors
                    _num_factored = 0
                    _num_unfactored = len(expr.summand.scalar.operands.entries)
                    # prepare to use conditions in assumptions
                    summation_conditions = expr.conditions.entries

                    # go through factors from back to front
                    for the_factor in reversed(
                            expr.summand.scalar.operands.entries):

                        if summation_index not in free_vars(the_factor):
                            expr = eq.update(
                                expr.inner_expr().summand.scalar.factorization(
                                    the_factor,
                                    assumptions=
                                    defaults.assumptions+summation_conditions))
                            _num_factored += 1
                            _num_unfactored -= 1

                    # group the factorable factors
                    if _num_factored > 0:
                        expr = eq.update(
                            expr.inner_expr().summand.scalar.association(
                                0, _num_factored,
                                assumptions=defaults.assumptions+summation_conditions))
                    # group the unfactorable factors
                    if _num_unfactored > 1:
                        expr = eq.update(
                            expr.inner_expr().summand.scalar.association(
                                1, _num_unfactored,
                                assumptions=defaults.assumptions+summation_conditions))

                    # finally, extract any factorable factors
                    from proveit.linear_algebra.scalar_multiplication import (
                            distribution_over_vec_sum_with_scalar_mult)
                    # Mult._simplification_directives_.ungroup = False
                    _V_sub = VecSpaces.known_vec_space(expr, field=field)
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
                            assumptions=
                            defaults.assumptions+expr.conditions.entries)
                    eq.update(impl.derive_consequent(
                            assumptions=
                            defaults.assumptions+expr.conditions.entries).
                            derive_reversed())

                else:
                    # The scalar component is not a Mult.
                    # Revert everything and return self = self.
                    print("Found summation index {0} in the scalar {1} "
                          "and the scalar is not a Mult object.".
                      format(summation_index, expr.summand.scalar))
                    eq = TransRelUpdater(self)

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
        Note that any vectors inside the TensorProd that depend on the
        index of summation cannot be pulled out of the VecSum and thus
        will cause the method to fail if not chosen to remain inside
        the VecSum.
        Note that this method only works when self has a single
        index of summation.
        Later versions of this method should generalize to allow
        multiple (contiguous) indices to be specified as arguments
        to indicate multple VecProd factors to remain within the VecSum
        (the contiguity is required since tensor products are not
        commutative).
        '''
        expr = self
        the_summand = self.summand

        # Check that 
        #    (1) the_summand is a TensorProd
        # or (2) the_summand is a ScalarMult;
        # otherwise, this method does not apply
        from proveit.linear_algebra import ScalarMult, TensorProd
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
        summation_index = expr.index
        for i in range(num_vec_factors):
            if i < idx_beg or i > idx_end:
                the_factor = tensor_prod_factors_list[i]
                if summation_index in free_vars(the_factor):
                    raise ValueError(
                            "TensorProd factor {0} cannot be factored "
                            "out of the given VecSum summation because "
                            "it is a function of the summation index {1}.".
                            format(the_factor, summation_index))
        
        # Everything checks out as best we can tell, so prepare to
        # import and instantiate the appropriate theorem,
        # depending on whether:
        # (1) the_summand is a TensorProd, or
        # (2) the_summand is a ScalarMult (with a TensorProd 'scaled')
        eq = TransRelUpdater(expr)
        if tensor_prod_summand:
            from proveit.linear_algebra.tensors import (
                tensor_prod_distribution_over_summation)
        else:
            from proveit.linear_algebra.tensors import (
                tensor_prod_distribution_over_summation_with_scalar_mult)
        if idx_beg != idx_end:
            # need to associate the elements and change idx value
            # but process is slightly different the two cases
            if tensor_prod_summand:
                expr = eq.update(expr.inner_expr().summand.association(
                        idx_beg, idx_end-idx_beg+1))
            else:
                expr = eq.update(expr.inner_expr().summand.scaled.association(
                        idx_beg, idx_end-idx_beg+1))
                # expr.summand.scaled.deduce_in_vec_space(field=field)
            idx = idx_beg
        # A kludgy piece here - when dealing with the ScalarMult
        # version of the summand, it still helps to form the analogous
        # Non-scalar version of the already-associated expression and
        # call the VecSpaces.known_vec_space() on it. Something
        # mysterious going on there that isn't being handled when
        # calling the known_vec_space() on the ScalarMult version.
        if tensor_prod_summand:
            _V_sub = VecSpaces.known_vec_space(expr, field=field)
        else:
            from proveit import i 
            temp_tensor_prod_version = VecSum(
                i, expr.summand.scaled, domain=expr.domain)
            _V_sub = VecSpaces.known_vec_space(
                    temp_tensor_prod_version, field=field)

        from proveit import K, f, Q, i, j, k, V, a, b, c, s
        # Substitutions regardless of Case
        _K_sub = VecSpaces.known_field(_V_sub)
        _b_sub = expr.indices
        _j_sub = _b_sub.num_elements()
        _Q_sub = Lambda(expr.indices, expr.condition)
        # Case-specific substitutions:
        if tensor_prod_summand:
            _a_sub = expr.summand.operands[:idx]
            _c_sub = expr.summand.operands[idx+1:]
            _f_sub = Lambda(expr.indices, expr.summand.operands[idx])
        else:
            _a_sub = expr.summand.scaled.operands[:idx]
            _c_sub = expr.summand.scaled.operands[idx+1:]
            _f_sub = Lambda(expr.indices, expr.summand.scaled.operands[idx])
            # _f_sub = Lambda(expr.indices, 
            #                 ScalarMult(expr.summand.scalar,
            #                            expr.summand.scaled.operands[idx]) )
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

        expr = eq.update(impl.derive_consequent().derive_reversed())

        return eq.relation

    # @equality_prover('tensor_prod_factored', 'tensor_prod_factor')
    # def tensor_prod_factoring(self, idx, field=None, **defaults_config):
    #     '''
    #     For a VecSum with a TensorProd operand and a (0-based) index
    #     idx, factor TensorProd vectors other than the vector at idx
    #     out of the VecSum and return an equality between the original
    #     VecSum and the new TensorProd. For example, we could take the
    #     VecSum vec_sum = VecSum(TensorProd(x, f(i), y))
    #     and call vec_sum.tensor_prod_factoring(1) to obtain:
    #         |- VecSum(TensorProd(x, f(i), y)) = 
    #            TensorProd(x, VecSum(f(i)), y)
    #     Note that any vectors inside the TensorProd that depend on the
    #     index of summation cannot be pulled out of the VecSum and thus
    #     will cause the method to fail if not chosen to remain inside
    #     the VecSum.
    #     Note that this method only works when self has a single
    #     index of summation.
    #     Later versions of this method should generalize to allow
    #     multiple (contiguous) indices to be specified as arguments
    #     to indicate multple VecProd factors to remain within the VecSum
    #     (the contiguity is required since tensor products are not
    #     commutative).
    #     '''

    #     # Check that the VecSum instance expression is a TensorProd
    #     # otherwise, this method does not apply
    #     from proveit.linear_algebra import TensorProd
    #     if not isinstance(self.instance_expr, TensorProd):
    #         raise ValueError(
    #             "tensor_prod_factoring() requires the VecSum instance " +
    #             "expression to be a TensorProd; instead the instance " +
    #             "expression is {}".format(self.instance_expr))

    #     # Check that the provided idx is within bounds
    #     # (it should refer to an actual TensorProd operand)
    #     tensor_prod_factors_list = list(self.instance_expr.operands.entries)
    #     if idx >= len(tensor_prod_factors_list):
    #         raise ValueError(
    #                 "idx value {0} provided for tensor_prod_factoring() "
    #                 "method is out-of-bounds; the TensorProd summand has "
    #                 "{1} factors: {2}, and thus possibly indices 0-{3}".
    #                 format(idx, len(tensor_prod_factors_list),
    #                        tensor_prod_factors_list,
    #                        len(tensor_prod_factors_list)-1))

    #     # Check that the TensorProd factors to be factored out do not
    #     # rely on the VecSum index of summation
    #     tensor_prod_factors_list = list(self.instance_expr.operands.entries)
    #     summation_index = self.index
    #     for i in range(len(tensor_prod_factors_list)):
    #         if i != idx:
    #             the_factor = tensor_prod_factors_list[i]
    #             if summation_index in free_vars(the_factor):
    #                 raise ValueError(
    #                         "TensorProd factor {0} cannot be factored "
    #                         "out of the given VecSum summation because "
    #                         "it is a function of the summation index {1}.".
    #                         format(the_factor, summation_index))
    #             # factor_operands = (
    #             #         get_all_operands([the_factor]))
    #             # if summation_index in factor_operands:
    #             #     raise ValueError(
    #             #             "TensorProd factor {0} cannot be factored "
    #             #             "out of the given VecSum summation because "
    #             #             "it is a function of the summation index {1}.".
    #             #             format(the_factor, summation_index))
        
    #     # Everything checks out as best we can tell, so import
    #     # and instantiate the theorem
    #     from proveit.linear_algebra.tensors import (
    #             tensor_prod_distribution_over_summation)
    #     from proveit import K, f, Q, i, j, k, V, a, b, c
    #     _V_sub = VecSpaces.known_vec_space(self, field=field)
    #     _K_sub = VecSpaces.known_field(_V_sub)
    #     _a_sub = self.summand.operands[:idx]
    #     _c_sub = self.summand.operands[idx+1:]
    #     _i_sub = _a_sub.num_elements()
    #     _k_sub = _c_sub.num_elements()
    #     _b_sub = self.indices
    #     _j_sub = _b_sub.num_elements()
    #     _f_sub = Lambda(self.indices, self.summand.operands[idx])
    #     _Q_sub = Lambda(self.indices, self.condition)

    #     impl = tensor_prod_distribution_over_summation.instantiate(
    #             {K:_K_sub, f:_f_sub, Q:_Q_sub, i:_i_sub, j:_j_sub,
    #              k:_k_sub, V:_V_sub, a:_a_sub, b:_b_sub, c:_c_sub},
    #              preserve_all=True)

    #     return impl.derive_consequent().derive_reversed().with_wrapping_at()

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

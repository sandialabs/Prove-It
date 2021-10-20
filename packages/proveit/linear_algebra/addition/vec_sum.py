from proveit import (defaults, Literal, Function, Lambda, 
                     relation_prover, equality_prover,
                     UnsatisfiedPrerequisites)
from proveit import a, b, c, f, i, j, v, K, Q, V
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
        if hasattr(self.summand, 'deduce_in_number_set'):
            # Maybe we can reduce the VecSum to a number Sum.
            inner_assumptions = defaults.assumptions + self.conditions.entries
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

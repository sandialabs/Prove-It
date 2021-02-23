from proveit import (Literal, Lambda, Function, Operation, 
                     OperationOverInstances, InnerExpr,
                     Judgment, free_vars, maybe_fenced, USE_DEFAULTS, 
                     ProofFailure, defaults)
from proveit.logic import Forall, InSet
from proveit.numbers.number_sets import (
        RealInterval, Interval, Real, Integer, Natural, Complex)
from proveit.numbers.negation import Neg
from proveit.numbers.ordering import LessEq, Less
from proveit import a, b, c, f, i, j, k, x, P, Q, S
from proveit import TransRelUpdater


class Sum(OperationOverInstances):
    # operator of the Sum operation.
    _operator_ = Literal(
        string_format='Sum',
        latex_format=r'\sum',
        theory=__file__)
    _init_argname_mapping_ = {'index_or_indices': 'instance_param_or_params',
                              'summand': 'instance_expr'}

#    def __init__(self, summand-instance_expression, indices-instance_vars, domains):
#    def __init__(self, instance_vars, instance_expr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic.booleanss):
        indices: instance vars
        summand: instance_expressions
        domains: conditions (except no longer optional)
        '''
        if (domains is not None):
            raise NotImplementedError("Sum class not yet implemented for "
                                      "multiple domains nor for multiple "
                                      "indices.")

        OperationOverInstances.__init__(
            self, Sum._operator_, index_or_indices, summand,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, _lambda_map=_lambda_map)
        if hasattr(self, 'instance_param'):
            self.index = self.instance_param
        if hasattr(self, 'instance_vars'):
            self.indices = self.instance_params
        self.summand = self.instance_expr
        """
        # think about this later
        if isinstance(self.domain,RealInterval):
            raise ValueError('Sum cannot sum over non-discrete set (e.g. Interval)')
        elif self.domain == Real:
            raise ValueError('Sum cannot sum over Real.')
        elif self.domain == Integer:
            self.domain = Interval(Neg(infinity),infinity)
        elif self.domain == Natural:
            self.domain = Interval(zero,infinity)
        """

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        from . import (summation_nat_closure, summation_int_closure, 
                       summation_real_closure, summation_complex_closure)
        _x = self.instance_param
        P_op, _P_op = Function(P, _x), self.instance_expr
        Q_op, _Q_op = Function(Q, _x), self.condition
        self.summand
        if number_set == Natural:
            thm = summation_nat_closure
        elif number_set == Integer:
            thm = summation_int_closure
        elif number_set == Real:
            thm = summation_real_closure
        elif number_set == Complex:
            thm = summation_complex_closure
        else:
            raise ProofFailure(
                    InSet(self, number_set), assumptions,
                    ("'deduce_in_number_set' not implemented for the %s set"
                     % str(number_set)))
        impl = thm.instantiate(
            { x: _x, P_op: _P_op, Q_op: _Q_op}, assumptions=assumptions)
        antecedent = impl.antecedent
        if not antecedent.proven(assumptions):
            # Conclude the antecedent via generalization.
            antecedent.conclude_via_generalization(
                    assumptions, defaults.automation)
        return impl.derive_consequent(assumptions=assumptions)

    def _formatted(self, format_type, **kwargs):
        # MUST BE UPDATED TO DEAL WITH 'joining' NESTED LEVELS
        fence = kwargs['fence'] if 'fence' in kwargs else False
        if isinstance(self.domain, Interval):
            lower = self.domain.lower_bound.formatted(format_type)
            upper = self.domain.upper_bound.formatted(format_type)
            formatted_inner = self.operator.formatted(
                format_type) + r'_{' + self.index.formatted(format_type) + '=' + lower + r'}' + r'^{' + upper + r'} '
            explicit_ivars = list(self.explicit_instance_vars())
            has_explicit_ivars = (len(explicit_ivars) > 0)
            explicit_conds = list(self.explicit_conditions())
            has_explicit_conds = (len(explicit_conds) > 0)
            if has_explicit_conds:
                if has_explicit_ivars:
                    formatted_inner += " | "
                formatted_inner += ', '.join(condition.formatted(format_type)
                                             for condition in explicit_conds)
            formatted_inner += self.summand.formatted(format_type, fence=True)
            return maybe_fenced(format_type, formatted_inner, fence=fence)
        else:
            return OperationOverInstances._formatted(self, format_type, fence)

    def do_reduced_simplification(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a Interval where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from proveit.logic import SimplificationError
        from . import sum_single
        if isinstance(
                self.domain,
                Interval) and self.domain.lower_bound == self.domain.upper_bound:
            if self.instance_vars.is_single():
                return sum_single.instantiate({Operation(
                    f, self.instance_vars): self.summand}).instantiate({a: self.domain.lower_bound})
        raise SimplificationError(
            "Sum simplification only implemented for a summation over a Interval of one instance variable where the upper and lower bound is the same")

    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a Interval where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs

    def reduce_geom_sum(self, assumptions=frozenset()):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        May need assumptions to proven prerequisite number set conditions.
        '''
        from theorems import inf_geom_sum, fin_geom_sum
        m_val = self.indices[0]

        try:
            #            self.r = extract_exp_base(self.summand)
            x_val = self.summand.base
        except BaseException:
            raise ValueError("Summand not an exponential!")
        if not isinstance(self.domain, Interval):
            raise ValueError("Not explicitly summing over Interval!")
        else:
            if self.domain.lower_bound == zero and self.domain.upper_bound == infinity:
                # We're in the infinite geom sum domain!
                deduce_in_complex(x_val, assumptions)
                return inf_geom_sum.instantiate({x: x_val, m: m_val})
            else:
                # We're in the finite geom sum domain!
                k_val = self.domain.lower_bound
                l_val = self.domain.upper_bound
                deduce_in_integer(k_val, assumptions)
                deduce_in_integer(l_val, assumptions)
                deduce_in_complex(x_val, assumptions)
                return fin_geom_sum.instantiate(
                    {x: x_val, m: m_val, k: k_val, l: l_val})
#        else:
#            print "Not a geometric sum!"

    # def shift(self, shift_amount, assumptions=frozenset()):
    #     '''
    #     Shift the summation indices by the shift amount, deducing and returning
    #     the equivalence of this summation with a index-shifted version.
    #     '''
    #     from theorems import index_shift
    #     if not self.indices.is_single() or not isinstance(self.domain, Interval):
    #         raise Exception(
    #             'Sum shift only implemented for summations with one index over a Interval')
    #     f_op, f_op_sub = Operation(f, self.index), self.summand
    #     deduce_in_integer(self.domain.lower_bound, assumptions)
    #     deduce_in_integer(self.domain.upper_bound, assumptions)
    #     deduce_in_integer(shift_amount, assumptions)
    #     return index_shift.instantiate({f_op: f_op_sub, x: self.index}).instantiate(
    #         {a: self.domain.lower_bound, b: self.domain.upper_bound, c: shift_amount})

    def shift(self, shift_amount, simplify_idx=True, simplify_summand=True,
              assumptions=USE_DEFAULTS, user_reductions=[]):
        '''
        Shift the summation indices by the shift_amount, deducing and
        returning the equivalence of this summation with the
        index-shifted version. When the simplify_x args are True, a
        shallow simplification is applied to the shifted indices and
        shifted summand. ALSO consider accepting manually provided
        reductions?
        This shift() method is implemented only for a Sum with a single
        index and only when the domain is an integer Interval.
        Example: Let S = Sum(i, i+2, Interval(0, 10)). Then S.shift(one)
        will return |- S = Sum(i, i+1, Interval(1, 11)).
        '''
        if hasattr(self, 'indices'):
            raise Exception(
                "Sum.shift() only implemented for summations with a single "
                "index over an Interval. The sum {} has indices {}."
                .format(self, self.indices))
        # the following constraint can eventually be modified to deal
        # with a domain like all Natural … but for now limited to
        # integer Interval domain
        if not isinstance(self.domain, Interval):
            raise Exception(
                "Sum.shift() only implemented for summations with a single "
                "index over an Interval. The sum {} has domain {}."
                .format(self, self.domain))

        from . import index_shift
        from proveit.numbers import Add

        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _c = shift_amount
        # create some (possible) reduction formulas for the shifted
        # components, which will then be passed through to the
        # instantiation as "reductions" for simpifying the final form
        # of the indices and summand
        if (simplify_idx):
            lower_bound_shifted = (
                Add(_a, _c).do_reduced_simplification(assumptions=assumptions))
            user_reductions = [*user_reductions, lower_bound_shifted]
            upper_bound_shifted = (
                Add(_b, _c).do_reduced_simplification(assumptions=assumptions))
            user_reductions = [*user_reductions, lower_bound_shifted]
        if (simplify_summand):
            summand_shifted = (
                Add(self.summand, _c).do_reduced_simplification(
                    assumptions=assumptions))
            user_reductions = [*user_reductions, summand_shifted]

        f_op, f_op_sub = Operation(f, self.index), self.summand
        return index_shift.instantiate(
            {f_op: f_op_sub, x: self.index}).instantiate(
            {a: self.domain.lower_bound, b: self.domain.upper_bound,
             c: shift_amount},
             reductions=user_reductions)

    def join(self, second_summation, assumptions=frozenset()):
        '''
        Join the "second summation" with "this" summation, deducing and returning
        the equivalence of these summations added with the joined summation.
        Both summation must be over Intervals.
        The relation between the first summation upper bound, UB1, and the second
        summation lower bound, LB2 must be explicitly either UB1 = LB2-1 or LB2=UB1+1.
        '''
        from theorems import sum_split_after, sum_split_before
        from proveit.numbers.common import one
        from proveit.numbers import Sub, Add
        if not isinstance(
                self.domain,
                Interval) or not isinstance(
                second_summation.domain,
                Interval):
            raise Exception(
                'Sum joining only implemented for Interval domains')
        if self.summand != second_summation.summand:
            raise Exception(
                'Sum joining only allowed when the summands are the same')
        if self.domain.upper_bound == Sub(
                second_summation.domain.lower_bound, one):
            sum_split = sum_split_before
            split_index = second_summation.domain.lower_bound
        elif second_summation.domain.lower_bound == Add(self.domain.upper_bound, one):
            sum_split = sum_split_after
            split_index = self.domain.upper_bound
        else:
            raise Exception(
                'Sum joining only implemented when there is an explicit increment of one from the upper bound and the second summations lower bound')
        lower_bound, upper_bound = self.domain.lower_bound, second_summation.domain.upper_bound
        deduce_in_integer(lower_bound, assumptions)
        deduce_in_integer(upper_bound, assumptions)
        deduce_in_integer(split_index, assumptions)
        return sum_split.instantiate({Operation(f, self.instance_vars): self.summand}).instantiate(
            {a: lower_bound, b: split_index, c: upper_bound, x: self.indices[0]}).derive_reversed()

    # def split(self, split_index, side='after', assumptions=frozenset()):
    #     r'''
    #     Splits summation over one Interval {a ... c} into two summations.
    #     If side == 'after', it splits into a summation over {a ... split_index} plus
    #     a summation over {split_index+1 ... c}.  If side == 'before', it splits into
    #     a summation over {a ... split_index-1} plus a summation over {split_index ... c}.
    #     As special cases, split_index==a with side == 'after' splits off the first single
    #     term.  Also, split_index==c with side == 'before' splits off the last single term.
    #     r'''
    #     if not isinstance(self.domain, Interval):
    #         raise Exception(
    #             'Sum splitting only implemented for Interval domains')
    #     if side == 'before' and self.domain.upper_bound == split_index:
    #         return self.split_off_last()
    #     if side == 'after' and self.domain.lower_bound == split_index:
    #         return self.split_off_first()
    #     if isinstance(self.domain, Interval) and self.instance_vars.is_single():
    #         from theorems import sum_split_after, sum_split_before
    #         sum_split = sum_split_after if side == 'after' else sum_split_before
    #         deduce_in_integer(self.domain.lower_bound, assumptions)
    #         deduce_in_integer(self.domain.upper_bound, assumptions)
    #         deduce_in_integer(split_index, assumptions)
    #         # Also needs lower_bound <= split_index and split_index <
    #         # upper_bound
    #         return sum_split.instantiate({Operation(f, self.instance_vars): self.summand}).instantiate(
    #             {a: self.domain.lower_bound, b: split_index, c: self.domain.upper_bound, x: self.indices[0]})
    #     raise Exception(
    #         "split_off_last only implemented for a summation over a Interval of one instance variable")

    def split(self, split_index, side='after', simplify_idx=True,
              assumptions=USE_DEFAULTS):
        r'''
        Splits summation over one integral Interval {a ... c} into two
        summations. If side == 'after', it splits into a summation over
        {a ... split_index} plus a summation over {split_index+1 ... c}.
        If side == 'before', it splits into a summation over
        {a ... split_index-1} plus a summation over {split_index ... c}.
        As special cases, split_index==a with side == 'after' splits
        off the first single term.  Also, split_index==c with
        side == 'before' splits off the last single term.
        '''
        if not isinstance(self.domain, Interval):
            raise Exception(
                'Sum splitting only implemented for Interval domains')
        if side == 'before' and self.domain.upper_bound == split_index:
            return self.split_off_last()
        if side == 'after' and self.domain.lower_bound == split_index:
            return self.split_off_first()
        if isinstance(self.domain, Interval) and self.instance_vars.is_single():
            from theorems import sum_split_after, sum_split_before
            sum_split = sum_split_after if side == 'after' else sum_split_before
            deduce_in_integer(self.domain.lower_bound, assumptions)
            deduce_in_integer(self.domain.upper_bound, assumptions)
            deduce_in_integer(split_index, assumptions)
            # Also needs lower_bound <= split_index and split_index <
            # upper_bound
            return sum_split.instantiate({Operation(f, self.instance_vars): self.summand}).instantiate(
                {a: self.domain.lower_bound, b: split_index, c: self.domain.upper_bound, x: self.indices[0]})
        raise Exception(
            "split_off_last only implemented for a summation over a Interval of one instance variable")

    def split_off_last(self, assumptions=frozenset()):
        from axioms import sum_split_last
        if isinstance(self.domain, Interval) and self.instance_vars.is_single():
            deduce_in_integer(self.domain.lower_bound, assumptions)
            deduce_in_integer(self.domain.upper_bound, assumptions)
            # Also needs lower_bound < upper_bound
            return sum_split_last.instantiate({Operation(f, self.instance_vars): self.summand}).instantiate(
                {a: self.domain.lower_bound, b: self.domain.upper_bound, x: self.indices[0]})
        raise Exception(
            "split_off_last only implemented for a summation over a Interval of one instance variable")

    def split_off_first(self, assumptions=frozenset()):
        from theorems import sum_split_first  # only for associative summation
        if isinstance(self.domain, Interval) and self.instance_vars.is_single():
            deduce_in_integer(self.domain.lower_bound, assumptions)
            deduce_in_integer(self.domain.upper_bound, assumptions)
            # Also needs lower_bound < upper_bound
            return sum_split_first.instantiate({Operation(f, self.instance_vars): self.summand}).instantiate(
                {a: self.domain.lower_bound, b: self.domain.upper_bound, x: self.indices[0]})
        raise Exception(
            "split_off_last only implemented for a summation over a Interval of one instance variable")

    def factorization(
            self,
            the_factor,
            pull="left",
            group_factor=True,
            group_remainder=None,
            assumptions=USE_DEFAULTS):
        '''
        If group_factor is True and the_factor is a product, it will be grouped together as a
        sub-product.  group_remainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complex so that
        the associative and commutation theorems are applicable.
        '''
        from proveit import ExprTuple, var_range
        from proveit.numbers.multiplication import distribute_through_summation
        from proveit.numbers import Mult, one
        if not free_vars(the_factor, err_inclusively=True).isdisjoint(
                self.instance_params):
            raise Exception(
                'Cannot factor anything involving summation indices '
                'out of a summation')
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr, assumptions)
        
        assumptions = defaults.checked_assumptions(assumptions)
        # We may need to factor the summand within the summation
        summand_assumptions = assumptions + self.conditions.entries
        summand_factorization = self.summand.factorization(
            the_factor,
            pull,
            group_factor=False,
            group_remainder=True,
            assumptions=summand_assumptions)
        gen_summand_factorization = summand_factorization.generalize(
                self.instance_params, conditions=self.conditions)
        expr = eq.update(expr.instance_substitution(gen_summand_factorization,
                                                    assumptions=assumptions))
        if isinstance(the_factor, Mult):
            factors = the_factor.factors
        else:
            factors = ExprTuple(the_factor)
        if pull == 'left':
            _a = factors
            _c = ExprTuple()
            summand_remainder = expr.summand.factors[-1]
        elif pull == 'right':
            _a = ExprTuple()
            _c = factors
            summand_remainder = expr.summand.factors[0]
        else:
            raise ValueError("'pull' must be 'left' or 'right', not %s"
                             %pull)
        _b = self.instance_params
        _i = _a.num_elements(assumptions)
        _j = _b.num_elements(assumptions)
        _k = _c.num_elements(assumptions)
        _P = Lambda(expr.instance_params, summand_remainder)
        _Q = Lambda(expr.instance_params, expr.condition)
        a_1_to_i = ExprTuple(var_range(a, one, _i))
        b_1_to_j = ExprTuple(var_range(b, one, _j))
        c_1_to_k = ExprTuple(var_range(c, one, _k))
        _impl = distribute_through_summation.instantiate(
                {i: _i, j: _j, k: _k, P:_P, Q:_Q, b_1_to_j: _b},
                assumptions=assumptions)
        quantified_eq = _impl.derive_consequent(assumptions)  
        eq.update(quantified_eq.instantiate(
                {a_1_to_i: _a, b_1_to_j:_b, c_1_to_k: _c}, 
                assumptions=assumptions))
        
        return eq.relation
    
    def deduce_bound(self, summand_relation, assumptions=USE_DEFAULTS):
        '''
        Given a universally quantified ordering relation over all 
        summand instances, return a bounding relation for the
        summation.  For example, using the summand relation
            \forall_{k in {m...n}} (a(k) <= b(k)),
        we can prove
            \sum_{l=m}^{n} a(l) <= \sum_{l=m}^{n} b(l)
        or using the summand relation
            \forall_{k in {m...n}} (a(k) < b(k)),
        and assuming m <= n, we can prove
            \sum_{l=m}^{n} a(l) < \sum_{l=m}^{n} b(l)
        '''
        from . import (weak_summation_from_summands_bound,
                       strong_summation_from_summands_bound)
        if not (self.instance_params.is_single()):
            raise NotImplementedError(
                    "sum.bound only currently implemented for summations "
                    "over a single parameter")
        if isinstance(summand_relation, Judgment):
            summand_relation = summand_relation.expr
        if not (isinstance(summand_relation, Forall) and
                summand_relation.instance_params.is_single() and
                (isinstance(summand_relation.instance_expr, Less) or
                 isinstance(summand_relation.instance_expr, LessEq))):
            raise ValueError("Expecting summand_relation to be a number "
                             "ordering relation (< or <=) universally "
                             "quantified over a single parameter, not %s"
                             %summand_relation)
        summand_lambda = Lambda(self.instance_param, self.summand)
        lesser_lambda = Lambda(summand_relation.instance_param, 
                               summand_relation.instance_expr.normal_lhs)
        greater_lambda = Lambda(summand_relation.instance_param, 
                                summand_relation.instance_expr.normal_rhs)
        if summand_lambda not in (lesser_lambda, greater_lambda):
            raise ValueError("Expecting summand_relation to be a universally "
                             "quantified number relation (< or <=) "
                             "involving the summand, %d, not %s"%
                             (self.summand, summand_relation))
        _a = lesser_lambda
        _b = greater_lambda
        _S = self.domain
        if isinstance(summand_relation.instance_expr, LessEq):
            # Use weak form
            sum_rel_impl = weak_summation_from_summands_bound.instantiate(
                    {a:_a, b:_b, S:_S}, assumptions=assumptions)
        else:
            # Use strong form
            sum_rel_impl = strong_summation_from_summands_bound.instantiate(
                    {a:_a, b:_b, S:_S}, assumptions=assumptions)
        sum_relation = sum_rel_impl.derive_consequent(assumptions)
        if summand_lambda == greater_lambda:
            return sum_relation.with_direction_reversed()
        return sum_relation

InnerExpr.register_equivalence_method(
    Sum, 'factorization', 'factorized', 'factor')
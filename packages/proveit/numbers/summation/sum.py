from proveit import (Expression, Literal, Lambda, Function, Operation,
                     OperationOverInstances, InnerExpr,
                     Judgment, free_vars, maybe_fenced, USE_DEFAULTS,
                     ProofFailure, defaults,
                     prover, relation_prover, equality_prover,
                     SimplificationDirectives, UnsatisfiedPrerequisites)
from proveit import a, b, c, f, i, j, k, l, m, x, Q, S
from proveit.logic import Forall, InSet
from proveit.numbers import one, Add, Neg, subtract
from proveit.numbers import (ZeroSet, Complex, Integer, Interval, Natural,
                             NaturalPos, Rational, Real, RealInterval,
                             readily_provable_number_set)
from proveit.numbers.ordering import Less, LessEq
from proveit import TransRelUpdater


class Sum(OperationOverInstances):
    # operator of the Sum operation.
    _operator_ = Literal(
        string_format='Sum',
        latex_format=r'\sum',
        theory=__file__)
    _init_argname_mapping_ = {'index_or_indices': 'instance_param_or_params',
                              'summand': 'instance_expr'}

    _simplification_directives_ = SimplificationDirectives(
            pull_out_index_indep_factors=True)

    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in
        basiclogic.booleanss):
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
            conditions=conditions, styles=styles, _lambda_map=_lambda_map)
        if hasattr(self, 'instance_param'):
            self.index = self.instance_param
        if hasattr(self, 'instance_params'):
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

    def _build_canonical_form(self):
        '''
        Returns a canonical form of this Sum with any 
        index-independent factors pulled out in front.
        '''
        from proveit.numbers import Mult
        canonical_summand = self.summand.canonical_form()
        if isinstance(canonical_summand, Mult):
            # Pull any index-independent scalar factors in front.
            index_indep_factors = []
            index_dep_factors = []
            for factor in canonical_summand.factors:
                if free_vars(factor).isdisjoint(self.indices):
                    index_indep_factors.append(factor)
                else:
                    index_dep_factors.append(factor)
            if len(index_indep_factors) > 0:
                # Pulling out some index-independent scalar factors.
                if len(index_dep_factors) > 0:
                    # Keeping some index-dependent scalar factors
                    # within the VecSum.
                    canonical_summand = Mult(
                            *index_dep_factors).canonical_form()
                else:
                    canonical_summand = one
                # Build/return the Mult with the Sum.
                _sum = Sum(self.indices, canonical_summand,
                      conditions=self.conditions.canonical_form())
                return Mult(
                        Mult(*index_indep_factors), _sum).canonical_form()
        # Build the canonical VecSum.
        return Sum(self.indices, canonical_summand,
                   conditions=self.conditions.canonical_form())

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from . import (summation_zero_closure, summation_nat_closure,
                       summation_nat_pos_closure, summation_int_closure, 
                       summation_real_closure, summation_complex_closure)
        _x = self.instance_param
        _f = Lambda(_x, self.instance_expr)
        _Q = Lambda(_x, self.condition)

        if number_set == ZeroSet:
            thm = summation_zero_closure
        elif number_set == Natural:
            thm = summation_nat_closure
        elif number_set == NaturalPos:
            thm = summation_nat_pos_closure
        elif number_set == Integer:
            thm = summation_int_closure
        elif number_set == Real:
            thm = summation_real_closure
        elif number_set == Complex:
            thm = summation_complex_closure
        else:
            raise NotImplementedError(
                "'Sum.deduce_in_number_set' not implemented for the %s set"
                % str(number_set))
        impl = thm.instantiate({ x: _x, f: _f, Q: _Q})
        antecedent = impl.antecedent
        if not antecedent.proven():
            # Conclude the antecedent via generalization.
            antecedent.conclude_via_generalization()
        return impl.derive_consequent()

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        with defaults.temporary() as tmp_defaults:
            tmp_defaults.assumptions = defaults.assumptions + tuple(
                    self.conditions)
            summand_ns = readily_provable_number_set(self.summand)
        if summand_ns is None:
            return None
        if summand_ns == ZeroSet:
            return ZeroSet
        if summand_ns in (Natural, NaturalPos, Integer, Real, Complex):
            # We have proven closure for these.
            # ToDo: implement more closure.
            return summand_ns
        if Integer.readily_includes(summand_ns): return Integer
        if Rational.readily_includes(summand_ns): return Rational
        if Real.readily_includes(summand_ns): return Real
        return Complex

    def _formatted(self, format_type, **kwargs):
        # MUST BE UPDATED TO DEAL WITH 'joining' NESTED LEVELS
        fence = kwargs['fence'] if 'fence' in kwargs else False
        explicit_conds = self.explicit_conditions()          
        if isinstance(self.domain, Interval) and len(explicit_conds)==0:
            formatted_operator = self.operator.formatted(format_type)
            formatted_index = self.index.formatted(format_type)
            formatted_lower = self.domain.lower_bound.formatted(format_type)
            formatted_upper = self.domain.upper_bound.formatted(format_type)
            formatted_summand = self.summand.formatted(format_type, fence=True)
            formatted_inner = "%s_{%s = %s}^{%s} %s"%(
                    formatted_operator, formatted_index,
                    formatted_lower, formatted_upper, formatted_summand)
            return maybe_fenced(format_type, formatted_inner, fence=fence)
        else:
            return OperationOverInstances._formatted(self, format_type,
                                                     fence=fence)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Sum
        expression assuming the operands have been simplified.

        For the trivial case of summing over only one item (currently
        implemented just for a Interval where the endpoints are equal),
        derive and return this summation expression equated with the
        simplified form of the single term.
        Assumptions may be necessary to deduce necessary conditions
        for the simplification.
        NEEDS UPDATING
        '''
        from proveit.logic import TRUE, SimplificationError
        from proveit.numbers import Mult
        from . import sum_single, trivial_sum
        summand = self.summand
        if (isinstance(self.domain,Interval) and
            self.domain.lower_bound == self.domain.upper_bound):
            if hasattr(self, 'index'):
                return sum_single.instantiate(
                    {Function(f, self.index): summand,
                     a: self.domain.lower_bound})
        if (isinstance(self.domain,Interval) and
                self.instance_param not in free_vars(summand)
                and self.non_domain_condition()==TRUE):
            # Trivial sum: summand independent of parameter.
            _a = self.domain.lower_bound
            _b = self.domain.upper_bound
            _x = summand
            return trivial_sum.instantiate(
                    {a:_a, b:_b, x:_x})
        if Sum._simplification_directives_.pull_out_index_indep_factors:
            if isinstance(summand, Mult):
                index_indep_factors = []
                for factor in summand.factors:
                    if free_vars(factor).isdisjoint(self.indices):
                        index_indep_factors.append(factor)
                return self.factorization(index_indep_factors, pull='left',
                                          group_factors=False)

        raise SimplificationError(
            "Sum simplification only implemented for a summation over an "
            "integer Interval of one instance variable where the upper "
            "and lower bounds are the same.")

    @equality_prover('geom_sum_reduced', 'geom_sum_reduce')
    def geom_sum_reduction(self, **defaults_config):
        r'''
        If this summation is in the form of a geometric sum
        (finite or infinite), equate it to an analytical form.

        Examples:
        ∑_{n=0}^{∞} x^n = 1 / (1 - x)
        ∑_{n=j}^{k} x^n = (x^{k + 1} - x^j) / (x - 1)
        '''
        from . import inf_geom_sum, gen_finite_geom_sum
        from proveit.numbers import zero, infinity

        try:
            #            self.r = extract_exp_base(self.summand)
            _x_sub = self.summand.base
        except BaseException:
            raise ValueError("Summand not an exponential!")
        if not isinstance(self.domain, Interval):
            raise ValueError("Not explicitly summing over Interval!")
        else:
            if (self.domain.lower_bound == zero and
                    self.domain.upper_bound == infinity):
                # We're in the infinite geom sum domain!
                _m = self.indices[0]
                return inf_geom_sum.instantiate({x: _x_sub, m: _m})
            else:
                # We're in the finite geom sum domain!
                _x, _j, _k = gen_finite_geom_sum.all_instance_params()
                # _i = gen_finite_geom_sum.instance_expr.instance_expr.lhs.indices
                _i = gen_finite_geom_sum.instance_expr.instance_expr.lhs.index
                # _i_sub = self.indices[0]
                _i_sub = self.index
                _j_sub = self.domain.lower_bound
                _k_sub = self.domain.upper_bound
                return gen_finite_geom_sum.instantiate(
                    {x: _x_sub, _i: _i_sub, j: _j_sub, _k: _k_sub})
#        else:
#            print "Not a geometric sum!"

    @equality_prover('shifted', 'shift')
    def shifting(self, shift_amount, **defaults_config):
        '''
        Shift the summation indices by the shift_amount, and shift
        the summand by a corresponding compensating amount, deducing
        and returning the equivalence of this summation with the
        index-shifted version.
        This shift() method is implemented only for a Sum with a single
        index and only when the domain is an integer Interval.
        Eventually this should also be implemented for domains of
        Natural, NaturalPos, etc.
        Example: Let S = Sum(i, i+2, Interval(0, 10)). Then S.shift(one)
        will return |- S = Sum(i, i+1, Interval(1, 11)).
        '''
        if not hasattr(self, 'index'):
            raise NotImplementedError(
                "Sum.shifting() only implemented for summations with a single "
                "index over an Interval. The sum {} has indices {}."
                .format(self, self.indices))
        # The following constraint can eventually be modified to deal
        # with a domain like all Natural … but for now limited to
        # integer Interval domain.
        if not isinstance(self.domain, Interval):
            raise NotImplementedError(
                "Sum.shifting() only implemented for summations with a single "
                "index over an Interval. The sum {} has domain {}."
                .format(self, self.domain))

        from . import index_shift

        _x = self.index
        _a = self.domain.lower_bound
        _b = self.domain.upper_bound
        _c = shift_amount

        f_op, f_op_sub = Function(f, self.index), self.summand

        """
        # SHOULD BE HANDLED VIA AUTO-SIMPLIFICATION NOW.

        # Create some (possible) reduction formulas for the shifted
        # components, which will then be passed through to the
        # instantiation as "reductions" for simpifying the final form
        # of the indices and summand. Notice that when attempting to
        # simplify the summand, we need to send along the assumption
        # about the index domain. If the (supposed) reduction is
        # trivial (like |– x = x), the eventual instantiation process
        # will ignore/eliminate it.
        replacements = list(defaults.replacements)
        if (simplify_idx):
            lower_bound_shifted = (
                Add(_a, _c).simplification(
                    shallow=True, assumptions=assumptions))
            replacements.append(lower_bound_shifted)
            upper_bound_shifted = (
                Add(_b, _c).simplification(
                    shallow=True, assumptions=assumptions))
            replacements.append(upper_bound_shifted)
        if (simplify_summand):
            summand_shifted = f_op_sub.basic_replaced({_i:subtract(_i, _c)})
            summand_shifted = (
                summand_shifted.simplification(shallow=True,
                    assumptions=[*assumptions, InSet(_i, Interval(_a, _b))]))
            replacements.append(summand_shifted)
        """

        return index_shift.instantiate(
            {f_op: f_op_sub, x: _x, a: _a, b: _b, c: _c})

    @prover
    def joining(self, second_summation, **defaults_config):
        '''
        Join the "second summation" with "this" (self) summation,
        deducing and returning the equivalence of the sum of the self
        and second_summation with the joined summation.
        Both summations must be over integer Intervals.
        The relation between the first summation upper bound, UB1,
        and the second summation lower bound, LB2, must be *explicitly*
        either UB1 = LB2-1 or LB2=UB1+1 *or* easily-derivable
        mathematical equivalents of those equalities.
        Example usage: let S1 = Sum(i, i^2, Interval(1,10)) and
        S2 = Sum(i, i^2, Interval(1,10)). Then S1.join(S2) returns
        |- S1 + S2 = Sum(i, i^2, Interval(1,20))
        '''

        if (not isinstance(self.domain,Interval) or
            not isinstance(second_summation.domain,Interval)):
            raise NotImplementedError(
                "Sum.join() is only implemented for summations with a "
                "single index over an integer Interval. The sum {0} has "
                "indices {1} and domain {2}; the sum {3} has indices "
                "{4} and domain {5}.".
                format(self, self.indices, self.domain, second_summation,
                       second_summation.indices, second_summation.domain))

        if self.summand != second_summation.summand:
            raise ValueError(
                "Sum joining using Sum.join() is only allowed when the "
                "summands are identical. The sum {0} has summand {1} "
                "while the sum {2} has summand {3}. If the summands are "
                "equal but do not appear identical, you will have to "
                "establish an appropriate substituion before calling the "
                "Sum.join() method.".
                format(self, self.summand, second_summation,
                       second_summation.summand))

        from . import sum_split_after, sum_split_before
        from proveit import a

        _i = self.index
        _a1 = self.domain.lower_bound
        _b1 = self.domain.upper_bound
        _a2 = second_summation.domain.lower_bound
        _b2 = second_summation.domain.upper_bound
        f_op, f_op_sub = Function(f, self.index), self.summand

        # Create low-effort, simplified versions of transition index
        # values, if possible
        _b1_plus_1_simplified = Add(_b1, one).shallow_simplified()
        _a2_minus_1_simplified = subtract(_a2, one).shallow_simplified()

        # This breaks into four cases (despite the temptation to
        # combine some of the cases):
        if (_b1 == subtract(_a2, one)):
            # UB1 == LB2 - 1 (literally)
            sum_split = sum_split_before
            split_index = _a2
        elif (_a2 == Add(_b1, one)):
            # LB2 == UB1 + 1 (literally)
            sum_split = sum_split_after
            split_index = _b1
        elif (_b1 == _a2_minus_1_simplified):
            # UB1 == LB2 - 1 (after simplification)
            sum_split = sum_split_before
            split_index = _a2
        elif (_a2 == _b1_plus_1_simplified):
            # LB2 == UB1 + 1 (after simplification)
            sum_split = sum_split_after
            split_index = _b1
        else:
            raise UnsatisfiedPrerequisites(
                "Sum joining using Sum.join() only implemented for when "
                "there is an explicit (or easily verified) increment "
                "of one unit from the first summation's upper bound "
                "to the second summation's lower bound (or decrement "
                "of one unit from second summation's lower bound to "
                "first summation's upper bound). We have first "
                "summation upper bound of {0} with the second summation "
                "lower bound of {1}. If these appear to have the "
                "necessary relationship, you might need to prove this "
                "before calling the Sum.join() method.".
                format(_b1, _a2))

        # Preserve the original summations that will be on the
        # left side of the equation.
        preserved_exprs = set(defaults.preserved_exprs)
        preserved_exprs.add(self)
        preserved_exprs.add(second_summation)

        return sum_split.instantiate(
            {f_op: f_op_sub, a: _a1, b: split_index, c: _b2, x: _i},
            preserved_exprs=preserved_exprs).derive_reversed()

    @equality_prover('partitioned', 'split')
    def partition(self, split_index, side='after', **defaults_config):
        r'''
        Split summation over one integral Interval {a ... c} into two
        summations. If side == 'after', it splits into a summation over
        {a ... split_index} plus a summation over {split_index+1 ... c}.
        If side == 'before', it splits into a summation over
        {a ... split_index-1} plus a summation over {split_index ... c},
        deducing and returning the equivalence of this summation with
        the split version. When the simplify_idx is True, a shallow
        simplification is applied to the new indices (for example,
        a new index of i = 4 + 1 may be expressed as i = 5).
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This split() method is implemented only for a Sum with a single
        index and only when the domain is an integer Interval.
        Eventually this should also be implemented for domains of
        Natural, NaturalPos, etc.
        As special cases, split_index==a with side == 'after' splits
        off the first single term.  Also, split_index==c with
        side == 'before' splits off the last single term.
        Example usage: Let S = Sum(i, i+2, Interval(0, 10)). Then
        S.split(four, side='after') will return
        |- S = Sum(i, i+2, Interval(0, 4)) +
               Sum(i, i+2, Interval(5, 10))
        '''
        # The following constraint can eventually be modified to allow
        # a domain like Natural or NaturalPos, but for now limited
        # to integer Interval domain.
        if (not isinstance(self.domain, Interval) or
                not hasattr(self, 'index')):
            raise NotImplementedError(
                "Sum.partition() only implemented for summations with a single "
                "index over an integer Interval. The sum {} has indices {} "
                "and domain {}."
                .format(self, self.indices, self.domain))

        # Special cases: splitting off last or first item
        if side == 'before' and self.domain.upper_bound == split_index:
            return self.partition_last()
        if side == 'after' and self.domain.lower_bound == split_index:
            return self.partition_first()

        _i = self.index
        _a = self.domain.lower_bound
        _b = split_index
        _c = self.domain.upper_bound
        f_op, f_op_sub = Function(f, self.index), self.summand

        """
        # SHOULD BE HANDLED VIA AUTO-SIMPLIFICATION NOW.

        # Create a (possible) reduction formula for the split
        # components' index expression, which will then be passed
        # through to the instantiation as a "reduction" for simpifying
        # the final form of the indices. If the (supposed) reduction is
        # trivial (like |– x = x), the eventual instantiation process
        # will ignore/eliminate it.
        if (simplify_idx):
            # 2 Cases to consider: side = 'after' vs. side = 'before'
            if side == 'after':
                # simplify lower index expr for 2nd sum of split
                new_idx = Add(_b, one).simplification(
                        shallow=True, assumptions=assumptions)
            else:
                # simplify upper index expr for 1st sum of split
                new_idx = subtract(_b, one).simplification(
                        shallow=True, assumptions=assumptions)
            user_reductions = [*user_reductions, new_idx]
        """

        from . import sum_split_after, sum_split_before
        sum_split = sum_split_after if side == 'after' else sum_split_before
        return sum_split.instantiate(
                {f_op: f_op_sub, a: _a, b: _b, c: _c, x: _i})

    @equality_prover('last_partitioned', 'split_last')
    def partition_last(self, **defaults_config):
        '''
        Split a summation over an integral Interval {a ... c} into a
        sum of: a new summation over the integral Interval {a ... (c-1)}
        and the final term evaluated at the upper bound, deducing and
        returning the equivalence of this summation with
        the new split version. When the simplify_idx is True, a shallow
        simplification is applied to the new indices (for example,
        a new index of i = 4 + 1 may be expressed as i = 5). When the
        simplify_summand = True, a shallow simplification is applied to
        the upper term that has been peeled off by itself.
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This split_off_last() method is implemented only for a Sum
        with a single index and only when the domain is an integer
        Interval. Eventually this should also be implemented for
        domains of Natural, NaturalPos, etc. split_off_last() is called
        from Sum.split() for special cases.
        Example usage: Let S = Sum(i, i+2, Interval(0, 10)). Then
        S.split_off_last() will return
        |- S = Sum(i, i+2, Interval(0, 9)) + 12
        '''
        if isinstance(self.domain, Interval) and hasattr(self, 'index'):

            from . import sum_split_last

            _i = self.index
            _a = self.domain.lower_bound
            _b = self.domain.upper_bound
            f_op, f_op_sub = Function(f, self.index), self.summand

            """
            # SHOULD BE HANDLED VIA AUTO-SIMPLIFICATION NOW.

            # Create (possible) reduction formulas for the upper
            # index expression of the resulting sum, and for the
            # resulting final term extracted from the sum, which will
            # then be passed through to the instantiation as reductions
            # for simpifying the final form of the indices and split-off
            # term. If any (supposed) reduction is trivial
            # (like |– x = x), the eventual instantiation process will
            # ignore/eliminate it.
            if (simplify_idx):
                # Just 1 case to address:
                # simplify upper index of resulting remaining sum
                new_idx = subtract(_b, one).simplification(
                            shallow=True, assumptions=assumptions)
                user_reductions = [*user_reductions, new_idx]
            if simplify_summand:
                # Simplify the summand for the last item
                new_summand = f_op_sub.basic_replaced({_i: _b})
                new_summand = new_summand.simplification(shallow=True,
                        assumptions=assumptions)
                user_reductions = [*user_reductions, new_summand]
            """

            return sum_split_last.instantiate(
                {f_op: f_op_sub, a: _a, b: _b, x: _i})
        raise UnsatisfiedPrerequisites(
                "Sum.partition_last() only implemented for summations with a "
                "single index over an integer Interval. The sum {} has "
                "index or indices {} and domain {}."
                .format(self, self.indices, self.domain))

    @equality_prover('first_partitioned', 'split_first')
    def partition_first(self, **defaults_config):
        '''
        Split a summation over an integral Interval {a ... c} into a
        sum of: the first term in the sum and a new summation over the
        integral Interval {a+1 ... c}, deducing and
        returning the equivalence of this summation with
        the new split version. When the simplify_idx is True, a shallow
        simplification is applied to the new indices (for example,
        a new index of i = 4 + 1 may be expressed as i = 5). When the
        simplify_summand = True, a shallow simplification is applied to
        the lower term that has been peeled off by itself.
        Eventually plan to accept and act on user-supplied reductions
        as well, but not implemented at this time.
        This split_off_last() method is implemented only for a Sum
        with a single index and only when the domain is an integer
        Interval. Eventually this should also be implemented for
        domains of Natural, NaturalPos, etc. split_off_last() is called
        from Sum.split() for special cases.
        Example usage: Let S = Sum(i, i+2, Interval(1, 10)). Then
        S.split_off_first() will return
        |- S = 3 + Sum(i, i+2, Interval(2, 10))
        '''

        if isinstance(self.domain, Interval) and hasattr(self, 'index'):

            from . import sum_split_first

            _i = self.index
            _a = self.domain.lower_bound
            _b = self.domain.upper_bound
            f_op, f_op_sub = Function(f, self.index), self.summand

            """
            # SHOULD BE HANDLED VIA AUTO-SIMPLIFICATION NOW.

            # Create (possible) reduction formulas for the lower
            # index expression of the resulting sum, and for the
            # resulting first term extracted from the sum, which will
            # then be passed through to the instantiation as reductions
            # for simpifying the final form of the indices and split-off
            # term. If any (supposed) reduction is trivial
            # (like |– x = x), the eventual instantiation process will
            # ignore/eliminate it.
            if simplify_idx:
                # Just 1 case to address:
                # simplify lower index of resulting remaining sum
                new_idx = Add(_a, one).simplification(
                            shallow=True, assumptions=assumptions)
                user_reductions = [*user_reductions, new_idx]
            if simplify_summand:
                # Simplify the summand for the first item
                new_summand = f_op_sub.basic_replaced({_i: _a})
                new_summand = new_summand.simplification(shallow=True,
                        assumptions=assumptions)
                user_reductions = [*user_reductions, new_summand]
            """

            return sum_split_first.instantiate(
                {f_op: f_op_sub, a: _a, b: _b, x: _i})

        raise NotImplementedError(
                "Sum.split_off_first() only implemented for summations with a "
                "single index over an integer Interval. The sum {} has "
                "index or indices {} and domain {}."
                .format(self, self.indices, self.domain))

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factors, pull="left", group_factors=True,
                      group_remainder=None, **defaults_config):
        '''
        Return the proven factorization (equality with the factored
        form) from pulling the factor(s) from this summation to the 
        "left" or "right".
        If group_factors is True, the factors will be grouped together 
        as a sub-product.  group_remainder is not relevant kept for 
        compatibility with other factor methods.
        '''
        from proveit import ExprTuple, var_range, IndexedVar
        from proveit.numbers.multiplication import distribute_through_summation
        from proveit.numbers import Mult, one
        if not isinstance(the_factors, Expression):
            # If 'the_factors' is not an Expression, assume it is
            # an iterable and make it a Mult.
            the_factors = Mult(*the_factors)            
        if not free_vars(the_factors).isdisjoint(self.instance_params):
            raise ValueError(
                'Cannot factor anything involving summation indices '
                'out of a summation')
        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        # We may need to factor the summand within the summation
        summand_assumptions = defaults.assumptions + self.conditions.entries
        summand_factorization = self.summand.factorization(
            the_factors,
            pull,
            group_factors=group_factors,
            group_remainder=True,
            assumptions=summand_assumptions)
        if summand_factorization.lhs != summand_factorization.rhs:
            gen_summand_factorization = summand_factorization.generalize(
                    self.instance_params, conditions=self.conditions)
            expr = eq.update(expr.instance_substitution(gen_summand_factorization,
                                                        preserve_all=True))
        if not group_factors and isinstance(the_factors, Mult):
            factors = the_factors.factors
        else:
            factors = ExprTuple(the_factors)
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
        _i = _a.num_elements()
        _j = _b.num_elements()
        _k = _c.num_elements()
        _f = Lambda(expr.instance_params, summand_remainder)
        _Q = Lambda(expr.instance_params, expr.condition)
        _impl = distribute_through_summation.instantiate(
                {i: _i, j: _j, k: _k, f:_f, Q:_Q, b:_b},
                preserve_all=True)
        quantified_eq = _impl.derive_consequent(preserve_all=True)
        eq.update(quantified_eq.instantiate(
                {a: _a, c: _c}, preserve_all=True))

        return eq.relation

    @relation_prover
    def deduce_bound(self, summand_relation, **defaults_config):
        r'''
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
                             "involving the summand {0} not {1}.".
                             format(self.summand, summand_relation))
        _a = lesser_lambda
        _b = greater_lambda
        _S = self.domain
        if isinstance(summand_relation.instance_expr, LessEq):
            # Use weak form
            sum_rel_impl = weak_summation_from_summands_bound.instantiate(
                    {a:_a, b:_b, S:_S}, preserve_all=True)
        else:
            # Use strong form
            sum_rel_impl = strong_summation_from_summands_bound.instantiate(
                    {a:_a, b:_b, S:_S}, preserve_all=True)
        sum_relation = sum_rel_impl.derive_consequent()
        if summand_lambda == greater_lambda:
            return sum_relation.with_direction_reversed()
        return sum_relation

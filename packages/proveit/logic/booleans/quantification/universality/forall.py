from proveit import (Literal, Function, OperationOverInstances,
                     ExprTuple, ExprRange, IndexedVar,
                     defaults, USE_DEFAULTS, ProofFailure)
from proveit import k, n, x, A, B, P, S
from proveit._core_.proof import Generalization


class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(string_format='forall', latex_format=r'\forall',
                         theory=__file__)
    
    # Map instance expressions to universal quantifications
    # over them that are known judgments.
    known_instance_exprs = dict()

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create a Forall expression:
        forall_{instance_param_or_params | conditions} instance_expr.
        This expresses that the instance_expr is true for all values of the
        instance parameter(s) given that the optional condition(s) is/are
        satisfied.  The instance parameter(s) and condition(s)
        may be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(
            self, Forall._operator_, instance_param_or_params,
            instance_expr, domain=domain, domains=domains,
            condition=condition, conditions=conditions,
            _lambda_map=_lambda_map)
    
    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for this
        forall operation.
        '''
        if (hasattr(self, 'instance_param') and self.has_domain()
                and hasattr(self.domain, 'unfold_forall')):

            if self.conditions.num_entries() == 0:
                # derive an unfolded version (dependent upon the domain)
                yield self.unfold
        # Remember the proven Universal judgments by their
        # instance expressions.
        Forall.known_instance_exprs.setdefault(
                judgment.expr.instance_expr, set()).add(judgment)

    def conclude(self, assumptions):
        '''
        If the instance expression, or some instance expression of
        nested universal quantifiers, is known to be true, conclude
        via generalization.  Otherwise, if the domain has a 'fold_forall'
        method, attempt to conclude this Forall statement
        via 'conclude_as_folded'.
        '''
        from proveit.logic import SubsetEq

        instance_expr = self.instance_expr
        
        # first try to prove via generalization without automation
        assumptions = defaults.checked_assumptions(assumptions)
        expr = self
        instance_param_lists = []
        conditions = []
        while isinstance(expr, Forall):
            new_params = expr.explicit_instance_params()
            instance_param_lists.append(list(new_params))
            conditions += list(expr.conditions.entries)
            expr = expr.instance_expr
            new_assumptions = assumptions + tuple(conditions)
            if expr.proven(assumptions=assumptions + tuple(conditions)):
                proven_inst_expr = expr.prove(new_assumptions)
                return proven_inst_expr.generalize(instance_param_lists,
                                                   conditions=conditions)
        
        if (self.has_domain() and self.instance_params.is_single 
                and self.conditions.is_single()):
            domain = self.domain 
            known_domains = set()
            # Next, check the known quantified instance expressions
            # and known set inclusions of domains to see if we can 
            # construct a proof via inclusive universal quantification.
            if instance_expr in Forall.known_instance_exprs:
                known_foralls = Forall.known_instance_exprs[instance_expr]
                for known_forall in known_foralls:
                    if (known_forall.has_domain() 
                            and known_forall.instance_params.is_single()
                            and known_forall.conditions.is_single()):
                        if known_forall.is_sufficient(assumptions):
                            known_domains.add(known_forall.domain)
            print('known_domains', known_domains)
            if len(known_domains) > 0 and domain in SubsetEq.known_right_sides:
                # We know this quantification in other domain(s).
                # Do any of those include this domain?
                for known_inclusion in SubsetEq.known_right_sides[domain]:
                    print('known_inclusion', known_inclusion)
                    if known_inclusion.is_sufficient(assumptions):
                        superset = known_inclusion.lhs
                        if superset in known_domains:
                            # We know the quantification over a s
                            # uperset.  We can use 
                            # inclusive_universal_quantification.
                            return self.conclude_via_domain_inclusion(
                                    self, superset, assumptions=assumptions)
        
        # The next 2 'ifs', one for prove_by_cases and one for
        # conclude_as_folded can eventually be merged as we eliminate the
        # separate conclude_as_folded() method. Keeping both for now
        # to ensure no problems as we transition.

        if self.has_domain() and hasattr(self.first_domain(), 'prove_by_cases'):
            try:
                return self.conclude_by_cases(assumptions)
            except Exception:
                raise ProofFailure(self, assumptions,
                                   "Unable to conclude automatically; the "
                                   "prove_by_cases method on the domain "
                                   "has failed. :o( ")

        # next try 'fold_as_forall' on the domain (if applicable)
        if self.has_domain() and hasattr(self.first_domain(), 'fold_as_forall'):
            # try fold_as_forall first
            try:
                return self.conclude_as_folded(assumptions)
            except Exception:
                raise ProofFailure(self, assumptions,
                                   "Unable to conclude automatically; "
                                   "the 'fold_as_forall' method on the "
                                   "domain failed.")
        else:
            # If there is no 'fold_as_forall' strategy to try, we can
            # attempt a different non-trivial strategy of proving
            # via generalization with automation.
            try:
                conditions = list(self.conditions.entries)
                proven_inst_expr = self.instance_expr.prove(
                    assumptions=assumptions + tuple(conditions))
                instance_param_lists = [list(self.explicit_instance_params())]
                # see if we can generalize multiple levels
                # simultaneously for a shorter proof
                while isinstance(proven_inst_expr.proof(), Generalization):
                    new_params = proven_inst_expr.explicit_instance_params()
                    instance_param_lists.append(list(new_params))
                    conditions += proven_inst_expr.conditions.entries
                    proven_inst_expr = (
                        proven_inst_expr.proof().required_truths[0])
                return proven_inst_expr.generalize(instance_param_lists,
                                                   conditions=conditions)
            except ProofFailure:
                raise ProofFailure(self, assumptions,
                                   "Unable to conclude automatically; "
                                   "the domain has no 'fold_as_forall' method "
                                   "and automated generalization failed.")

        raise ProofFailure(self, assumptions,
                           "Unable to conclude automatically; a "
                           "universally quantified instance expression "
                           "is not known to be true and the domain has "
                           "no 'fold_as_forall' method.")

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From this forall statement, derive an "unfolded" version
        dependent upon the domain of the forall, calling unfold_forall
        on the condition. For example, from
        forall_{A in BOOLEANS} P(A),
        derives P(TRUE) and P(FALSE).
        '''
        assert self.has_domain(), (
            "Cannot unfold a forall statement with no domain")
        return self.domain.unfold_forall(self, assumptions)

    """
    def equate_with_unfolded(self):
        pass
    """

    # Eventually the conclude_by_cases() method will replace the
    # conclude_as_folded() method. Maintaining both temporarily to
    # ensure continued compatibility across the system.

    def conclude_by_cases(self, assumptions=USE_DEFAULTS):
        '''
        Conclude this forall statement from an "unfolded" version
        dependent upon the domain of the forall, calling prove_by_cases
        on the domain. For example, conclude
        forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''
        assert self.has_domain(), (
            "Forall.conclude_by_cases: cannot fold a forall statement, or "
            "prove a forall statement using proof by cases, if the forall "
            "statement has no domain specified.")
        if self.instance_params.num_entries() > 1:
            # When there are more than one instance variables, we
            # must conclude the unbundled form first and then
            # derive the bundled form from that.
            unbundled = self.unbundle_equality(assumptions=assumptions).rhs
            unbundled = unbundled.conclude_by_cases(assumptions)
            return unbundled.bundle(assumptions=assumptions)
        return self.domain.prove_by_cases(self, assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Conclude this forall statement from an "unfolded" version
        dependent upon the domain of the forall,
        calling fold_as_forall on the condition.
        For example, conclude
        forall_{A in BOOLEANS} P(A) from P(TRUE) and P(FALSE).
        '''
        assert self.has_domain(), (
            "Cannot fold a forall statement with no domain")
        if self.instance_params.num_entries() > 1:
            # When there are more than one instance variables, we
            # must conclude the unbundled form first and the
            # derive the bundled form from that.
            unbundled = self.unbundle_equality(assumptions=assumptions).rhs
            unbundled = unbundled.conclude_as_folded(assumptions)
            return unbundled.bundle(assumptions=assumptions)
        blah = self.domain.fold_as_forall(self, assumptions)
        return blah
    
    def conclude_via_domain_inclusion(self, superset_domain,
                                      assumptions=USE_DEFAULTS):
        '''
        Conclude this forall statement from a similar forall statement
        over a broader domain.  For example, conclude
        forall_{x in B} P(x) from forall_{x in A} P(x)
        given A superset_eq B.
        '''
        from proveit.logic.sets.inclusion import (
                inclusive_universal_quantification)
        if not (self.has_domain() and self.instance_params.is_single 
                and self.conditions.is_single()):
            raise ValueError("May only call conclude_via_domain_inclusion "
                             "on a Forall expression with a single instance "
                             "variable over a domain and no other conditions.")
        _x = self.instance_param
        P_op, _P_op = Function(P, _x), self.instance_expr
        return inclusive_universal_quantification.instantiate(
                {x:_x, P_op:_P_op, A:superset_domain, B:self.domain},
                assumptions=assumptions).derive_consequent(assumptions)

    def bundle(self, num_levels=2, *, assumptions=USE_DEFAULTS):
        '''
        Given a nested forall, derive an equivalent form in which a
        given number of nested levels is bundled together.

        For example,
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        can become
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        via bundle with num_levels=2.
        '''
        from proveit import bundle  # generic for OperationOverInstances
        from . import bundle as bundle_thm
        return bundle(self, bundle_thm, num_levels=num_levels,
                      assumptions=assumptions)

    def bundle_equality(self, num_levels=2, *, assumptions=USE_DEFAULTS):
        '''
        Given a nested forall, equate it with an equivalent form in
        which a given number of nested levels is bundled together.

        For example,
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        can be equated with
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        via bundle with num_levels=2.
        '''
        from proveit import bundle  # generic for OperationOverInstances
        from . import bundling
        return bundle(self, bundling, num_levels=num_levels,
                      assumptions=assumptions)

    def unbundle(self, num_param_entries=(1,), *, assumptions=USE_DEFAULTS):
        '''
        From a nested forall, derive an equivalent form in which the
        parameter entries are split in number according to
        'num_param_entries'.

        For example,
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        can become
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        via bundle with num_param_entries=(2, 1) or
        num_param_entries=(2,) -- the last number can be implied
        by the remaining number of parameters.
        '''
        from proveit import unbundle  # generic for Op..OverInstances
        from . import unbundle as unbundle_thm
        return unbundle(self, unbundle_thm,
                        num_param_entries=num_param_entries,
                        assumptions=assumptions)

    def unbundle_equality(self, num_param_entries=(1,), *,
                          assumptions=USE_DEFAULTS):
        '''
        From a nested forall, equate it with an equivalent form in
        which the parameter entries are split in number according to
        'num_param_entries'.

        For example,
            \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
        can equate with
            \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
        via bundle with num_param_entries=(2, 1) or
        num_param_entries=(2,) -- the last number can be implied
        by the remaining number of parameters.
        '''
        from proveit import unbundle  # generic for Op..OverInstances
        from . import bundling
        return unbundle(
            self, bundling, num_param_entries=num_param_entries,
            assumptions=assumptions)

    def instantiate(self, repl_map=None, assumptions=USE_DEFAULTS):
        '''
        First attempt to prove that this Forall statement is true under
        the assumptions, and then call instantiate on the Judgment.
        '''
        return self.prove(assumptions).instantiate(
            repl_map, assumptions=assumptions)
    
    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if
        possible by calling the condition's forall_evaluation method
        '''
        assert self.has_domain(), ("Cannot automatically evaluate a forall "
                                   "statement with no domain")

        if len(list(self.instance_param_lists())) == 1:
            if hasattr(self.domain, 'forall_evaluation'):
                # Use the domain's forall_evaluation method
                return self.domain.forall_evaluation(self, assumptions)
        else:
            # Evaluate an unravelled version
            unravelled_equiv = self.derive_unraveled_equiv(
                [var for var in (list(self.instance_var_lists()))])
            return unravelled_equiv.rhs.evaluation(assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this forall expression
        is in the set of BOOLEANS, as all forall expressions are
        (they are taken to be false when not true).
        '''
        from proveit.numbers import one
        from . import forall_in_bool
        _x = self.instance_params
        P_op, _P_op = Function(P, _x), self.instance_expr
        _n = _x.num_elements(assumptions)
        x_1_to_n = ExprTuple(ExprRange(k, IndexedVar(x, k), one, _n))
        return forall_in_bool.instantiate(
            {n: _n, P_op: _P_op, x_1_to_n: _x},
            assumptions=assumptions)

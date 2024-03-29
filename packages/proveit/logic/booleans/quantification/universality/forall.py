from proveit import (Literal, Function, Lambda, OperationOverInstances,
                     ExprTuple, ExprRange, IndexedVar, UnusableProof,
                     defaults, USE_DEFAULTS, ProofFailure,
                     prover, relation_prover, equality_prover)
from proveit import k, n, x, A, B, P, Q, S
from proveit._core_.proof import Generalization


class Forall(OperationOverInstances):
    # operator of the Forall operation
    _operator_ = Literal(string_format='forall', latex_format=r'\forall',
                         theory=__file__)
    
    # Map instance parameter -> expression maps to universal 
    # quantifications over them that are known judgments.
    known_instance_maps = dict()

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
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
            condition=condition, conditions=conditions, styles=styles,
            _lambda_map=_lambda_map)
    
    def _record_as_proven(self, judgment):
        '''
        Remember the proven Universal judgments by their
        instance expressions.
        '''
        instance_map = Lambda(judgment.expr.instance_params,
                              judgment.expr.instance_expr)
        Forall.known_instance_maps.setdefault(
                instance_map, set()).add(judgment)

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

        # Perform a generic instantiation assuming all conditions,
        # but don't cascade further side-effects which can be
        # problematic.
        yield self._instantiate_generically
        
    def _readily_provable(self):
        '''
        The universal quantification is readily probable if the
        instance expression is readily probably under appropriate
        assumptions of if another universal quantification has
        been proven with a more inclusive domain.
        '''
        if self._readily_provable_via_generalization():
            return True
        return False
        #TODO, OTHER CASES
    
    def _readily_provable_via_generalization(self):
        # Check if the instance expression is readily provable under
        # appropriate assumptions.
        from proveit import free_vars
        instance_vars = (self.instance_vars if
                         hasattr(self, 'instance_vars')
                         else [self.instance_var])
        conditions = self.conditions
        expr = self.instance_expr
        # Can't use assumptions involving instance variables
        inner_assumptions = \
            [assumption for assumption in defaults.assumptions if
             free_vars(assumption).isdisjoint(instance_vars)]
        # Add the conditions as assumptions.
        inner_assumptions += list(conditions.entries)
        return expr.readily_provable(assumptions=inner_assumptions)

    @prover
    def conclude(self, **defaults_config):
        '''
        If the instance expression, or some instance expression of
        nested universal quantifiers, is known to be true, conclude
        via generalization.  Otherwise, if the domain has a 'fold_forall'
        method, attempt to conclude this Forall statement
        via 'conclude_by_cases'.
        '''
        from proveit.logic import SubsetEq
        
        # Make sure we derive side-effects from the conditions
        # before checking of the generalization is readily provable
        # for Forall.conclude purposes.
        if hasattr(self, 'condition'):
            with defaults.temporary() as tmp_defaults:
                if hasattr(self, 'conditions'):
                    tmp_defaults.assumptions = (
                            defaults.assumptions+self.conditions)
                if hasattr(self, 'conditions'):
                    tmp_defaults.assumptions = (
                            defaults.assumptions+(self.condition,))
                defaults.make_assumptions()

        try:
            # First see if we can prove via generalization.
            if self._readily_provable_via_generalization():
                return self.conclude_via_generalization()
            elif (self.canonically_labeled()
                  ._readily_provable_via_generalization()):
                return self.canonically_labeled().conclude_via_generalization()
        except UnusableProof:
            # Try a different strategy if there was an unusable proof.
            pass
        
        if (self.has_domain() and self.instance_params.is_single 
                and self.conditions.is_single()):
            instance_map = Lambda(self.instance_params, self.instance_expr)
            domain = self.domain 
            known_domains = set()
            # Next, check the known quantified instance expressions
            # and known set inclusions of domains to see if we can 
            # construct a proof via inclusive universal quantification.
            if instance_map in Forall.known_instance_maps:
                known_foralls = Forall.known_instance_maps[instance_map]
                for known_forall in known_foralls:
                    if (known_forall.has_domain() 
                            and known_forall.instance_params.is_single()
                            and known_forall.conditions.is_single()):
                        if known_forall.is_applicable():
                            known_domains.add(known_forall.domain)
            if len(known_domains) > 0 and domain in SubsetEq.known_left_sides:
                # We know this quantification in other domain(s).
                # Do any of those include this domain?
                for known_inclusion in SubsetEq.known_left_sides[domain]:
                    if known_inclusion.is_applicable():
                        superset = known_inclusion.superset
                        if superset in known_domains:
                            # We know the quantification over a s
                            # uperset.  We can use 
                            # inclusive_universal_quantification.
                            return self.conclude_via_domain_inclusion(
                                    superset)

        if self.has_domain() and hasattr(self.first_domain(), 'prove_by_cases'):
            try:
                return self.conclude_by_cases()
            except ProofFailure:
                raise ProofFailure(self, defaults.assumptions,
                                   "Unable to conclude automatically; the "
                                   "prove_by_cases method on the domain "
                                   "has failed. :o( ")
        # conclude via generalization as last resort
        return self.conclude_via_generalization()

    @prover
    def unfold(self, **defaults_config):
        '''
        From this forall statement, derive an "unfolded" version
        dependent upon the domain of the forall, calling unfold_forall
        on the condition. For example, from
        forall_{A in BOOLEANS} P(A),
        derives P(TRUE) and P(FALSE).
        '''
        assert self.has_domain(), (
            "Cannot unfold a forall statement with no domain")
        return self.domain.unfold_forall(self)

    def _instantiate_generically(self, **defaults_config):
        '''
        Instantiate all nested layers of universal quantification
        with no changes to instance parameters and assuming all
        conditions.  Do not propagate further side-effects.
        Do this for the canonical form for good measure (which would
        allow a generalization under different parameter labels).
        '''
        with defaults.temporary() as tmp_defaults:
            tmp_defaults.automation = False
            canonical_version = self.canonically_labeled()
            if self._style_id != canonical_version._style_id:
                # Instantiate the generic form for good measure.
                canonical_version.prove().instantiate(
                        num_forall_eliminations=len(
                                self.instance_param_lists()),
                        assumptions=canonical_version.all_conditions())

            return self.prove().instantiate(
                    num_forall_eliminations=len(self.instance_param_lists()),
                    assumptions=self.all_conditions())

    """
    def equate_with_unfolded(self):
        pass
    """

    @prover
    def conclude_via_generalization(self, **defaults_config):
        '''
        Conclude this universal quantification by proving the instance
        expression with assumptions that include the conditions of the
        quantification and then performing generalization step(s).
        This will delve into any number of nested universal
        quantifications if necessary.  With automation turned on,
        we will attempt to prove the innermost instance expression,
        under appropriate assumptions, via automation if necessary.
        '''
        from proveit import free_vars
        automation = defaults.conclude_automation
        expr = self
        instance_param_lists = []
        conditions = []
        proven_inst_expr = None
        inner_assumptions = defaults.assumptions
        while isinstance(expr, Forall):
            new_params = expr.explicit_instance_params()
            new_vars = expr.explicit_instance_vars()
            instance_param_lists.append(list(new_params))
            # Can't use assumptions involving instance variables
            # except from the conditions that we will explicitly add.
            inner_assumptions = \
                [assumption for assumption in inner_assumptions if
                 free_vars(assumption).isdisjoint(new_vars)]
            inner_assumptions += expr.conditions.entries
            conditions += expr.conditions.entries
            expr = expr.instance_expr
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = inner_assumptions
                if expr.proven():
                    proven_inst_expr = expr.prove()
                    break
                elif automation and not isinstance(expr, Forall):
                    proven_inst_expr = expr.prove()
                    break
        if proven_inst_expr is not None:
            return proven_inst_expr.generalize(instance_param_lists,
                                               conditions=conditions)            
        raise ProofFailure(self, defaults.assumptions,
                "Unable to 'conclude_via_generalization' without automation.")

    # Eventually the conclude_by_cases() method will replace the
    # conclude_as_folded() method. Maintaining both temporarily to
    # ensure continued compatibility across the system.

    @prover
    def conclude_by_cases(self, **defaults_config):
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
            unbundled = self.unbundle_equality().rhs
            unbundled = unbundled.conclude_by_cases()
            return unbundled.bundle()
        result = self.domain.prove_by_cases(self)
        return result
    
    @prover
    def conclude_via_domain_inclusion(self, superset_domain,
                                      **defaults_config):
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
        _P = Lambda(_x, self.instance_expr)
        _impl = inclusive_universal_quantification.instantiate(
                {x:_x, P: _P, A:superset_domain, B:self.domain})
        return _impl.derive_consequent()

    @prover
    def bundle(self, num_levels=2, **defaults_config):
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
        return bundle(self, bundle_thm, num_levels=num_levels)

    @prover # Could be an @equality_prover but leave it as is for now.
    def bundle_equality(self, num_levels=2, **defaults_config):
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
        return bundle(self, bundling, num_levels=num_levels)

    @prover
    def unbundle(self, num_param_entries=(1,), **defaults_config):
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
                        num_param_entries=num_param_entries)

    @prover # Could be an @equality_prover but leave it as is for now.
    def unbundle_equality(self, num_param_entries=(1,), 
                          **defaults_config):
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
            self, bundling, num_param_entries=num_param_entries)

    @prover
    def instantiate(self, repl_map=None, *,
                    num_forall_eliminations=None,
                    simplify_only_where_marked=False,
                    markers_and_marked_expr=None,
                    **defaults_config):
        '''
        First attempt to prove that this Forall statement is true under
        the assumptions, and then call instantiate on the Judgment.
        '''
        return self.prove().instantiate(
            repl_map, num_forall_eliminations=num_forall_eliminations,
            simplify_only_where_marked=simplify_only_where_marked,
            markers_and_marked_expr=markers_and_marked_expr)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        From this forall statement, evaluate it to TRUE or FALSE if
        possible by calling the domain's forall_evaluation method
        '''
        from proveit.logic import EvaluationError
        if must_evaluate and not self.has_domain():
            # Cannot automatically evaluate a forall statement with
            # no domain.
            raise EvaluationError(self)
        
        if hasattr(self, 'instance_param'):
            if hasattr(self.domain, 'forall_evaluation'):
                # Use the domain's forall_evaluation method
                return self.domain.forall_evaluation(self)

        '''
        # Let's not do this fancy stuff just yet.
        # Evaluate an unbundled version
        unbundle_eq = self.unbundle_equality()
        return unbundle_eq.rhs.evaluation()
        '''
        if must_evaluate:
            raise EvaluationError(self)
        
        return OperationOverInstances.shallow_simplification(self)

    def readily_in_bool(self):
        '''
        Universal quantification is always boolean.
        '''
        return True

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this forall expression
        is in the set of BOOLEANS, as all forall expressions are
        (they are taken to be false when not true).
        '''
        from . import forall_in_bool, forall_with_conditions__is_bool
        _x = self.instance_params
        _P = Lambda(_x, self.instance_expr)
        _n = _x.num_elements()
        if self.conditions.num_entries() == 0:
            return forall_in_bool.instantiate(
                {n: _n, P: _P, x: _x})
        _Q = Lambda(_x, self.condition)
        return forall_with_conditions__is_bool.instantiate(
                {n: _n, P: _P, Q: _Q, x: _x}, preserve_expr=self,
                auto_simplify=True)

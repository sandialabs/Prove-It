from proveit import (Lambda, Conditional, OperationOverInstances, Judgment,
                     composite_expression, prover, relation_prover)
from proveit import defaults, Literal, Function, ExprTuple
from proveit import n, x, y, z, A, B, P, Q, R, S, Px


class Exists(OperationOverInstances):
    # operator of the Exists operation
    _operator_ = Literal(
        string_format='exists',
        latex_format=r'\exists',
        theory=__file__)

    # a dictionary to track Skolem constants chosen with the
    # Exists.choose() method
    skolem_consts_to_existential = dict()
    
    # Map instance parameter -> expression maps to existential 
    # quantifications over them that are known judgments.
    known_instance_maps = dict()

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        '''
        Create a exists (there exists) expression:
        exists_{instance_param_or_params | condition} instance_expr
        This expresses that there exists a value of the instance parameters(s)
        for which the optional condition(s) is/are satisfied and the
        instance_expr is true.  The instance parameter(s) and condition(s) may
        be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(
            self, Exists._operator_, instance_param_or_params, instance_expr,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, _lambda_map=_lambda_map, styles=styles)

    @prover
    def conclude(self, **defaults_config):
        from proveit.logic import SubsetEq
        if (self.has_domain() and self.instance_params.is_single 
                and self.conditions.is_single()):
            instance_map = Lambda(self.instance_params, self.instance_expr)
            domain = self.domain 
            known_domains = set()
            # Check the known quantified instance expressions
            # and known set inclusions of domains to see if we can 
            # construct a proof via inclusive existential 
            # quantification.
            if instance_map in Exists.known_instance_maps:
                known_foralls = Exists.known_instance_maps[instance_map]
                for known_forall in known_foralls:
                    if (known_forall.has_domain() 
                            and known_forall.instance_params.is_single()
                            and known_forall.conditions.is_single()):
                        if known_forall.is_applicable():
                            known_domains.add(known_forall.domain)
            if len(known_domains) > 0 and domain in SubsetEq.known_left_sides:
                # We know this quantification in other domain(s).
                # Does our domain include any of those?
                for known_inclusion in SubsetEq.known_right_sides[domain]:
                    if known_inclusion.is_applicable():
                        subset = known_inclusion.subset
                        if subset in known_domains:
                            # We know the quantification over a s
                            # uperset.  We can use 
                            # inclusive_universal_quantification.
                            return self.conclude_via_domain_inclusion(
                                    subset)
        
    def _record_as_proven(self, judgment):
        '''
        Remember the proven Existential judgments by their
        instance expressions.
        '''
        instance_map = Lambda(judgment.expr.instance_params,
                              judgment.expr.instance_expr)        
        Exists.known_instance_maps.setdefault(
                instance_map, set()).add(judgment)

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for an exists operations.
        '''
        return
        yield self.derive_negated_forall  # derive the negated forall form

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a negated exists operation.
        '''
        yield self.deduce_not_exists  # derive the NotExists form.

    def choose(self, *skolem_constants, print_message=True):
        '''
        From the existential expression
        self = exists_{x_1,...,x_n | Q(x_1,...,x_n)} P(x_1,...,x_n),
        generate Skolem constants a_1,...,a_n in correspondence with
        the instance params x_1,...,x_n. The process will:
        (1) add Q(a_1,...,a_n) and P(a_1,...,a_n) to the default
            assumptions;
        (2) register the Skolem constants a_1,...,a_n in the
            skolem_consts_to_existential dictionary so they can be
            eliminated later using the eliminate() method;
        (3) return the newly-generated assumptions Q(a_1,...,a_n) and
            P(a_1,...,a_n)
        '''
        # Register this particular collection of Skolem constants
        # in the dictionary as a key linking them to this Exists object
        Exists.skolem_consts_to_existential[skolem_constants] = self

        # build the Skolemized versions of the conditions Q and the
        # instance expression P
        repl_dict = {param: skolem_const for param, skolem_const
                     in zip(self.instance_params, skolem_constants)}
        P_skolem = self.instance_expr.basic_replaced(repl_dict)
        Q_skolem = self.conditions.basic_replaced(repl_dict)

        # Update the default assumptions with the Skolem versions
        # of the conditions and instance expression
        defaults.assumptions = (*defaults.assumptions, *Q_skolem.entries, P_skolem)
        if print_message:
            print(
                "Creating Skolem 'constant(s)': {0}.\n"
                "Call the Judgment.eliminate{0} to complete the "
                "Skolemization\n(when the 'constant(s)' are no longer needed).\n"
                "Adding to defaults.assumptions:". format(
                    skolem_constants, *Q_skolem.entries))

        return ExprTuple(*Q_skolem.entries, P_skolem)

    @staticmethod
    @prover
    def eliminate(skolem_constants, judgment, **defaults_config):
        '''
        For the provided judgment of the form S |– alpha and the tuple
        of Skolem constants skolem_constants that had been specified
        earlier using the Exists.choose(), derive and return a new
        judgment S' |– alpha where all assumptions in S involving only
        the given skolem_constants are now eliminated.
        This process will only work if the provided skolem_constants
        exactly match a set of Skolem constants used earlier in an
        Exists.choose() method to produce the Skolem constant-based
        subset of assumptions you wish to eliminate from S.
        '''
        from proveit import free_vars, Lambda
        from proveit import n, P, Q, alpha
        from proveit.logic import And
        from proveit.core_expr_types import (x_1_to_n, y_1_to_n)
        from proveit.logic.booleans.quantification.existence import (
            skolem_elim)
        if skolem_constants not in Exists.skolem_consts_to_existential:
            raise KeyError("In calling Exists.eliminate(), the Skolem "
                           "constants provided were: {}, but you can only "
                           "eliminate Skolem constants that were chosen "
                           "earlier when using Exists.choose() and the "
                           "Skolem constants to be eliminated must appear "
                           "exactly as specified in the original "
                           "Exists.choose() method.".format(skolem_constants))
        # Since the Skolem constants appear to be correct, we check
        # if any of the Skolem constants appear as free variables in
        # the judgment, raising an error if so:
        skolem_constants_remaining = (
            set(skolem_constants).intersection(free_vars(judgment)) )
        if skolem_constants_remaining != set():
            raise ValueError(
                    "In calling the Exists.eliminate() static method, which "
                    "might have arisen from a judgment.eliminate() call, "
                    f"the Skolem constant(s) {skolem_constants_remaining} "
                    "still appear as free variable(s) in the target judgment "
                    f"{judgment}, which is not allowed. ")
        existential = Exists.skolem_consts_to_existential[skolem_constants]
        skolem_assumptions = set(existential.choose(
            *skolem_constants, print_message=False))
        with defaults.temporary() as temp_defaults:
            temp_defaults.assumptions = (
                    assumption for assumption in defaults.assumptions
                    if assumption not in skolem_assumptions)

            _P = Lambda(
                existential.instance_params, existential.instance_expr)
            if hasattr(existential, 'condition'):
                _Q = Lambda(existential.instance_params, existential.condition)
            else:
                # There is no condition but we still need to provide
                # something for _Q so we provide an empty conjunction,
                # And().
                _Q = Lambda(
                    existential.instance_params, And())
            _alpha = judgment
            _n = existential.instance_params.num_elements()
            x_1_to__n = ExprTuple(x_1_to_n.basic_replaced({n: _n}))
            y_1_to__n = ExprTuple(y_1_to_n.basic_replaced({n: _n}))
    
            # express the judgment as an implication to match details of
            # the skolem_elim theorem being instantiated further below
            P_implies_alpha = _alpha.as_implication(
                hypothesis=_P.apply(*skolem_constants))
            # Although the generalization to further match theorem
            # details can be handled through automation, it can reduce
            # computations to explicitly handle it here right now:
            P_implies_alpha.generalize(
                    skolem_constants,
                    conditions=[_Q.apply(*skolem_constants)])
    
            return skolem_elim.instantiate(
                {n: _n, P: _P, Q: _Q, alpha: _alpha,
                 x_1_to__n: skolem_constants,
                 y_1_to__n: existential.instance_params},
                preserve_all=True).derive_consequent()

    @prover
    def unfold(self, **defaults_config):
        '''
        From this existential quantifier, and knowing or assuming
        self to be TRUE, derive the "unfolded" version according
        to its definition, producing the negation of a universal
        quantification. For example, given

            A = |- Exists((a,b), (a+b = 5), domain = NaturalPos),

        A.unfold() produces:

            |- Not(Forall((a, b in NaturalPos), [(a+b = 5) != T])).

        As explained in the existence axioms notebook, the format here
        (and the awkwardness of the conclusion) arises from the effort
        to avoid the assumption that the operation always returns a
        Boolean. On the other hand, if we have:

            B = |- Exists(x, Not(P(x))),

        then B.unfold() produces:

            |- Not(Forall(x, P(x)))

        '''
        from proveit.logic import Not, TRUE
        from proveit.logic.booleans.quantification.existence import (
                exists_not_unfolding, exists_unfolding)
        _x = _y = self.instance_params
        _n = _x.num_elements()

        # distinguish between Exists(x, P(x)) vs Exists(x, Not(P(x)))
        _case_not = False
        if isinstance(self.instance_expr, Not):
            _case_not = True
            _P = Lambda(_x, self.instance_expr.operand)
        else:
            _P = Lambda(_x, self.instance_expr)
        # distinguish between cases with and w/out conditions
        if hasattr(self, 'condition'):
            _Q = Lambda(_x, self.condition)
        else:
            _Q = Lambda(_x, TRUE)
        if _case_not:
            return exists_not_unfolding.instantiate(
            {n: _n, P: _P, Q: _Q, x: _x, y: _y}).derive_consequent()
        return exists_unfolding.instantiate(
            {n: _n, P: _P, Q: _Q, x: _x, y: _y}).derive_consequent()

    @prover
    def definition(self, **defaults_config):
        '''
        Return definition of this existential quantifier as an
        equation with this existential quantifier on the left
        and a negated universal quantification on the right. This
        handles two separate cases (along with cases with and w/out
        conditions):
            Exists(x, P(x)) vs. Exists(x, Not(P(x))),
        which return:
            Not(Forall(x, P(x) != T)) and Not(Forall(x, P(x))),
        respectively.
        '''
        from proveit import defaults
        from proveit.logic import Forall, Not, NotEquals, TRUE
        from proveit.logic.booleans.quantification.existence import (
            exists_def, exists_not_eq_not_forall)
        _x = _y = self.instance_params
        _n = _x.num_elements()

        # distinguish between Exists(x, P(x)) vs Exists(x, Not(P(x)))
        _case_not = False
        if isinstance(self.instance_expr, Not):
            _case_not = True
            _P = Lambda(_x, self.instance_expr.operand)
        else:
            _P = Lambda(_x, self.instance_expr)
        # distinguish between cases with and w/out conditions
        if hasattr(self, 'condition'):
            _Q = Lambda(_x, self.condition)
        else:
            _Q = Lambda(_x, TRUE)

        # Construct the rhs result to preserve (using
        # 'preserve_all = TRUE' in the instantiation step further
        # below tends to preserve too much, in particular preserving
        # the "empty" condition _Q = Lambda(_x, TRUE) when we'd like
        # it to be simplified away entirely).
        if hasattr(self, 'condition'):
            if _case_not:
                rhs_to_preserve = (
                    Not(Forall(_x, self.instance_expr.operand,
                        conditions = [self.condition])))
            else:
                rhs_to_preserve = (
                    Not(Forall(_x, 
                        NotEquals(self.instance_expr, TRUE),
                        conditions = [self.condition])))
        else:
            if _case_not:
                rhs_to_preserve = (
                    Not(Forall(_x, self.instance_expr.operand)))
            else:
                rhs_to_preserve = (
                    Not(Forall(_x,
                        NotEquals(self.instance_expr, TRUE))))
        
        # now ready to instantiate thm based on _case_not, and
        # explicitly preserving the expected rhs of the resulting eq.
        with defaults.temporary() as temp_defaults:
            temp_defaults.preserved_exprs = {self, rhs_to_preserve}
            if _case_not:
                return exists_not_eq_not_forall.instantiate(
                    {n: _n, P: _P, Q: _Q, x: _x, y: _y})
            else:
                return exists_def.instantiate(
                    {n: _n, P: _P, Q: _Q, x: _x, y: _y})

    @prover
    def deduce_not_exists(self, **defaults_config):
        r'''
        Deduce notexists_{x | Q(x) P(x) assuming not(exists_{x | Q(x) P(x)),
        where self is exists_{x | Q(x) P(x).
        '''
        from .not_exists import NotExists
        not_exists_expr = NotExists(
            self.instance_params,
            self.instance_expr,
            domain=self.domain,
            conditions=self.conditions)
        return not_exists_expr.conclude_as_folded()

    @prover
    def conclude_via_example(self, example_instance, **defaults_config):
        '''
        Conclude and return this
        [exists_{x_1, .., x_n | Q(x_1, ..., x_n)} P(x_1, ..., x_n)] 
        from P(y_1, ..., y_n) and Q(y_1, ..., y_n)
        where y_1, ..., y_n is the given example_instance.
        '''
        from . import existence_by_example
        from . import existence_by_example_with_conditions
        _x = self.instance_params
        _n = _x.num_elements()
        _P = Lambda(_x, self.instance_expr)
        _y = composite_expression(example_instance)
        if hasattr(self, 'condition'):
            _Q = Lambda(_x, self.condition)
            return existence_by_example_with_conditions.instantiate(
                {n:_n, x:_x, y:_y, P:_P, Q:_Q})
        return existence_by_example.instantiate(
                {n:_n, x:_x, y:_y, P:_P})

    @prover
    def conclude_via_domain_inclusion(self, subset_domain,
                                      **defaults_config):
        '''
        Conclude this exists statement from a similar exists statement
        over a narrower domain.  For example, conclude
        exists_{x in B} P(x) from exists_{x in A} P(x)
        given A subset_eq B.
        '''
        from proveit.logic.sets.inclusion import (
                inclusive_existential_quantification)
        if not (self.has_domain() and self.instance_params.is_single 
                and self.conditions.is_single()):
            raise ValueError("May only call conclude_via_domain_inclusion "
                             "on a Forall expression with a single instance "
                             "variable over a domain and no other conditions.")
        _x = self.instance_param
        _P = Lambda(_x, self.instance_expr)
        _impl = inclusive_existential_quantification.instantiate(
            {x:_x, P:_P, A:subset_domain, B:self.domain})
        return _impl.derive_consequent()

    @prover
    def derive_negated_forall(self, **defaults_config):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and 
        return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and 
        return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        from . import exists_unfolding
        from . import exists_not_implies_not_forall
        from proveit.logic import Not
        _x = self.instance_params
        _Q = Lambda(_x, self.condition)
        if isinstance(self.instance_expr, Not):
            _P = Lambda(_x, self.instance_expr.operand)
            _impl = exists_not_implies_not_forall.instantiate(
                {P: _P, Q: _Q, S: self.domain, x: _x}) 
            return _impl.derive_consequent()
        else:
            _P = Lambda(_x, self.instance_expr)
            _impl = exists_unfolding.instantiate(
                {P: _P, Q: _Q, S: self.domain, x:_x})
            return _impl.derive_consequent()

    @prover
    def substitute_domain(self, superset, **defaults_config):
        '''
        Substitute the domain with a superset.
        From [exists_{x in A| Q(x)} P(x)], derive and return 
        [exists_{x in B| Q(x)} P(x)]
        given A subseteq B.
        '''
        from proveit.logic import And
        from . import exists_in_superset
        _x = self.instance_params
        _P = Lambda(_x, self.instance_expr)
        if self.conditions.num_entries() == 1:
            _Q = Lambda(_x, self.condition)
        else:
            _Q = Lambda(_x, And(self.conditions[1:]))
        _impl = exists_in_superset.instantiate(
            {P: _P, Q: _Q, A: self.domain, B: superset, x: _x, y: _x})
        return _impl.derive_consequent()

    """
    @prover
    def elim_domain(self, **defaults_config):
        '''
        From [exists_{x in S | Q(x)} P(x)], derive and return [exists_{x | Q(x)} P(x)],
        eliminating the domain which is a weaker form.
        '''
        from . import exists_in_general
        _x = self.instance_vars
        _P = Lambda(_x, self.instance_expr)
        _Q = Lambda(_x, self.condition)
        return exists_in_general.instantiate(
            {P: _P, Q: _Q, S: self.domain, x: _x, y: _x},
            preserve_all=True).derive_consequent()
    """

    def readily_in_bool(self):
        '''
        Existential quantification is always boolean.
        '''
        return True

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        from . import exists_is_bool, exists_with_conditions_is_bool
        _x = self.instance_params
        _P = Lambda(_x, self.instance_expr)
        _n = _x.num_elements()
        if self.conditions.num_entries() == 0:
            return exists_is_bool.instantiate(
                {n: _n, P: _P, x: _x})
        _Q = Lambda(_x, self.condition)
        return exists_with_conditions_is_bool.instantiate(
                {n: _n, P: _P, Q: _Q, x: _x}, preserve_expr=self,
                auto_simplify=True)

    @prover
    def substitute_instances(self, universality, **defaults_config):
        '''
        Derive from this Exists operation, Exists_{..x.. in S | ..Q(..x..)..} P(..x..),
        one that substitutes instance expressions given some
        universality = forall_{..x.. in S | P(..x..), ..Q(..x..)..} R(..x..).
                                            or forall_{..x.. in S | ..Q(..x..)..} P(..x..) = R(..x..).
        Either is allowed in the theory of the existential quantifier.
        Derive and return the following type of existential operation assuming universality:
        Exists_{..x.. in S | ..Q(..x..)..} R(..x..)
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        raise NotImplementedError("Need to test/update")
        from . import existential_implication, no_domain_existential_implication
        from proveit import Etcetera
        from proveit.logic import Forall
        from proveit._generic_ import InstanceSubstitutionException
        if isinstance(universality, Judgment):
            universality = universality.expr
        if not isinstance(universality, Forall):
            raise InstanceSubstitutionException(
                "'universality' must be a forall expression", self, universality)

        if self.instance_expr in universality.conditions:
            # map from the forall instance variables to self's instance
            # variables
            i_var_substitutions = {
                forall_ivar: self_ivar for forall_ivar,
                self_ivar in zip(
                    universality.instance_vars,
                    self.instance_vars)}
            first_condition = universality.conditions[0].substituted(
                i_var_substitutions)
            if first_condition != self.instance_expr:
                raise InstanceSubstitutionException(
                    "The first condition of the 'universality' must match the instance expression of the Exists operation having instances substituted",
                    self,
                    universality)
            if (universality.instance_vars.num_entries() !=
                    self.instance_vars.num_entries()):
                raise InstanceSubstitutionException(
                    "'universality' must have the same number of variables as the Exists operation having instances substituted",
                    self,
                    universality)
            if universality.domain != self.domain:
                raise InstanceSubstitutionException(
                    "'universality' must have the same domain as the Exists having instances substituted",
                    self,
                    universality)
            if ExpressionList(universality.conditions[1:]).substituted(
                    i_var_substitutions) != self.conditions:
                raise InstanceSubstitutionException(
                    "'universality' must have the same conditions as the Exists operation having instances substituted, in addition to the Exists instance expression",
                    self,
                    universality)
            _x = universality.instance_vars,
            _y = self.instance_params
            _P = Lambda(_y, self.instance_expr)
            _Q = Lambda(_y, self.condition)
            _R = Lambda(_y, universality.instance_expr.substituted(
                i_var_substitutions))
            _impl = existential_implication.instantiate(
                {P: _P, Q: _Q, R: _R, S: self.domain, x: _x, y: _y, z: _y})
            return _impl.derive_consequent().derive_consequent()
        # Default to the OperationOverInstances version which works with
        # universally quantified equalities.
        return OperationOverInstances.substitute(
            self, universality)

from proveit import (Lambda, Conditional, Operation, OperationOverInstances, 
                     Judgment, ProofFailure, free_vars, composite_expression,
                     prover, equality_prover, relation_prover)
from proveit import defaults, Literal, Function, ExprTuple
from proveit import n, x, y, z, A, B, P, Q, R, S, Px
from IPython.display import display


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

    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, exists_{x | Q(x)} P(x) is a stylized form of
        exists_{x} [Q(x) ∧ P(x).]
        Return the conjunction (e.g., Q(x) ∧ P(x) in the example).
        '''
        from proveit.logic import And
        return And(condition, instance_expr)
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, exists_{x | Q(x)} P(x) is a stylized form of
        exists_{x} [Q(x) ∧ P(x).]
        Return the condition and instance_expr as a tuple.  For the example,
        this would return (Q(x), P(x)).
        '''
        from proveit.logic import And
        if isinstance(lambda_body, And) and lambda_body.operands.is_double():
            return tuple(lambda_body.operands)
        return None, lambda_body

    def _readily_provable(self):
        '''
        Return True iff we should readily be able to conclude this existential
        quantification.  Certain forms may be proved automatically
        (e.g., existence of a conservative definition).
        '''
        from proveit.logic import Equals, Forall, And
        if not hasattr(self, 'condition') and (
                self.instance_expr.readily_provable()):
            return True # trivial existence by example.
        elif hasattr(self, 'condition') and (
                And(self.condition, self.instance_expr).readily_provable()):
            return True # simple existence by example.
        elif self.as_defined().proven():
            return True
        elif self.instance_params.is_single() and (
                len(self.conditions) == 0 and
                isinstance(self.instance_expr, Equals) and
                self.instance_expr.lhs == self.instance_param and
                self.instance_param not in free_vars(self.instance_expr.rhs)):
            # Existential for a conservative definition.
            return True
        elif self.instance_params.is_single() and (
                len(self.conditions) == 0 and
                isinstance(self.instance_expr, Forall) and
                isinstance(self.instance_expr.instance_expr, Equals) and
                isinstance(self.instance_expr.instance_expr.lhs, Operation) and
                self.instance_expr.instance_expr.lhs.operator == self.instance_param and
                self.instance_expr.instance_expr.lhs.operands == (
                    self.instance_expr.instance_params) and 
                self.instance_param not in free_vars(
                    self.instance_expr.instance_expr.rhs)):
            # Existential for a conservatively defined operation.
            return True
        return False

    @prover
    def conclude(self, **defaults_config):
        from proveit import Operation, free_vars
        from proveit.logic import And, Forall, Equals, SubsetEq
        if (not hasattr(self, 'condition') and 
            self.instance_expr.readily_provable()) or (
                    hasattr(self, 'condition') and
                    And(self.condition, self.instance_expr).readily_provable()):
            # simple existence by example.
            return self.conclude_via_example(self.instance_param_or_params)
        elif self.as_defined().proven():
            return self.conclude_as_folded()
        # is this obsolete? not sure. may resurrect:
        '''
        elif self.instance_params.is_single() and (
                len(self.conditions) == 0 and
                isinstance(self.instance_expr, Forall) and
                isinstance(self.instance_expr.instance_expr, Equals) and
                isinstance(self.instance_expr.instance_expr.lhs, Operation) and
                self.instance_expr.instance_expr.lhs.operator == self.instance_param and
                self.instance_expr.instance_expr.lhs.operands == (
                    self.instance_expr.instance_params) and 
                self.instance_param not in free_vars(
                    self.instance_expr.instance_expr.rhs)):
            from . import existence_by_basic_example
            exist_by_example_relabeled = (
                existence_by_basic_example.
                inner_expr().instance_expr.operand.relabeled(
                    {x:self.instance_param}))
            return exist_by_example_relabeled.instantiate(
                {P:Lambda(self.instance_param, self.instance_expr), 
                 self.instance_param:Lambda(
                     self.instance_expr.instance_expr.lhs.operands,
                     self.instance_expr.instance_expr.rhs)})
        '''
        # Check for existence by equlity
        try:
            return self.conclude_via_equality()
        except ValueError:
            return None
        if (self.has_domain() and self.instance_params.is_single()
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

    def incidentals(self, judgment):
        '''
        Side-effect derivations to attempt automatically for an exists operations.
        '''
        return
        yield self.derive_negated_forall  # derive the negated forall form

    def negation_incidentals(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a negated exists operation.
        '''
        yield self.deduce_not_exists  # derive the NotExists form.

    def choose(self, *skolem_constants, print_message=True,
               _append_new_assumption=True):
        '''
        From the existential expression
        self = exists_{x_1,...,x_n | Q(x_1,...,x_n)} P(x_1,...,x_n),
        or exists_{x_1,...,x_n} P(x_1,...,x_n) or exists_{x} P(x).
        generate Skolem constants a_1,...,a_n in correspondence with
        the instance params x_1,...,x_n. The process will:
        (1) add Q(a_1,...,a_n) (if applicable) and P(a_1,...,a_n) to the
            default assumptions;
        (2) register the Skolem constants a_1,...,a_n in the
            skolem_consts_to_existential dictionary so they can be
            eliminated later using the eliminate() method;
        (3) return the newly-generated assumptions Q(a_1,...,a_n) 
            (if applicable) and P(a_1,...,a_n).
        '''
        # Register this particular collection of Skolem constants
        # in the dictionary as a key linking them to this Exists object
        Exists.skolem_consts_to_existential[skolem_constants] = self

        # build the Skolemized versions of the conditions Q and the
        # instance expression P
        repl_dict = {param: skolem_const for param, skolem_const
                     in zip(self.instance_params, skolem_constants)}
        P_skolem = self.operand.body.basic_replaced(repl_dict)

        # Update the default assumptions with the Skolem versions
        # of the conditions and instance expression
        if _append_new_assumption:
            defaults.assumptions = (*defaults.assumptions, P_skolem)
            if print_message:
                print(
                    "Creating Skolem 'constant(s)': {0}.\n"
                    "Call the Judgment.eliminate{0} to complete the "
                    "Skolemization\n(when the 'constant(s)' are no longer "
                    "needed).\n"
                    "Adding to defaults.assumptions:". format(skolem_constants))

        return P_skolem

    @staticmethod
    @prover
    def eliminate(skolem_constant_or_constants, judgment,
                  print_message=True, **defaults_config):
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
        from proveit import n, P, alpha
        from proveit.core_expr_types import (x_1_to_n, y_1_to_n)
        from proveit.logic.booleans.quantification.existence import (
            skolem_elim)
        if isinstance(skolem_constant_or_constants, tuple):
            skolem_constants = skolem_constant_or_constants
        else:
            try:
                skolem_constants = tuple(skolem_constant_or_constants)
            except:
                skolem_constants = (skolem_constant_or_constants,)
        
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
        skolem_assumption = existential.choose(
            *skolem_constants, print_message=False,
            _append_new_assumption=False)
        # skolem_assumption no longer needed as an assumption.
        if skolem_assumption not in defaults.assumptions:
            raise Exception("Expecting %s in defaults.assumptions so it can "
                            "be properly removed with this 'eliminate' call"
                            %skolem_assumption)
        if print_message:
            print("Removing from defaults.assumptions:")
            display(skolem_assumption)                
        defaults.assumptions = (
                assumption for assumption in defaults.assumptions
                if assumption != skolem_assumption)

        _P = Lambda(existential.instance_params,
                    existential.operand.body)
        _alpha = judgment

        # express the judgment as an implication to match details of
        # the skolem_elim theorem being instantiated further below
        P_implies_alpha = _alpha.as_implication(
            hypothesis=_P.apply(*skolem_constants))
        P_implies_alpha.generalize(skolem_constants)

        if hasattr(existential, 'instance_param'):
            assert len(skolem_constants)==1
            inst = skolem_elim.instantiate(
                {P: _P, alpha: _alpha,
                 x: skolem_constants[0],
                 y: existential.instance_param},
                preserve_all=True)
            return inst.derive_consequent()
        else:
            from proveit.logic.booleans.quantification.existence import (
                multi_skolem_elim)
            _n = existential.instance_params.num_elements()
            x_1_to__n = ExprTuple(x_1_to_n.basic_replaced({n: _n}))
            y_1_to__n = ExprTuple(y_1_to_n.basic_replaced({n: _n}))
            return multi_skolem_elim.instantiate(
                {n: _n, P: _P, alpha: _alpha,
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
        from proveit.logic import Not
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            if isinstance(self.instance_expr, Not):
                _P = Lambda(_x, self.instance_expr.operand)
                if _Q is None:
                    from . import exists_not_unfolding
                    thm = exists_not_unfolding
                else:
                    from . import conditional_exists_not_unfolding
                    thm = conditional_exists_not_unfolding
            else:
                _P = Lambda(_x, self.instance_expr)
                if _Q is None:
                    from . import exists_unfolding
                    thm = exists_unfolding
                else:
                    from . import conditional_exists_unfolding
                    thm = conditional_exists_unfolding
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P}).derive_consequent()
            else:
                return thm.instantiate({x:_x, y:_y, P:_P, Q:_Q}).derive_consequent()            
        else:
            raise NotImplementedError("multi-parameter existence unfolding will"
                                      " be implemented later.")

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Return definition of this existential quantifier as an
        equation with this existential quantifier on the left
        and a negated universal quantification on the right. This
        handles 4 separate cases:
            1. ∃_x P(x)
            2. ∃_x ¬P(x)
            3. ∃_{x | Q(x)} P(x)
            4. ∃_{x | Q(x)} ¬P(x)
        which return:
            1. ¬[∀_x ¬P(x)]
            2. ¬[∀_x P(x)]
            3. ¬[∀_{x | Q(x)} ¬P(x)]
            4. ¬[∀_{x | Q(x)} P(x)]
        respectively, as well as multi-parameter variants.
        '''
        from proveit.logic import Not
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            if isinstance(self.instance_expr, Not):
                _P = Lambda(_x, self.instance_expr.operand)
                if _Q is None:
                    from . import exists_not_by_def
                    thm = exists_not_by_def
                else:
                    from . import conditional_exists_not_by_def
                    thm = conditional_exists_not_by_def
            else:
                _P = Lambda(_x, self.instance_expr)
                if _Q is None:
                    from . import exists_def
                    thm = exists_def
                else:
                    from . import conditional_exists_by_def
                    thm = conditional_exists_by_def
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P})
            else:
                return thm.instantiate({x:_x, y:_y, P:_P, Q:_Q})
        else:
            raise NotImplementedError("multi-parameter existence definition will"
                                      " be implemented later.")

        '''
        # TODO: Work on generalizations later.
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
        '''

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

    def as_defined(self):
        '''
        Return the equivalent form that would result from
        self.definition().rhs.
        '''
        return self.equivalent_universal_quantification()

    def equivalent_universal_quantification(self):
        from proveit.logic import Forall, Not
        _x = self.instance_params
        if isinstance(self.instance_expr, Not):
            _P = self.instance_expr.operand
        else:
            _P = Not(self.instance_expr)
        if hasattr(self, 'condition'):
            _Q = self.condition
        else:
            _Q = None
        
        if _Q is None:
            return Not(Forall(_x, _P))
        else:
            return Not(Forall(_x, _P, condition=_Q))


    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Conclude this existential quantification from an equivalent
        universal quantification.
        '''
        from proveit.logic import Not
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            if isinstance(self.instance_expr, Not):
                _P = Lambda(_x, self.instance_expr.operand)
                if _Q is None:
                    from . import exists_not_folding
                    thm = exists_not_folding
                else:
                    from . import conditional_exists_not_folding
                    thm = conditional_exists_not_folding
            else:
                _P = Lambda(_x, self.instance_expr)
                if _Q is None:
                    from . import exists_folding
                    thm = exists_folding
                else:
                    from . import conditional_exists_folding
                    thm = conditional_exists_folding
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P}).derive_consequent()
            else:
                return thm.instantiate({x:_x, y:_y, P:_P, Q:_Q}).derive_consequent()
        else:
            raise NotImplementedError("multi-parameter existence folding will"
                                      " be implemented later.")

    @prover
    def conclude_via_equality(self, **defaults_config):
        '''
        Conclude an return existence of the form
        ∃_{x, y} (x = y)
        ∃_{x, y} (y = x)
        '''
        from proveit.logic import Equals
        if hasattr(self, 'instance_param') and (
                isinstance(self.instance_expr, Equals) and
                len(self.conditions) == 0):
            instance_param = self.instance_param
            lhs, rhs = self.instance_expr.lhs, self.instance_expr.rhs
            if rhs == instance_param and instance_param not in free_vars(lhs):
                from . import existence_by_reversed_equality
                return existence_by_reversed_equality.instantiate(
                    {x:instance_param, y:lhs})
            if lhs == instance_param and instance_param not in free_vars(rhs):
                from . import existence_by_equality
                return existence_by_equality.instantiate(
                    {x:instance_param, y:rhs})
        raise ProofFailure(self, defaults.assumptions,
                           "Not an existence form to conclude by equality")

    @prover
    def conclude_via_example(self, example_instance, **defaults_config):
        '''
        Conclude and return this
        [exists_{x_1, .., x_n | Q(x_1, ..., x_n)} P(x_1, ..., x_n)] 
        from P(y_1, ..., y_n) and Q(y_1, ..., y_n)
        where y_1, ..., y_n is the given example_instance.
        '''
        from . import existence_by_example
        if self.instance_params.is_single():
            if hasattr(self, 'condition'):
                from . import conditional_existence_by_example
                _x = example_instance
                _y = self.instance_params[0]
                _P = Lambda(_y, self.instance_expr)
                _Q = Lambda(_y, self.condition)
                return conditional_existence_by_example.instantiate(
                    {P:_P, Q:_Q, x:_x, y:_y})
            else:
                _x = example_instance
                _y = self.instance_params[0]
                _P = Lambda(_y, self.instance_expr)
                return existence_by_example.instantiate(
                    {P: Lambda(_y, self.instance_expr), x: _x, y: _y})
        else:
            _x = self.instance_params
            _n = _x.num_elements()
            _P = Lambda(_x, self.instance_expr)
            _y = composite_expression(example_instance)
            if hasattr(self, 'condition'):
                from . import multi_existence_by_example
                _Q = Lambda(_x, self.condition)
                return multi_existence_by_example.instantiate(
                    {n: _n, x: _x, y: _y, P: _P, Q: _Q})
            else:
                from . import multiparam_existence_by_example
                return multiparam_existence_by_example.instantiate(
                    {n: _n, x: _x, y: _y, P: _P})

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
        if not (self.has_domain() and self.instance_params.is_single() 
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
        _n = self.instance_params.num_elements()
        _Q = Lambda(_x, self.conditions)
        if isinstance(self.instance_expr, Not):
            _P = Lambda(_x, self.instance_expr.operand)
            _impl = exists_not_implies_not_forall.instantiate(
                {P: _P, Q: _Q, x: _x, y: _x, n: _n})
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
        if len(self.conditions) == 1:
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
        Attempt to deduce, then return, that this existence expression
        is in the set of BOOLEANS, as all existence expressions are
        (this property transfers from universal quantification).
        '''
        from . import exists_is_bool
        if self.instance_params.is_single():
            with_expanded_condition = self.with_expanded_condition()
            _x = self.instance_param
            inst = exists_is_bool.instantiate(
                {x:_x, P:Lambda(_x, with_expanded_condition.instance_expr)})
            if self.has_compact_condition():
                return inst.inner_expr().element.with_compact_condition()
            return inst
        else:
            raise NotImplementedError("multi-parameter version will"
                                      " be implemented later.")

    @prover
    def substitute_instance(self, new_instance_expr, **defaults_config):
        '''
        Given this Exists operation of the form ∃_x P(x),
        derive and return ∃_x R(x) provided that ∀_x P(x) ⇒ R(x).
        This is also generalizes for multiple parameters and conditional
        quantifiers: from ∃_{x | Q(x)} P(x) to ∃_{x | Q(x)} R(x) given
        ∀_{x | Q(x)} P(x) ⇒ R(x).
        '''
        from . import existential_instance_weakening
        if self.instance_params.is_single():
            if hasattr(self, 'condition'):
                from . import conditional_existential_instance_weakening
                _x = self.instance_param
                _P = Lambda(_x, self.instance_expr)
                _Q = Lambda(_x, self.condition)
                _R = Lambda(_x, new_instance_expr)
                inst = conditional_existential_instance_weakening.instantiate(
                    {P:_P, Q:_Q, R:_R, x:_x, y:_x, z:_x})
            else:
                _x = self.instance_param
                _P = Lambda(_x, self.instance_expr)
                _R = Lambda(_x, new_instance_expr)
                inst = existential_instance_weakening.instantiate(
                    {P:_P,  R:_R, x:_x, y:_x, z:_x})
        else:
            _x = self.instance_params
            _n = _x.num_elements()
            _P = Lambda(_x, self.instance_expr)
            _R = Lambda(_x, new_instance_expr)
            if hasattr(self, 'condition'):
                from . import (
                    multiparam_conditional_existential_instance_weakening)
                _thm = multiparam_conditional_existential_instance_weakening
                _Q = Lambda(_x, self.condition)
                inst = _thm.instantiate(
                    {n: _n, x: _x, y: _x, z: _x, P: _P, Q: _Q, R:_R})
            else:
                from . import multiparam_existential_instance_weakening
                inst = multiparam_existential_instance_weakening.instantiate(
                    {n: _n, x: _x, y: _x, z:_x, P: _P, R:_R})
        return inst.derive_consequent().derive_consequent()

    @prover
    def substitute_condition(self, new_condition, **defaults_config):
        '''
        Given this Exists operation of the form ∃_{x | Q(x)} P(x),
        derive and return ∃_{x | R(x)} P(x) provided that 
        ∀_x P(x) ⇒ R(x).
        This is also generalizes for multiple parameters.
        '''
        from . import existential_condition_weakening
        if not hasattr(self, 'condition'):
            raise ValueError("No 'condition' to substitute")

        if self.instance_params.is_single():
                _x = self.instance_param
                _P = Lambda(_x, self.instance_expr)
                _Q = Lambda(_x, self.condition)
                _R = Lambda(_x, new_condition)
                inst = existential_condition_weakening.instantiate(
                    {P:_P, Q:_Q, R:_R, x:_x, y:_x, z:_x})
        else:
            from . import (
                multiparam_existential_condition_weakening)
            _x = self.instance_params
            _n = _x.num_elements()
            _P = Lambda(_x, self.instance_expr)
            _R = Lambda(_x, new_condition)
            _thm = multiparam_existential_condition_weakening
            _Q = Lambda(_x, self.condition)
            inst = _thm.instantiate(
                {n: _n, x: _x, y: _x, z: _x, P: _P, Q: _Q, R:_R})
        return inst.derive_consequent().derive_consequent()
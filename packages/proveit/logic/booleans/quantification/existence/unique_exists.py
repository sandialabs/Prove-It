from proveit import (Lambda, Conditional, OperationOverInstances, Judgment,
                     composite_expression, prover, relation_prover,
                     equality_prover)
from proveit import (defaults, Literal, Function, ExprTuple, USE_DEFAULTS,
                     safe_dummy_vars)
from proveit import n, w, x, y, z, A, B, P, Q, R, S, Px


class UniqueExists(OperationOverInstances):
    # operator of the Exists operation
    _operator_ = Literal(
        string_format='exists!',
        latex_format=r'\exists!',
        theory=__file__)

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
            self, UniqueExists._operator_, instance_param_or_params, instance_expr,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, _lambda_map=_lambda_map, styles=styles)

    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, unique_exists_{x | Q(x)} P(x) is a stylized
        form of unique_exists_{x} [Q(x) ∧ P(x).]
        Return the conjunction (e.g., Q(x) ∧ P(x) in the example).
        '''
        from proveit.logic import And
        return And(condition, instance_expr)
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, unique_exists_{x | Q(x)} P(x) is a stylized
        form of unique_exists_{x} [Q(x) ∧ P(x).]
        Return the condition and instance_expr as a tuple.  For the example,
        this would return (Q(x), P(x)).
        '''
        from proveit.logic import And
        if isinstance(lambda_body, And) and lambda_body.operands.is_double():
            return tuple(lambda_body.operands)
        return None, lambda_body

    def _readily_provable(self):
        '''
        Return True iff we should be able to conclude this NotExists;
        specifically if the equilent universal quantification is readily
        provable: 
        '''
        return self.as_defined().readily_provable()

    @prover
    def conclude(self, **defaults_config):
        if self.as_defined().readily_provable():
            return self.conclude_as_folded()

    def incidentals(self, judgment):
        '''
        Side-effect derivations to attempt automatically 
        for a UniqueExists operation.
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, var1, var2, **defaults_config):
        '''
        Return definition of this UniqueExists quantifier as an
        equation with this UniqueExists quantifier on the left
        and a negated universal quantification on the right. This
        handles two separate cases: with and w/out conditions:
            1. ∃!_x P(x)
            2. ∃!_{x | Q(x)} P(x)
        which return:
            1. ∃_x P(x) ∧ [∀_{w, z | P(w), P(z)} w=z]
            2. ∃_{x | Q(x)} P(x) ∧ [∀_{w, z | Q(w), Q(z), P(w), P(z)} w=z]
        respectively where w=var1 and z=var2,
        as well as multi-parameter variants.
        '''
        if self.instance_params.is_single():
            _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_y, self.condition)
            else:
                _Q = None
            _P = Lambda(_y, self.instance_expr)
            if _Q is None:
                from . import unique_exists_by_def
                thm = unique_exists_by_def
            else:
                from . import conditional_unique_exists_by_def
                thm = conditional_unique_exists_by_def
            if _Q is None:
                return thm.instantiate({y:_y, w:var1, z:var2, P:_P})
            else:
                return thm.instantiate({y:_y, w:var1, z:var2, P:_P, Q:_Q})
        else:
            raise NotImplementedError("multi-parameter existence definition will"
                                      " be implemented later.")

    @prover
    def unfold(self, var1=None, var2=None, **defaults_config):
        '''
        Derive and return
        Forall_{x | Q(x)} P(x)) ∧ Forall_{w, z | Q(w), Q(z)} P(x))
        from UniqueExists_{x | Q(x)} P(x)
        where w=var1 and z=var2.
        '''
        if self.instance_params.is_single():
            _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_y, self.condition)
            else:
                _Q = None
            _P = Lambda(_y, self.instance_expr)
            if _Q is None:
                from . import unique_exists_unfolding
                thm = unique_exists_unfolding
            else:
                from . import conditional_unique_exists_unfolding
                thm = conditional_unique_exists_unfolding
            sub_dict = {y:_y, P:_P}
            if var1 is not None: sub_dict[w] = var1
            if var2 is not None: sub_dict[z] = var2
            if _Q is not None: sub_dict[Q] = _Q
            return thm.instantiate(sub_dict).derive_consequent()
        else:
            from . import multiparam_unique_exists_unfolding
            _x = _y = self.instance_params
            _n = _x.num_elements()
            _Q = Lambda(_x, self.conditions)
            _P = Lambda(_x, self.instance_expr)
            return multiparam_unique_exists_unfolding.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) 
        from Not(Exists_{x | Q(x)} P(x)).
        '''
        if self.instance_params.is_single():
            _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_y, self.condition)
            else:
                _Q = None
            _P = Lambda(_y, self.instance_expr)
            if _Q is None:
                from . import unique_exists_folding
                thm = unique_exists_folding
            else:
                from . import conditional_unique_exists_folding
                thm = conditional_unique_exists_folding
            if _Q is None:
                return thm.instantiate({y:_y, P:_P}).derive_consequent()
            else:
                return thm.instantiate(
                    {y:_y, P:_P, Q:_Q}).derive_consequent()
        else:
            from . import multiparam_unique_exists_folding
            _x = _y = self.instance_params
            _n = _x.num_elements()
            _Q = Lambda(_x, self.conditions)
            _P = Lambda(_x, self.instance_expr)
            return multiparam_unique_exists_folding.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()

    def as_defined(self):
        '''
        Return the equivalent form that would result from
        self.definition().rhs (up to the choice of instance parameters
        which is not important when quantified).
        '''
        from proveit.logic import And, Forall, Exists, Implies, Equals
        _w, _z = safe_dummy_vars(2, self)
        if self.instance_params.is_single():
            _y = self.instance_param
            _Pw = self.instance_expr.basic_replaced({_y:_w})
            _Pz = self.instance_expr.basic_replaced({_y:_z})
            if hasattr(self, 'condition'):
                _Qw = self.condition.basic_replaced({_y:_w})
                _Qz = self.condition.basic_replaced({_y:_z})
                return And(Exists(_y, self.instance_expr,
                                  condition=self.condition), 
                           Forall((_w, _z), Implies(And(_Pw, _Pz),
                                                    Equals(_w, _z)),
                                  conditions=[_Qw, _Qz]))
            else:
                return And(Exists(_y, self.instance_expr), 
                           Forall((_w, _z), Equals(_w, _z),
                                  conditions=[_Pw, _Pz]))
        else:
            raise NotImplementedError(
                "multi-parameter UniqueExists.as_defined() will"
                " be implemented later.")
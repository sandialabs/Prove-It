from proveit import OperationOverInstances
from proveit import (Literal, Operation, Lambda, 
                     prover, equality_prover, relation_prover)
from proveit import n, x, y, P, Q, S


class NotExists(OperationOverInstances):
    # operator of the NotExists operation
    _operator_ = Literal(
        string_format='notexists',
        latex_format=r'\nexists',
        theory=__file__)

    def __init__(self, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        '''
        Create a exists (there exists) expression:
        exists_{instance_param_or_params | conditions} instance_expr
        This expresses that there exists a value of the instance 
        parameters(s) for which the optional condition(s) is/are
        satisfied and the instance_expr is true.  The instance 
        parameters(s) and condition(s) may be singular or plural
        (iterable).
        '''
        OperationOverInstances.__init__(
            self, NotExists._operator_, instance_param_or_params,
            instance_expr, domain=domain, domains=domains,
            condition=condition, conditions=conditions,
            styles=styles, _lambda_map=_lambda_map)

    def _readily_provable(self):
        '''
        Return True iff we should be able to conclude this NotExists;
        specifically if the equilent universal quantification is readily
        provable: 
        '''
        return self.equivalent_universal_quantification().readily_provable()

    @prover
    def conclude(self, **defaults_config):
        if self.equivalent_universal_quantification().readily_provable():
            return self.conclude_as_folded()

    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, ∄_{x | Q(x)} P(x) is a stylized form
        of ∄_{x} [Q(x) ∧ P(x).]
        Return the conjunction (e.g., Q(x) ∧ P(x) in the example).
        '''
        from proveit.logic import And
        return And(condition, instance_expr)
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        '''
        The condition for an existential quantifier is effected via a
        conjunction. That is, ∄_{x | Q(x)} P(x) is a stylized form
        of ∄_{x} [Q(x) ∧ P(x).]
        Return the condition and instance_expr as a tuple.  For the example,
        this would return (Q(x), P(x)).
        '''
        from proveit.logic import And
        if isinstance(lambda_body, And) and lambda_body.operands.is_double():
            return tuple(lambda_body.operands)
        return None, lambda_body
    
    def incidentals(self, judgment):
        '''
        Side-effect derivations to attempt automatically 
        for a NotExists operation.
        '''
        yield self.unfold  # unfolded form: Not(Exists(..))

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Return definition of this NotExists quantifier as an
        equation with this NotExists quantifier on the left
        and a negated universal quantification on the right. This
        handles two separate cases: with and w/out conditions:
            1. ∄_x P(x)
            2. ∄_{x | Q(x)} P(x)
        which return:
            1. ∀_x ¬P(x)
            2. ∀_{x | Q(x)} ¬P(x)
        respectively where w=var1 and z=var2,
        as well as multi-parameter variants.
        '''
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            _P = Lambda(_x, self.instance_expr)
            if _Q is None:
                from . import not_exists_by_def
                thm = not_exists_by_def
            else:
                from . import conditional_not_exists_by_def
                thm = conditional_not_exists_by_def
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P})
            else:
                return thm.instantiate({x:_x, y:_y, P:_P, Q:_Q})
        else:
            raise NotImplementedError("multi-parameter existence definition will"
                                      " be implemented later.")

    @prover
    def unfold(self, **defaults_config):
        '''
        Derive and return Not(Exists_{x | Q(x)} P(x)) from 
        NotExists_{x | Q(x)} P(x).
        '''
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            _P = Lambda(_x, self.instance_expr)
            if _Q is None:
                from . import not_exists_unfolding
                thm = not_exists_unfolding
            else:
                from . import conditional_not_exists_unfolding
                thm = conditional_not_exists_unfolding
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P}).derive_consequent()
            else:
                return thm.instantiate(
                    {x:_x, y:_y, P:_P, Q:_Q}).derive_consequent()
        else:
            from . import multiparam_not_exists_unfolding
            _x = _y = self.instance_params
            _n = _x.num_elements()
            _Q = Lambda(_x, self.conditions)
            _P = Lambda(_x, self.instance_expr)
            return multiparam_not_exists_unfolding.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()

    def as_defined(self):
        '''
        Return the equivalent form that would result from
        self.definition().rhs.
        '''
        return self.equivalent_universal_quantification()

    def equivalent_universal_quantification(self):
        from proveit.logic import Forall, Not
        if self.instance_params.is_single():
            _x = self.instance_params[0]
            if isinstance(self.instance_expr, Not):
                _P = self.instance_expr.operand
            else:
                _P = Not(self.instance_expr)
            if hasattr(self, 'condition'):
                _Q = self.condition
            else:
                _Q = None
            
            if _Q is None:
                return Forall(_x, _P)
            else:
                return Forall(_x, _P, condition=_Q)

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) 
        from Not(Exists_{x | Q(x)} P(x)).
        '''
        if self.instance_params.is_single():
            _x = _y = self.instance_params[0]
            if hasattr(self, 'condition'):
                _Q = Lambda(_x, self.condition)
            else:
                _Q = None
            _P = Lambda(_x, self.instance_expr)
            if _Q is None:
                from . import not_exists_folding
                thm = not_exists_folding
            else:
                from . import conditional_not_exists_folding
                thm = conditional_not_exists_folding
            if _Q is None:
                return thm.instantiate({x:_x, y:_y, P:_P}).derive_consequent()
            else:
                return thm.instantiate(
                    {x:_x, y:_y, P:_P, Q:_Q}).derive_consequent()
        else:
            from . import multiparam_not_exists_folding
            _x = _y = self.instance_params
            _n = _x.num_elements()
            _Q = Lambda(_x, self.conditions)
            _P = Lambda(_x, self.instance_expr)
            return multiparam_not_exists_folding.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()

    @prover
    def conclude_via_forall(self, **defaults_config):
        '''
        Prove and return either some 
        NotExists_{x | Q(x)} Not(P(x)) or NotExists_{x | Q(x)} P(x)
        from forall_{x | Q(x)} P(x) 
        or from forall_{x | Q(x)} (P(x) != TRUE)
        respectively.
        '''
        exists_conditions = True
        if len(self.conditions) == 0:
            exists_conditions = False
        from . import forall_implies_not_exists_not, not_exists_via_forall
        from . import forall_implies_not_exists_not_no_conditions
        from . import not_exists_via_forall_no_conditions
        from proveit.logic import Not, NotEquals, TRUE
        _x = _y = self.instance_params
        _n = _x.num_elements()
        _Q = Lambda(_x, self.conditions)
        if isinstance(self.instance_expr, Not):
            _P = Lambda(_x, self.instance_expr.operand)
            if exists_conditions:
                return forall_implies_not_exists_not.instantiate(
                    {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()
            else:
                return forall_implies_not_exists_not_no_conditions.instantiate(
                    {x: _x, y: _y, n: _n, P: _P}).derive_consequent()
        else:
            _P = Lambda(_x, self.instance_expr)
            if exists_conditions:
                return not_exists_via_forall.instantiate(
                    {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()
            else:
                return not_exists_via_forall_no_conditions.instantiate(
                    {x: _x, y: _y, n: _n, P: _P}).derive_consequent()

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
        from . import notexists_is_bool, notexists_with_conditions_is_bool
        _x = self.instance_params
        _P = Lambda(_x, self.instance_expr)
        _n = _x.num_elements()
        if self.conditions.num_entries() == 0:
            return notexists_is_bool.instantiate(
                {n: _n, P: _P, x: _x})
        _Q = Lambda(_x, self.condition)
        return notexists_with_conditions_is_bool.instantiate(
                {n: _n, P: _P, Q: _Q, x: _x}, preserve_expr=self,
                auto_simplify=True)

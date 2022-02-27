from proveit import OperationOverInstances
from proveit import Literal, Operation, prover
from proveit import P, Q, S


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

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically 
        for a NotExists operation.
        '''
        yield self.unfold  # unfolded form: Not(Exists(..))

    @prover
    def unfold(self, **defaults_config):
        '''
        Derive and return Not(Exists_{x | Q(x)} P(x)) from 
        NotExists_{x | Q(x)} P(x).
        '''
        from . import not_exists_unfolding
        _x = _y = self.instance_params
        _Q = Lambda(_x, self.conditions)
        _P = Lambda(_x, self.instance_expr)
        return not_exists_unfolding.instantiate(
            {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Prove and return some NotExists_{x | Q(x)} P(x) 
        from Not(Exists_{x | Q(x)} P(x)).
        '''
        from . import not_exists_folding
        _x = _y = self.instance_params
        _Q = Lambda(_x, self.conditions)
        _P = Lambda(_x, self.instance_expr)
        return not_exists_folding.instantiate(
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
        from . import forall_implies_not_exists_not, not_exists_via_forall
        from proveit.logic.equality.eq_ops import NotEquals
        from bool_ops import Not
        from bool_set import TRUE
        _x = _y = self.instance_params
        _n = _x.num_elements()
        _Q = Lambda(_x, self.conditions)
        if isinstance(self.instance_expr, Not):
            _P = Lambda(_x, self.instance_expr.operand)
            return forall_implies_not_exists_not.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()
        else:
            _P = Lambda(_x, self.instance_expr.operand)
            return not_exists_via_forall.instantiate(
                {x: _x, y: _y, n: _n, P: _P, Q:_Q}).derive_consequent()


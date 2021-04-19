from proveit import (Literal, OperationOverInstances, Operation, ExprTuple,
                     single_or_composite_expression, USE_DEFAULTS)
from proveit import x, y, f, P, Q, S


class SetOfAll(OperationOverInstances):
    # operator of the SetOfAll operation
    _operator_ = Literal(string_format='SetOfAll',
                         latex_format=r'\textrm{SetOfAll}', theory=__file__)
    _init_argname_mapping_ = {'instance_element': 'instance_expr'}

    def __init__(self, instance_param_or_params, instance_element,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        '''
        Create an expression representing the set of all
        instance_element for instance parameter(s) such that the conditions
        are satisfied:
        {instance_element | conditions}_{instance_param_or_params \in S}
        '''
        OperationOverInstances.__init__(
            self, SetOfAll._operator_, instance_param_or_params,
            instance_element, domain=domain, domains=domains,
            condition=condition, conditions=conditions,
            styles=styles, _lambda_map=_lambda_map)
        self.instance_element = self.instance_expr
        if hasattr(self, 'instance_param'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instance_params'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires domains")
        else:
            assert False, ("Expecting either 'instance_param' or 'instance_params' "
                           "to be set")

    def _formatted(self, format_type, fence=False, **kwargs):
        from proveit import ExprRange
        out_str = ''
        explicit_conditions = ExprTuple(*self.explicit_conditions())
        inner_fence = (explicit_conditions.num_entries() > 0)
        formatted_instance_element = self.instance_element.formatted(
            format_type, fence=inner_fence)
        explicit_domains = self.explicit_domains()
        domain_conditions = ExprTuple(*self.domain_conditions())
        if format_type == 'latex':
            out_str += r"\left\{"
        else:
            out_str += "{"
        out_str += formatted_instance_element
        if explicit_conditions.num_entries() > 0:
            formatted_conditions = explicit_conditions.formatted(
                format_type, fence=False)
            if format_type == 'latex':
                out_str += r'~|~'
            else:
                out_str += ' s.t. '  # such that
            out_str += formatted_conditions
        if format_type == 'latex':
            out_str += r"\right\}"
        else:
            out_str += "}"
        out_str += '_{'
        instance_param_or_params = self.instance_param_or_params
        if (not any(isinstance(entry, ExprRange) for entry in explicit_domains)
                and explicit_domains == [explicit_domains[0]] * len(explicit_domains)):
            # all in the same domain
            out_str += instance_param_or_params.formatted(
                format_type, operator_or_operators=',', fence=False)
            out_str += r' \in ' if format_type == 'latex' else ' in '
            out_str += explicit_domains[0].formatted(format_type)
        else:
            out_str += domain_conditions.formatted(format_type,
                                                   operator_or_operators=',',
                                                   fence=False)
        out_str += '}'
        return out_str

    """
    # The below must be updated

    def unfold_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from . import unfold_comprehension, unfold_basic_comprehension, unfold_basic1_cond_comprehension, in_superset_if_in_comprehension
        Q_op, Q_op_sub = Function(Qmulti, self.instance_var), self.conditions
        if len(self.instance_vars) == 1 and self.instance_element == self.instance_vars[0]:
            in_superset_if_in_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instance_vars[0]}, assumptions=assumptions) # x in S side-effect
            if len(self.conditions) == 1:
                Q_op, Q_op_sub = Function(Q, self.instance_vars), self.conditions[0]
                return unfold_basic1_cond_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, x:element},  {y:self.instance_vars[0]}, assumptions=assumptions)
            else:
                return unfold_basic_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instance_vars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Function(f, self.instance_vars), self.instance_element
            return unfold_comprehension.instantiate({S:self.domain,  Q_op:Q_op_sub, f_op:f_sub, x:element}, {y_multi:self.instance_vars}).derive_conclusion(assumptions)

    def deduce_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''
        from . import fold_comprehension, fold_basic_comprehension
        Q_op, Q_op_sub = Function(Qmulti, self.instance_vars), self.conditions
        if len(self.instance_vars) == 1 and self.instance_element == self.instance_vars[0] and len(self.conditions) == 1:
            Pop, Psub = Function(P, self.instance_vars), self.conditions[0]
            return fold_basic_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instance_vars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Function(f, self.instance_vars), self.instance_element
            return fold_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, f_op:f_sub, x:element}, {y_multi:self.instance_vars}).derive_conclusion(assumptions)
    """

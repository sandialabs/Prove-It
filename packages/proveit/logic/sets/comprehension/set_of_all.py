from proveit import (
        ExprTuple, Function, Literal, OperationOverInstances,
        Lambda, composite_expression, relation_prover, defaults)
from proveit import f, n, x, y, Q, R, S


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
        instance_element = self.instance_element
        if hasattr(self, 'condition'):
            with defaults.temporary() as temp_defaults:
                # Add the condition as an assumption when formatting 
                # the instance expression.
                temp_defaults.assumptions = defaults.assumptions + (
                        self.condition,)
                formatted_instance_element =  instance_element.formatted(
                    format_type, fence=inner_fence)
        else:
            formatted_instance_element = instance_element.formatted(
                    format_type, fence=inner_fence)
        explicit_domains = self.explicit_domains()
        has_multi_domain = not self.has_one_domain()
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
        if has_multi_domain:
            out_str += domain_conditions.formatted(
                    format_type, operator_or_operators=',', fence=False)
        else:
            # all in the same domain
            out_str += instance_param_or_params.formatted(
                format_type, operator_or_operators=',', fence=False)
            out_str += r' \in ' if format_type == 'latex' else ' in '
            out_str += explicit_domains[0].formatted(format_type)
        out_str += '}'
        return out_str

    @relation_prover
    def deduce_superset_eq_relation(self, superset, **defaults_config):
        '''
        Try to prove {f(x) | Q(x)_{x in S) subset_eq `superset`.
        '''
        from . import subset_via_condition_constraint
        if isinstance(superset, SetOfAll):
            _x = composite_expression(self.instance_param_or_params)
            _y = superset.instance_param_or_params
            _f = Lambda(_y, superset.instance_element)
            _g = Lambda(_x, self.instance_element)
            if (_f == _g and 
                    self.explicit_domains() == superset.explicit_domains()):
                _Q = Lambda(superset.instance_param_or_params, 
                            superset.non_domain_condition())
                _R = Lambda(self.instance_param_or_params, 
                            self.non_domain_condition())
                _S = self.explicit_domains()
                _n = _x.num_elements()
                impl = subset_via_condition_constraint.instantiate(
                    {n:_n, f:_f, S:_S, Q:_Q, R:_R, x:_x, y:_y})
                return impl.derive_consequent()
        raise NotImplementedError(
                "SetOfAll.deduce_superset_eq_relation only implemented "
                "to prove a superset relation with another SetOfAll that "
                "has the same domain and instance mapping: %s vs %s"
                %(self, superset))

    @relation_prover
    def deduce_subset_eq_relation(self, subset, **defaults_config):
        '''
        Try to prove {f(x) | Q(x)_{x in S) subset_eq `superset`.
        '''
        if not isinstance(subset, SetOfAll):
            raise NotImplementedError(
                    "SetOfAll.deduce_subset_eq_relation only implemented "
                    "to prove a subset relation with another SetOfAll that "
                    "has the same domain and instance mapping: %s vs %s"
                    %(self, subset))
        return subset.deduce_superset_eq_relation(self)

    # The below must be updated
    # Being updated gradually by wdc starting 12/21/2021

    @relation_prover
    def unfold_membership(self, element, **defaults_config):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return
        [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return
        [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return
        exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from . import (unfold, unfold_basic_comprehension,
                       in_superset_if_in_comprehension)
        from proveit.logic import And
        if len(self.explicit_conditions())==1:
            explicit_conditions = self.explicit_conditions()[0]
        else:
            explicit_conditions = And(*self.explicit_conditions())
        # why is the following line there before testing number of vars
        _Q_op, _Q_op_sub = Function(Q, self.all_instance_vars()), explicit_conditions
        if (len(self.all_instance_vars()) == 1 and
            self.instance_element == self.instance_var):
            # simple case of {x | Q(x)}_{x in S};
            # derive x in S side-effect
            print("(1) SetOfAll.unfold_membership(): inside first if.")
            print("_Q_op = ")
            display(_Q_op)
            print("_Q_op_sub = ")
            display(_Q_op_sub)
            in_superset_if_in_comprehension.instantiate(
                    {S: self.domain, _Q_op: _Q_op_sub,
                     x: element, y: self.instance_var})
            print("SetOfAll.unfold_membership(): end")
            if len(self.explicit_conditions())==1:
                _Q_op, _Q_op_sub = (
                    Function(Q, self.all_instance_vars()), explicit_conditions)
            #     return unfold_basic1_cond_comprehension.instantiate(
            #             {S:self.domain, Q_op:Q_op_sub,
            #              x:element, y:self.instance_vars[0]})
            # else:
            #     return unfold_basic_comprehension.instantiate({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instance_vars[0]}, assumptions=assumptions)
        # else:
        #     f_op, f_sub = Function(f, self.instance_vars), self.instance_element
        #     return unfold_comprehension.instantiate({S:self.domain,  Q_op:Q_op_sub, f_op:f_sub, x:element}, {y_multi:self.instance_vars}).derive_conclusion(assumptions)



    """

    @prover
    def unfold_membership(self, element, **defaults_config):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return
        [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return
        [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return
        exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from . import (unfold_comprehension, unfold_basic_comprehension,
                       unfold_basic1_cond_comprehension,
                       in_superset_if_in_comprehension)
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

    @prover
    def deduce_membership(self, element, **defaults_config):
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

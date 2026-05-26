from proveit import (
        ExprTuple, Operation, OperationOverInstances, Function, Literal,
        Variable, Lambda, composite_expression, NamedExprs, free_vars,
        relation_prover, defaults)
from proveit import f, n, x, y, Q, R, S
from proveit.logic.sets.membership import InSet


class SetOfAll(OperationOverInstances):
    # operator of the SetOfAll operation
    _operator_ = Literal(string_format='SetOfAll',
                         latex_format=r'\textrm{SetOfAll}', theory=__file__)

    def __init__(self, instance_param_or_params, instance_element,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, styles=None,
                 _lambda_map=None):
        '''
        Create an expression representing the set of all
        instance_element for instance parameter(s) such that the conditions
        are satisfied:
        {f(x) | x ∈ S, Q(x)}, represented internally as
        SetOfAll(x ↦ {'instance_element': f(x),
                      'condition': (x ∈ S ∧ Q(x)))
        '''
        if _lambda_map is not None:
            # Remake from the first operand lambda map.
            OperationOverInstances.__init__(
                self, SetOfAll._operator_, None, None,
                styles=styles, _lambda_map=_lambda_map)
            self.instance_element = self._instance_expr
            return
            
        OperationOverInstances.__init__(
            self, SetOfAll._operator_, instance_param_or_params,
            instance_element, domain=domain, domains=domains,
            condition=condition, conditions=conditions,
            styles=styles, _lambda_map=_lambda_map)
        self.instance_element = self._instance_expr
        if hasattr(self, 'instance_param'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instance_params'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires domains")
        else:
            assert False, ("Expecting either 'instance_param' or 'instance_params' "
                           "to be set")

    @property
    def instance_expr(self):
        raise AttributeError('Use instance_element not instance_expr for SetOfAll')

    @classmethod
    def _create_operand(cls, instance_param_or_params, instance_expr, conditions):
        assert conditions.num_entries() > 0
        if conditions.is_single():
            condition = conditions[0]
        else:
            from proveit.logic import And
            condition = And(*conditions)
        body = cls._create_instance_expr_with_condition(
            instance_expr, condition)
        return Lambda(instance_param_or_params, body)
    
    @classmethod
    def _create_instance_expr_with_condition(cls, instance_expr, condition):
        return NamedExprs(('instance_element', instance_expr),
                          ('condition', condition))
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        # Intenally, the instance expression is the condition.
        assert isinstance(lambda_body, NamedExprs)
        return lambda_body['condition'], lambda_body['instance_element']

    def extract_my_init_arg_value(self, arg_name):
        if arg_name == 'instance_element':
            return self.operand.body['instance_element']
        return OperationOverInstances.extract_my_init_arg_value(self, arg_name)

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions
        options = StyleOptions(self)
        options.add_option(
            name = 'wrap_param_positions',
            description = (
                    "position(s) at which wrapping of parameters is to occur; "
                    "'2 n - 1' is after the nth operand, '2 n' is "
                    "after the nth parameter."),
            default = '()',
            related_methods = (
                    'with_param_wrapping_at', 
                    'without_param_wrapping',
                    'wrap_param_positions'))
        options.add_option(
            name = 'param_justification',
            description = ("justify to the 'left', 'center', or 'right' "
                           "in the array cells for wrapped parameters"),
            default = 'left',
            related_methods = ('with_condition_justification',
                               'with_param_wrapping_at'))     
        options.add_option(
            name = 'suchthat_wrapping',
            description = ("Wrap 'before' or 'after' the '|' that separates "
                           "the parameter(s) from the condition(s) (or None)."),
            default = None,
            related_methods = ('with_wrap_after_suchthat',
                               'with_wrap_before_suchthat',
                               'without_suchthat_wrapping')),
        options.add_option(
            name = 'suchthat_justification',
            description = ("justify to the 'left', 'center', or 'right' "
                           "in the array cells for wrapping before/after '|' "
                           "that divides parameter(s) and condition(s)"),
            default = 'left',
            related_methods = ('with_suchthat_justification',
                               'with_wrap_after_suchthat',
                               'with_wrap_before_suchthat'))
        options.add_option(
            name = 'wrap_condition_positions',
            description = (
                    "position(s) at which wrapping of conditions is to occur; "
                    "'2 n - 1' is after the nth operand, '2 n' is "
                    "after the nth condition."),
            default = '()',
            related_methods = (
                    'with_condition_wrapping_at', 
                    'without_condition_wrapping',
                    'wrap_condition_positions'))
        options.add_option(
            name = 'condition_justification',
            description = ("justify to the 'left', 'center', or 'right' "
                           "in the array cells for wrapped conditions"),
            default = 'left',
            related_methods = ('with_condition_justification',
                               'with_condition_wrapping_at')),
        return options

    def with_param_wrapping_at(self, *wrap_positions):
        return self.with_styles(
            wrap_param_positions='(' +
            ' '.join(
                str(pos) for pos in wrap_positions) +
            ')')

    def without_param_wrapping(self, *wrap_positions):
        return self.with_param_wrapping_at()

    def with_param_justification(self, justification):
        return self.with_styles(param_justification=justification)

    def wrap_param_positions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.get_style(
            'wrap_param_positions', '').strip('()').split(' ') if pos_str != '']
    
    def with_wrap_before_suchthat(self):
        return self.with_styles(suchthat_wrapping='before')

    def with_wrap_after_suchthat(self):
        return self.with_styles(suchthat_wrapping='after')
    
    def without_suchthat_wrapping(self):
        return self.with_styles(suchthat_wrapping=None)

    def with_suchthat_justification(self, justification):
        return self.with_styles(suchthat_justification=justification)

    def with_condition_wrapping_at(self, *wrap_positions):
        return self.with_styles(
            wrap_condition_positions='(' +
            ' '.join(
                str(pos) for pos in wrap_positions) +
            ')')

    def without_condition_wrapping(self, *wrap_positions):
        return self.with_condition_wrapping_at()

    def with_condition_justification(self, justification):
        return self.with_styles(condition_justification=justification)

    """
    def with_param_range_indices(self, start_index_or_indices,
                                end_index_or_indices):
        if not isinstance(start_index_or_indices, Expression) or (
                not isinstance(end_index_or_indices, Expression)):
            start_index_or_indices = composite_expression(start_index_or_indices)
            end_index_or_indices = composite_expression(end_index_or_indices)
        return self.with_styles(param_range_start=start_index_or_indices,
                                param_range_end=end_index_or_indices)
    """

    def wrap_condition_positions(self):
        '''
        Return a list of wrap condition positions according to the current
        style setting.
        '''
        return [int(pos_str) for pos_str in self.get_style(
            'wrap_condition_positions', '').strip('()').split(' ')
            if pos_str != '']

    def _formatted(self, format_type, fence=False, **kwargs):
        # style call to wrap the expression after the parameters
        suchthat_wrapping = self.get_style('suchthat_wrapping', 'No')
        if suchthat_wrapping == 'No': suchthat_wrapping=None
        suchthat_justification = self.get_style('suchthat_justification', 'left')
        param_justification = self.get_style('param_justification', 'left')
        condition_justification = self.get_style('condition_justification', 'left')
        instance_element = self.instance_element

        (param_membership_conditions, explicit_conditions, 
         formatted_membership_op, formatted_class) = (
            self.param_membership_formatting_info(format_type))
        # Note: there may be an expression range parameter 
        # - that would have one entry
        has_multi_domain = (len(explicit_conditions) < len(self.conditions)
                            and formatted_class is None)
        with defaults.temporary() as temp_defaults:
            # Add the conditions as assumptions when formatting 
            # the instance expression.
            temp_defaults.automation = False
            temp_defaults.assumptions = defaults.assumptions + (
                    self.conditions)
            formatted_instance_elem =  instance_element.formatted(
                format_type, fence=True)

        if format_type == 'latex':
            out_str = r"\left\{"
        else:
            out_str = "{"
        out_str += formatted_instance_elem

        if format_type == 'latex' and suchthat_wrapping is not None:
            out_str += r'\scriptsize \begin{array}{%s}'%suchthat_justification[0]

        if suchthat_wrapping == 'before':
            if format_type == 'latex':
                out_str += r'\\'
            out_str += '\n'
        else:
            if format_type == 'latex':
                out_str += '~'
            else:
                out_str += ' '
        out_str += "|"
        if suchthat_wrapping == 'after':
            if format_type == 'latex':
                out_str += r'\\'
            out_str += '\n'
        else:
            if format_type == 'latex':
                out_str += '~'
            else:
                out_str += ' '

        if has_multi_domain:
            out_str += param_membership_conditions.formatted(
                format_type, operator_or_operators=',', 
                wrap_positions=self.wrap_param_positions(),
                justification=param_justification, fence=False)
        else:
            # 1 domain for all instance parameters
            out_str += self.instance_params.formatted(
                format_type, operator_or_operators=',', 
                wrap_positions=self.wrap_param_positions(), 
                justification=param_justification, fence=False)
            assert (formatted_membership_op == 
                    InSet._operator_.formatted(format_type))
            out_str += ' %s '%formatted_membership_op
            out_str += formatted_class
        out_str += ', '
        if len(explicit_conditions) > 0:
            wrap_condition_positions = self.wrap_condition_positions()
            if len(wrap_condition_positions) > 0 and format_type == 'latex':
                out_str += r'\scriptsize'
            out_str += explicit_conditions.formatted(
                format_type, fence=False, operator_or_operators=',', 
                wrap_positions=self.wrap_condition_positions(),
                justification=condition_justification)
        if format_type == 'latex' and suchthat_wrapping is not None:
            out_str += r'\end{array}'
        if format_type == 'latex':
            out_str += r"\right\}"
        else:
            out_str += "}"
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

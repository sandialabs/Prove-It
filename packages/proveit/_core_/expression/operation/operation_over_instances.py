import inspect
from proveit._core_.expression.expr import (
    Expression, MakeNotImplemented, free_vars)
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda, get_param_var
from proveit._core_.expression.composite import (
    ExprTuple, is_single, single_or_composite_expression, 
    composite_expression, ExprRange)
from proveit._core_.expression.conditional import Conditional
from proveit._core_.defaults import USE_DEFAULTS
from .operation import Operation, OperationError
from .function import Function


def _extract_domain_from_condition(ivar, condition):
    '''
    Given a "domain" condition (e.g., "x in S" or "(x_1 in S), ..., (x_n in S)")
    return the domain (e.g., "S").  Return None if the condition is not
    a "domain" condition for the given instance variable(s).
    '''
    from proveit.logic import InSet
    if isinstance(ivar, ExprRange):
        # See if the condition is a range of domain conditions
        # matching the instance variable range.
        # For example, x_1, ..., x_n as the instance variable
        # range matching x_1 in S_1, ..., x_n in S_n.
        if (isinstance(condition, ExprRange)
                and isinstance(condition.body, InSet)
                and condition.start_index == ivar.start_index
                and condition.end_index == ivar.end_index):
            # Replace the condition parameter with the ivar parameter
            # and see if the InSet element matches ivar.body.
            cond_body_elem_with_repl_param = condition.body.element.replaced(
                {condition.parameter: ivar.parameter})
            if cond_body_elem_with_repl_param == ivar.body:
                if condition.parameter in free_vars(condition.body.domain,
                                                    err_inclusively=True):
                    # There is a range of domains matching a range of
                    # parameters.
                    return ExprRange(
                        condition.parameter, condition.body.domain,
                        condition.start_index, condition.end_index)
            return condition.body.domain
    elif isinstance(condition, InSet) and condition.element == ivar:
        return condition.domain
    return None


class OperationOverInstances(Operation):
    '''
    OperationOverInstances description: TODO
    '''

    '''
    When deriving from OperationOverInstances, set the '_init_argname_mapping'
    static variable to indicate how the initialization argument names in the
    derived class correspond with the OperationOverInstances argument names.
    Omitted keys will be presumed to be unchanged argument names.  This is
    a simple way to make extract_my_init_arg_value function properly without
    overriding it.
    '''
    _init_argname_mapping_ = {
        'instance_param_or_params': 'instance_param_or_params',
        'instance_expr': 'instance_expr',
        'domain': 'domain',
        'domains': 'domains',
        'conditions': 'conditions'}

    def __init__(self, operator, instance_param_or_params, instance_expr, *,
                 domain=None, domains=None, condition=None, conditions=None,
                 styles=None, _lambda_map=None):
        '''
        Create an Operation for the given operator that is applied over
        instances of the given instance parameter(s), instance_param_or_params,
        for the given instance Expression,  instance_expr under the given
        conditions.  That is, the operation operates over all possibilities of
        given Variable(s) wherever the condition(s) is/are satisfied.  Examples
        include forall, exists, summation, etc. instance_param_or_params may be
        singular or plural (iterable).  Each parameter may be a Variable or
        Iter over IndexedVars (just as a Lambda parameter).  An
        OperationOverInstances is effected as an Operation over a Lambda map
        with a conditional body.

        If a 'domain' is supplied, additional conditions are generated that
        each instance parameter is in the domain "set": InSet(x_i, domain),
        where x_i is for each instance parameter.  If, instead, 'domains' are
        supplied, then each instance parameter is supplied with its own domain
        (one for each instance parameter).  Whether the OperationOverInstances
        is constructed with domain/domains explicitly, or they are provided as
        conditions in the proper order does not matter.  Essentially, the
        'domain' concept is simply a convenience for conditions of this form
        and may be formatted using a shorthand notation.
        For example, "forall_{x in S | Q(x)} P(x)" is a shorthand notation for
        "forall_{x | x in S, Q(x)} P(x)".

        _lambda_map is used internally for efficiently rebuilding an
        OperationOverInstances expression.
        '''
        from proveit.logic import InSet
        from proveit._core_.expression.lambda_expr.lambda_expr import get_param_var

        if styles is None:
            styles = dict()
        if 'with_wrapping' not in styles:
            styles['with_wrapping'] = 'False'
        if 'wrap_params' not in styles:
            styles['wrap_params'] = 'False'
        if 'justification' not in styles:
            styles['justification'] = 'center'

        if condition is not None:
            if conditions is not None:
                raise ValueError("Cannot specify both 'conditions' and "
                                 "'condition'")
            conditions = (condition,)
        elif conditions is None:
            conditions = tuple()
        elif isinstance(conditions, ExprTuple):
            conditions = conditions.entries

        if _lambda_map is not None:
            # Use the provided 'lambda_map' instead of creating one.
            from proveit.logic import And
            lambda_map = _lambda_map
            instance_params = lambda_map.parameters
            if isinstance(lambda_map.body, Conditional):
                # Has conditions.
                instance_expr = lambda_map.body.value
                if (isinstance(lambda_map.body.condition, And) and
                        not is_single(lambda_map.body.condition.operands)):
                    conditions = composite_expression(
                        lambda_map.body.condition.operands)
                else:
                    conditions = composite_expression(
                        lambda_map.body.condition)
            else:
                # No conditions.
                instance_expr = lambda_map.body
                conditions = ExprTuple()
        else:
            # We will need to generate the Lambda sub-expression.
            # Do some initial preparations w.r.t. instance_params, domain(s), and
            # conditions.
            instance_params = composite_expression(instance_param_or_params)
            if instance_params.num_entries() == 0:
                raise ValueError(
                    "Expecting at least one instance parameter when "
                    "constructing an OperationOverInstances")

            # Add appropriate conditions for the domains:
            if domain is not None:
                # prepend domain conditions
                if domains is not None:
                    raise ValueError(
                        "Provide a single domain or multiple domains, "
                        "not both")
                if not isinstance(domain, Expression):
                    raise TypeError(
                        "The domain should be an 'Expression' type")
                domains = [domain] * instance_params.num_entries()

            if domains is not None:
                # Prepend domain conditions.  Note that although we start with
                # all domain conditions at the beginning,
                # some may later get pushed back as "inner conditions"
                # (see below),
                if len(domains) != instance_params.num_entries():
                    raise ValueError(
                        "When specifying multiple domains, the number "
                        "should be the same as the number of instance "
                        "variables.")
                for domain in domains:
                    if domain is None:
                        raise ValueError(
                            "When specifying multiple domains, none "
                            "of them can be the None value")
                domain_conditions = []
                for iparam, domain in zip(instance_params, domains):
                    if isinstance(iparam, ExprRange):
                        if isinstance(domain, ExprRange):
                            if ((iparam.start_index != domain.start_index) or
                                    (iparam.end_index != domain.end_index)):
                                raise ValueError(
                                    "A range of parameters must match "
                                    "in start and end indices with the "
                                    "corresponding range of domains: "
                                    "%s vs %s and %s vs %s" %
                                    (iparam.start_index,
                                     domain.start_index,
                                     iparam.end_index, domain.end_index))
                            # Use the same parameter for the domain
                            # as the instance parameter.
                            domain_body_with_new_param = \
                                domain.body.replaced({domain.parameter:
                                                      iparam.parameter})
                            condition = ExprRange(
                                iparam.parameter,
                                InSet(iparam.body, domain_body_with_new_param),
                                iparam.start_index, iparam.end_index)
                        else:
                            condition = ExprRange(
                                iparam.parameter, InSet(iparam.body, domain),
                                iparam.start_index, iparam.end_index)
                    else:
                        condition = InSet(iparam, domain)
                    domain_conditions.append(condition)
                conditions = domain_conditions + list(conditions)
            conditions = composite_expression(conditions)

        # domain(s) may be implied via the conditions.  If domain(s) were
        # supplied, this should simply reproduce them from the conditions that
        # were prepended.
        domain = domains = None  # These may be reset below if there are ...
        if (conditions.num_entries() >= instance_params.num_entries()):
            domains = [_extract_domain_from_condition(ivar, cond) for
                       ivar, cond in zip(instance_params, conditions)]
            if all(domain is not None for domain in domains):
                # Used if we have a single instance variable
                domain = domains[0]
            else:
                domains = None

        if _lambda_map is None:
            # Now do the actual lambda_map creation
            if instance_params.num_entries() == 1:
                instance_param_or_params = instance_params[0]
            # Generate the Lambda sub-expression.
            lambda_map = OperationOverInstances._createOperand(
                instance_param_or_params, instance_expr, conditions)

        self.instance_expr = instance_expr
        '''Expression corresponding to each 'instance' in the OperationOverInstances'''

        self.instance_params = instance_params
        if (instance_params.num_entries() > 1 or
                isinstance(instance_params[0], ExprRange)):
            '''Instance parameters of the OperationOverInstance.'''
            self.instance_vars = [get_param_var(parameter) for
                                  parameter in instance_params]
            self.instance_param_or_params = self.instance_params
            self.instance_var_or_vars = self.instance_vars
            '''Instance parameter variables of the OperationOverInstance.'''
            if domains is not None:
                # Domain for each instance variable
                self.domains = tuple(domains)
                '''Domains of the instance parameters (may be None)'''
                n_domains = len(self.domains)
                if (not any(isinstance(entry, ExprRange) for entry
                            in self.domains)
                        and self.domains == tuple([self.domains[0]] * n_domains)):
                    # Multiple domains that are all the same.
                    self.domain = self.domains[0]
            else:
                self.domain = None
        else:
            self.instance_param = instance_params[0]
            '''Outermost instance parameter of the OperationOverInstance.'''
            self.instance_var = get_param_var(self.instance_param)
            self.instance_param_or_params = self.instance_param
            self.instance_var_or_vars = self.instance_var
            '''Outermost instance parameter variable of the OperationOverInstance.'''
            self.domain = domain
            '''Domain of the outermost instance parameter (may be None)'''

        self.conditions = conditions
        '''Conditions applicable to the outermost instance variable (or iteration of indexed variables) of the OperationOverInstance.  May include an implicit 'domain' condition.'''

        if isinstance(lambda_map.body, Conditional):
            self.condition = lambda_map.body.condition

        Operation.__init__(self, operator, lambda_map, styles=styles)

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        OperationOverInstances class is to include appropriate
        'with_wrapping', 'wrap_params', and 'with_justification' calls.
        '''
        with_wrapping = (self.get_style('with_wrapping', 'False') == 'True')
        wrap_params = (self.get_style('wrap_params', 'False') == 'True')
        justification = self.get_style('justification')
        call_strs = []
        if with_wrapping:
            call_strs.append('with_wrapping()')
        if wrap_params:
            call_strs.append('wrap_params()')
        if justification != 'center':
            call_strs.append('with_justification("' + justification + '")')
        return call_strs

    def effective_condition(self):
        '''
        Return the effective 'condition' of the OperationOverInstances.
        If there is no 'condition', return And operating on zero
        operands.
        '''
        if hasattr(self, 'condition'):
            return self.condition
        else:
            from proveit.logic import And
            return And()

    def has_domain(self):
        if hasattr(self, 'domains'):
            return self.domains is not None
        return self.domain is not None

    def first_domain(self):
        if hasattr(self, 'domains'):
            return self.domains[0]
        return self.domain

    @staticmethod
    def _createOperand(instance_param_or_params, instance_expr, conditions):
        if conditions.num_entries() == 0:
            return Lambda(instance_param_or_params, instance_expr)
        else:
            conditional = Conditional(instance_expr, conditions)
            return Lambda(instance_param_or_params, conditional)

    def extract_my_init_arg_value(self, arg_name):
        '''
        Return the most proper initialization value for the
        initialization argument of the given name in order to
        reconstruct this Expression in its current style.
        '''
        init_argname_mapping = self.__class__._init_argname_mapping_
        arg_name = init_argname_mapping.get(arg_name, arg_name)
        if arg_name == 'operator':
            return self.operator  # simply the operator
        elif arg_name == 'instance_param_or_params':
            # return the joined instance variables according to style.
            return single_or_composite_expression(
                OperationOverInstances.explicit_instance_params(self))
        elif arg_name == 'instance_expr':
            # return the inner instance expression after joining the
            # instance variables according to the style
            return self.instance_expr
        elif arg_name == 'domain' or arg_name == 'domains':
            # return the proper single domain or list of domains
            domains = OperationOverInstances.explicit_domains(self)
            if not hasattr(self, 'domain') or domains != [
                    self.domain] * len(domains):
                if arg_name == 'domains' and len(domains) > 0:
                    return ExprTuple(*domains)
                else:
                    return None
            if self.domain is None:
                return None
            return self.domain if arg_name == 'domain' else None
        elif arg_name == 'condition' or arg_name == 'conditions':
            # return the joined conditions excluding domain conditions
            conditions = composite_expression(
                OperationOverInstances.explicit_conditions(self))
            if conditions.num_entries() == 1 and arg_name == 'condition':
                return conditions[0]
            elif conditions.num_entries() > 1 and arg_name == 'conditions':
                return conditions
            return None

    @classmethod
    def _make(cls, core_info, styles, sub_expressions):
        if len(core_info) != 1 or core_info[0] != 'Operation':
            raise ValueError(
                "Expecting Operation core_info to contain exactly one item: 'Operation'")
        if len(sub_expressions) != 2:
            raise ValueError("Expecting exactly two sub_expressions for an "
                             "OperationOverInstances object: an operator and "
                             "a lambda_map.")

        implicit_operator = cls._implicitOperator()
        if implicit_operator is None:
            raise OperationError(
                "Expecting a '_operator_' attribute for class "
                "%s for the default OperationOverInstances._make "
                "method" %
                str(cls))

        operator = sub_expressions[0]
        lambda_map = sub_expressions[1]

        if not (operator == implicit_operator):
            raise OperationError("An implicit operator may not be changed")

        args, varargs, varkw, defaults, kwonlyargs, kwonlydefaults, _ = \
            inspect.getfullargspec(cls.__init__)
        if '_lambda_map' not in kwonlyargs:
            raise OperationError(
                "'_lambda_map' must be a keyword only argument "
                "for a constructor of a class %s derived from "
                "OperationOverInstances." %
                str(cls))

        # Subtract 'self' from the number of args and set
        # the rest to None.
        num_remaining_args = len(args) - 1
        made_operation = cls(
            *[None] * num_remaining_args,
            _lambda_map=lambda_map)
        if styles is not None:
            made_operation.with_styles(**styles)
        return made_operation

    def _all_instance_params(self):
        '''
        Yields the instance parameters (each a Variable or Iter of IndexedVars)
        of this OperationOverInstances and any instance parameters of nested
        OperationOverInstances.
        '''
        if hasattr(self, 'instance_params'):
            for ivar in self.instance_params:
                yield ivar
        else:
            yield self.instance_param
        if isinstance(self.instance_expr, self.__class__):
            for inner_ivar in self.instance_expr._all_instance_params():
                yield inner_ivar

    def all_instance_params(self):
        '''
        Returns all instance parameters (each a Variable or Iter of
        IndexedVars) of this OperationOverInstances
        and all instance parameters of nested OperationOverInstances.
        '''
        return list(self._all_instance_params())

    def _all_instance_vars(self):
        '''
        Yields the instance parameter variable of this OperationOverInstances
        and any instance parameter variables of nested OperationOverInstances
        of the same type.
        '''
        if hasattr(self, 'instance_vars'):
            for ivar in self.instance_vars:
                yield ivar
        else:
            yield self.instance_var
        if isinstance(self.instance_expr, self.__class__):
            for inner_ivar in self.instance_expr._all_instance_vars():
                yield inner_ivar

    def all_instance_vars(self):
        '''
        Returns all instance parameter variables of this OperationOverInstances
        and all instance parameters variables of nested OperationOverInstances.
        '''
        return list(self._all_instance_vars())

    def _all_domains(self):
        '''
        Yields the domain of this OperationOverInstances
        and any domains of nested OperationOVerInstances
        of the same type.  Some of these may be null.
        Modified by wdc on 6/17/2019, modifying generator fxn name
        from alldomains() to _alldomains() and adding a separate
        non-generator version of the alldomains() fxn below.
        '''
        if hasattr(self, 'domains'):
            for domain in self.domains:
                yield domain
        else:
            yield self.domain
            if isinstance(self.instance_expr, self.__class__):
                for domain in self.instance_expr.all_domains():
                    yield domain

    def all_domains(self):
        '''
        Returns all domains of this OperationOverInstances
        including domains of nested OperationOverInstances
        of the same type.
        '''
        return list(self._all_domains())

    def _all_conditions(self):
        '''
        Yields each condition of this OperationOverInstances
        and any conditions of nested OperationOverInstances
        of the same type.
        Modified by wdc on 6/06/2019, modifying generator fxn name
        from all_conditions() to _all_conditions() and adding a separate
        non-generator version of the all_conditions() fxn below.
        '''
        for condition in self.conditions:
            yield condition
        if isinstance(self.instance_expr, self.__class__):
            for condition in self.instance_expr.all_conditions():
                yield condition

    def all_conditions(self):
        '''
        Returns all conditions of this OperationOverInstances
        and all conditions of nested OperationOverInstances
        of the same type. Relies on the Python generator function
        _all_conditions() defined above.
        Added by wdc on 6/06/2019.
        '''
        return list(self._all_conditions())

    def explicit_instance_params(self):
        '''
        Return the instance parameters that are to be shown explicitly
        in the formatting (as opposed to being made implicit via
        conditions) joined together at this level according to the
        style. By default, this includes all of the instance parameters
        that are to be joined but this may be overridden to exclude
        implicit instance parameters.
        '''
        if hasattr(self, 'instance_params'):
            return self.instance_params.entries
        else:
            return [self.instance_param]

    def explicit_instance_vars(self):
        '''
        Return the instance parameter variables that are to be shown explicitly
        in the formatting (as opposed to being made implicit via conditions)
        joined together at this level according to the style. The behavior
        is determined by 'explicit_instance_params'.  Here, we simply extract
        the variables from the parameters that result from
        'explicit_instance_params'.
        '''
        return [get_param_var(parameter) for
                parameter in self.explicit_instance_params()]

    def explicit_domains(self):
        '''
        Return the domains of the instance variables as a tuple.
        '''
        if not self.has_domain():
            return tuple()
        if hasattr(self, 'domains'):
            return self.domains
        elif self.domain is not None:
            return (self.domain,)
        return tuple()  # No explicitly displayed domains

    def has_one_domain(self):
        '''
        Return True if and only if each instance parameter has
        the some explicit domain.
        '''
        if hasattr(self, 'domain'):
            return True
        return False

    def domain_conditions(self):
        '''
        Return the domain conditions of all instance variables that
        areg joined together at this level according to the style.
        '''
        if hasattr(self, 'domains'):
            assert (self.conditions.num_entries() >= 
                    len(self.domains)), (
                            'expecting a condition for each domain')
            for iparam, condition, domain in  \
                    zip(self.instance_params, self.conditions, self.domains):
                assert domain == _extract_domain_from_condition(
                    iparam, condition)
            return self.conditions[:len(self.domains)].entries
        else:
            explicit_domains = self.explicit_domains()
            if len(explicit_domains) == 0:
                return []  # no explicit domains
            domain_conditions = []
            assert (self.domain ==
                    _extract_domain_from_condition(self.instance_param,
                                                   self.conditions[0]))
            domain_conditions.append(self.conditions[0])
            return domain_conditions

    def explicit_conditions(self):
        '''
        Return the conditions that are to be shown explicitly in the formatting
        (after the "such that" symbol "|") at this level according to the
        style.  By default, this includes all of the 'joined' conditions except
        implicit 'domain' conditions.
        '''
        if hasattr(self, 'domains'):
            assert (self.conditions.num_entries() >= 
                    len(self.domains)), (
                            'expecting a condition for each domain')
            for iparam, condition, domain in zip(
                    self.instance_params, self.conditions, self.domains):
                cond_domain = _extract_domain_from_condition(iparam, condition)
                assert cond_domain == domain
            return self.conditions[len(self.domains):].entries  # skip the domains
        else:
            explicit_domains = self.explicit_domains()
            conditions = []
            if len(explicit_domains) == 0:
                conditions.extend(self.conditions.entries)
            else:
                cond_domain = _extract_domain_from_condition(
                    self.instance_param, self.conditions[0])
                assert cond_domain == self.domain
                conditions.extend(self.conditions[1:].entries)
            return conditions

    def _instance_param_lists(self):
        '''
        Yield lists of instance vars that include all of the instance
        paramaters (see all_instance_params method) but grouped together
        according to the style joining instance variables together.
        '''
        expr = self
        while isinstance(expr, self.__class__):
            if hasattr(expr, 'instance_params'):
                yield expr.instance_params  # grouped together
            else:
                yield [expr.instance_param]
            expr = expr.instance_expr

    def instance_param_lists(self):
        '''
        Returns lists of instance parameters that include all of the instance
        parameters (see all_instance_params method) but grouped together
        according to the style joining instance parameters together.
        '''
        return list(self._instance_param_lists())

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions
        options = StyleOptions(self)
        options.add_option(
            'with_wrapping',
            'Whether or not to wrap the Expression after the parameters, default is True')
        options.add_option(
            'wrap_params',
            'Wraps every two parameters AND wraps the Expression after the parameters, '
            'default is True')
        options.add_option(
            'justification',
            "justify to the 'left', 'center', or 'right' in the array cells")
        return options

    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    def with_wrapping(self, wrap=True):
        '''
        Wraps the 'instance_expr' onto the next line. For example
        \forall_{a, b, c, d, e, f, g}
        P(a, b, c, d, e, f, g)

        rather than
        \forall_{a, b, c, d, e, f, g} P(a, b, c, d, e, f, g)
        '''
        return self.with_styles(with_wrapping=str(wrap))

    def wrap_params(self, wrap=True):
        '''
        Wraps the parameters onto the multiple lines depending on
        how many parameters there are.   For example:
        \forall_{a, b, c,
                d, e, f, g} P(a, b, c, d, e, f, g)

        rather than
        \forall_{a, b, c, d, e, f, g} P(a, b, c, d, e, f, g)
        '''
        return self.with_styles(wrap_params=str(wrap))

    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)

    def _formatted(
            self,
            format_type,
            with_wrapping=None,
            wrap_params=None,
            justification=None,
            fence=False):
        '''
        Format the OperationOverInstances according to the style
        which may join nested operations of the same type.
        '''

        if with_wrapping is None:
            # style call to wrap the expression after the parameters
            with_wrapping = self.get_style('with_wrapping', 'False')
        if wrap_params is None:
            # style call to wrap the expression after the parameters
            wrap_params = self.get_style('wrap_params', 'False')
        if justification is None:
            justification = self.get_style('justification', 'center')
        # override this default as desired
        explicit_iparams = list(self.explicit_instance_params())
        explicit_conditions = ExprTuple(*self.explicit_conditions())
        explicit_domains = ExprTuple(*self.explicit_domains())
        instance_expr = self.instance_expr
        has_explicit_iparams = (len(explicit_iparams) > 0)
        has_explicit_conditions = (explicit_conditions.num_entries() > 0)
        has_multi_domain = not self.has_one_domain()
        domain_conditions = ExprTuple(*self.domain_conditions())
        out_str = ''
        formatted_params = ', '.join([param.formatted(format_type, abbrev=True)
                                      for param in explicit_iparams])
        if format_type == 'string':
            if fence:
                out_str += '['
            out_str += self.operator.formatted(format_type) + '_{'
            if has_explicit_iparams:
                if has_multi_domain:
                    out_str += domain_conditions.formatted(
                        format_type, operator_or_operators=',', fence=False)
                else:
                    out_str += formatted_params
            if not has_multi_domain and self.domain is not None:
                out_str += ' in '
                if has_multi_domain:
                    out_str += explicit_domains.formatted(
                        format_type, operator_or_operators='*', fence=False)
                else:
                    out_str += self.domain.formatted(format_type, fence=False)
            if has_explicit_conditions:
                if has_explicit_iparams:
                    out_str += " | "
                out_str += explicit_conditions.formatted(
                    format_type, fence=False)
                # out_str += ', '.join(condition.formatted(format_type) for condition in self.conditions
                # if condition not in implicit_conditions)
            out_str += '} ' + instance_expr.formatted(format_type, fence=True)
            if fence:
                out_str += ']'
        if format_type == 'latex':
            if fence:
                out_str += r'\left['
            if wrap_params == 'True':
                out_str += self.operator.formatted(
                    format_type) + r'_{ \scriptsize \begin{array}{' + justification[0] + '}' + '\n'
                if has_explicit_iparams:
                    if has_multi_domain:
                        out_str += self._wrap_params_formatted(
                            format_type=format_type,
                            params=domain_conditions,
                            operator_or_operators=',',
                            fence=False)
                    else:
                        out_str += self._wrap_params_formatted(
                            format_type=format_type, params=explicit_iparams, fence=False)
                if not has_multi_domain and self.domain is not None:
                    out_str += r' \in '
                    out_str += self.domain.formatted(format_type, fence=False)
                if has_explicit_conditions:
                    if has_explicit_iparams:
                        out_str += "~|~"
                    out_str += self._wrap_params_formatted(
                        format_type=format_type, params=explicit_conditions, fence=False)
                out_str += r'\end{array}' + '\n' + r'}~  \\' + '\n' + \
                    instance_expr.formatted(format_type, fence=True)
            else:
                out_str += self.operator.formatted(format_type) + r'_{'
                if has_explicit_iparams:
                    if has_multi_domain:
                        out_str += domain_conditions.formatted(
                            format_type, operator_or_operators=',', fence=False)
                    else:
                        out_str += formatted_params
                if not has_multi_domain and self.domain is not None:
                    out_str += r' \in '
                    out_str += self.domain.formatted(format_type, fence=False)
                if has_explicit_conditions:
                    if has_explicit_iparams:
                        out_str += "~|~"
                    out_str += explicit_conditions.formatted(
                        format_type, fence=False)
                # out_str += ', '.join(condition.formatted(format_type) for condition in self.conditions
                # if condition not in implicit_conditions)
                if with_wrapping == 'True':
                    print(instance_expr.formatted(format_type, fence=True))
                    out_str += r'}~ ' + \
                        instance_expr.formatted(format_type, fence=True)
                else:
                    out_str += '}~' + \
                        instance_expr.formatted(format_type, fence=True)
            if fence:
                out_str += r'\right]'
        # print(out_str)
        return out_str

    def _wrap_params_formatted(
            self,
            format_type,
            params,
            fence,
            operator_or_operators=None):
        '''
        Wraps the list of parameters depending on the type.
        '''
        out_str = ''
        cap = 70
        # the average length of a range of ranges and a range
        count = 0
        if isinstance(params, list):
            for i, entry in enumerate(params):
                if count > cap:
                    count = 0
                    out_str += r'\\' + '\n'
                if i == len(params) - 1:
                    out_str += entry.formatted(format_type, fence=fence)
                else:
                    out_str += entry.formatted(format_type, fence=fence) + ', '
                count += len(entry.formatted(format_type, fence=fence))
        elif isinstance(params, ExprTuple):
            for entry in params.entries:
                if count > cap:
                    count = 0
                    out_str += r'\\' + '\n'
                if operator_or_operators is not None:
                    out_str += entry.formatted(format_type,
                                               operator_or_operators=operator_or_operators,
                                               fence=fence)
                    count += len(entry.formatted(format_type,
                                                 operator_or_operators=operator_or_operators,
                                                 fence=fence))
                else:
                    out_str += entry.formatted(format_type, fence=fence)
                    count += len(entry.formatted(format_type, fence=fence))
        return out_str

    """
    def instance_substitution(self, universality, assumptions=USE_DEFAULTS):
        '''
        Equate this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..),
        with one that substitutes instance expressions given some
        universality = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Derive and return the following type of equality assuming universality:
        Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..) = Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        from proveit.logic.equality import instance_substitution, no_domain_instance_substitution
        from proveit.logic import Forall, Equals
        from proveit import Judgment
        from proveit import n, Qmulti, x_multi, y_multi, z_multi, f, g, Upsilon, S
        if isinstance(universality, Judgment):
            universality = universality.expr
        if not isinstance(universality, Forall):
            raise InstanceSubstitutionException("'universality' must be a forall expression", self, universality)
        if len(universality.instance_vars) != len(self.instance_vars):
            raise InstanceSubstitutionException("'universality' must have the same number of variables as the OperationOverInstances having instances substituted", self, universality)
        if universality.domain != self.domain:
            raise InstanceSubstitutionException("'universality' must have the same domain as the OperationOverInstances having instances substituted", self, universality)
        # map from the forall instance variables to self's instance variables
        i_var_substitutions = {forall_ivar:self_ivar for forall_ivar, self_ivar in zip(universality.instance_vars, self.instance_vars)}
        if universality.conditions.substituted(i_var_substitutions) != self.conditions:
            raise InstanceSubstitutionException("'universality' must have the same conditions as the OperationOverInstances having instances substituted", self, universality)
        if not isinstance(universality.instance_expr, Equals):
            raise InstanceSubstitutionException("'universality' must be an equivalence within Forall: " + str(universality))
        if universality.instance_expr.lhs.substituted(i_var_substitutions) != self.instance_expr:
            raise InstanceSubstitutionException("lhs of equivalence in 'universality' must match the instance expression of the OperationOverInstances having instances substituted", self, universality)
        f_op, f_op_sub = Operation(f, self.instance_vars), self.instance_expr
        g_op, g_op_sub = Operation(g, self.instance_vars), universality.instance_expr.rhs.substituted(i_var_substitutions)
        Q_op, Q_op_sub = Operation(Qmulti, self.instance_vars), self.conditions
        if self.has_domain():
            return instance_substitution.instantiate({Upsilon:self.operator, Q_op:Q_op_sub, S:self.domain, f_op:f_op_sub, g_op:g_op_sub},
                                                    relabel_map={x_multi:universality.instance_vars, y_multi:self.instance_vars, z_multi:self.instance_vars}, assumptions=assumptions).derive_consequent(assumptions=assumptions)
        else:
            return no_domain_instance_substitution.instantiate({Upsilon:self.operator, Q_op:Q_op_sub, f_op:f_op_sub, g_op:g_op_sub},
                                                             relabel_map={x_multi:universality.instance_vars, y_multi:self.instance_vars, z_multi:self.instance_vars}, assumptions=assumptions).derive_consequent(assumptions=assumptions)

    def substitute_instances(self, universality, assumptions=USE_DEFAULTS):
        '''
        Assuming this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..)
        to be a true statement, derive and return Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        given some 'universality' = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        substitution = self.instance_substitution(universality, assumptions=assumptions)
        return substitution.derive_right_via_equality(assumptions=assumptions)
    """


def bundle(expr, bundle_thm, num_levels=2, *, assumptions=USE_DEFAULTS):
    '''
    Given a nested OperationOverInstances, derive or equate an
    equivalent form in which a given number of nested levels is
    bundled together.  Use the given theorem specific to the particular
    OperationOverInstances.

    For example,
        \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
    can become
        \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
    via bundle with num_levels=2.

    For example of the form of the theorem required, see
    proveit.logic.booleans.quantification.bundling or
    proveit.logic.booleans.quantification.bundling_equality.
    '''
    from proveit.relation import TransRelUpdater
    from proveit.logic import Implies, Equals
    # Make a TransRelUpdater only if the bundle_thm yield an
    # equation, in which case we'll want the result to be an equation.
    eq = None
    bundled = expr
    while num_levels >= 2:
        if (not isinstance(bundled, OperationOverInstances) or
                not isinstance(bundled.instance_expr, OperationOverInstances)):
            raise ValueError(
                "May only 'bundle' nested OperationOverInstances, "
                "not %s" %
                bundled)
        _m = bundled.instance_params.num_elements()
        _n = bundled.instance_expr.instance_params.num_elements()
        _P = bundled.instance_expr.instance_expr
        _Q = bundled.effective_condition()
        _R = bundled.instance_expr.effective_condition()
        m, n = bundle_thm.instance_vars
        P, Q, R = bundle_thm.instance_expr.instance_vars
        correspondence = bundle_thm.instance_expr.instance_expr
        if isinstance(correspondence, Implies):
            if (not isinstance(correspondence.antecedent,
                               OperationOverInstances) or not 
                    correspondence.consequent.instance_params.num_entries() == 2):
                raise ValueError("'bundle_thm', %s, does not have the "
                                 "expected form with the bundled form as "
                                 "the consequent of the implication, %s"
                                 % (bundle_thm, correspondence))
            x_1_to_m, y_1_to_n = correspondence.consequent.instance_params
        elif isinstance(correspondence, Equals):
            if not isinstance(
                correspondence.rhs, OperationOverInstances or not 
                    correspondence.antecedent.instance_params.num_entries() == 2):
                raise ValueError("'bundle_thm', %s, does not have the "
                                 "expected form with the bundled form on "
                                 "right of the an equality, %s"
                                 % (bundle_thm, correspondence))
            x_1_to_m, y_1_to_n = correspondence.rhs.instance_params

        all_params = bundled.instance_params + bundled.instance_expr.instance_params
        Pxy = Function(P, all_params)
        Qx = Function(Q, bundled.instance_params)
        Rxy = Function(R, all_params)
        x_1_to_m = x_1_to_m.replaced({m: _m})
        y_1_to_n = y_1_to_n.replaced({n: _n})
        instantiation = bundle_thm.instantiate(
            {m: _m, n: _n, ExprTuple(x_1_to_m): bundled.instance_params,
             ExprTuple(y_1_to_n): bundled.instance_expr.instance_params,
             Pxy: _P, Qx: _Q, Rxy: _R}, assumptions=assumptions)
        if isinstance(instantiation.expr, Implies):
            bundled = instantiation.derive_consequent()
        elif isinstance(instantiation.expr, Equals):
            if eq is None:
                eq = TransRelUpdater(bundled)
            try:
                bundled = eq.update(instantiation)
            except ValueError:
                raise ValueError(
                    "Instantiation of bundle_thm %s is %s but "
                    "should match %s on one side of the equation."
                    % (bundle_thm, instantiation, bundled))
        else:
            raise ValueError("Instantiation of bundle_thm %s is %s but "
                             "should be an Implies or Equals expression."
                             % (bundle_thm, instantiation))
        num_levels -= 1
    if eq is None:
        # Return the bundled result.
        return bundled
    else:
        # Return the equality between the original expression and
        # the bundled result.
        return eq.relation


def unbundle(expr, unbundle_thm, num_param_entries=(1,), *,
             assumptions=USE_DEFAULTS):
    '''
    Given a nested OperationOverInstances, derive or equate an
    equivalent form in which the parameter entries are split in
    number according to 'num_param_entries'.  Use the given theorem
    specific to the particular OperationOverInstances.

    For example,
        \forall_{x, y, z | Q(x, y), R(z)} P(x, y, z)
    can become
        \forall_{x, y | Q(x, y)} \forall_{z | R(z)} P(x, y, z)
    via bundle with num_param_entries=(2, 1) or
    num_param_entries=(2,) -- the last number can be implied
    by the remaining number of parameters.

    For example of the form of the theorem required, see
    proveit.logic.booleans.quantification.unbundling or
    proveit.logic.booleans.quantification.bundling_equality.
    '''
    from proveit.relation import TransRelUpdater
    from proveit.logic import Implies, Equals, And
    # Make a TransRelUpdater only if the bundle_thm yield an
    # equation, in which case we'll want the result to be an equation.
    eq = None
    unbundled = expr
    net_indicated_param_entries = sum(num_param_entries)
    num_actual_param_entries = expr.instance_params.num_entries()
    for n in num_param_entries:
        if not isinstance(n, int) or n <= 0:
            raise ValueError(
                "Each of 'num_param_entries', must be an "
                "integer greater than 0.  %s fails this requirement."
                % (num_param_entries))
    if net_indicated_param_entries > num_actual_param_entries:
        raise ValueError("Sum of 'num_param_entries', %s=%d should not "
                         "be greater than the number of parameter entries "
                         "of %s for unbundling."
                         % (num_param_entries, net_indicated_param_entries,
                            expr))
    if net_indicated_param_entries < num_actual_param_entries:
        diff = num_actual_param_entries - net_indicated_param_entries
        num_param_entries = list(num_param_entries) + [diff]
    else:
        num_param_entries = list(num_param_entries)
    while len(num_param_entries) > 1:
        n_last_entries = num_param_entries.pop(-1)
        first_params = ExprTuple(*unbundled.instance_params[:-n_last_entries])
        first_param_vars = {get_param_var(param) for param in first_params}
        remaining_params = \
            ExprTuple(*unbundled.instance_params[-n_last_entries:])
        _m = first_params.num_elements()
        _n = remaining_params.num_elements()
        _P = unbundled.instance_expr
        # Split up the conditions between the outer
        # OperationOverInstances and inner OperationOverInstances
        condition = unbundled.effective_condition()
        if isinstance(condition, And):
            _nQ = 0
            for cond in condition.operands:
                cond_vars = free_vars(cond, err_inclusively=True)
                if first_param_vars.isdisjoint(cond_vars):
                    break
                _nQ += 1
            if _nQ == 0:
                _Q = And()
            elif _nQ == 1:
                _Q = condition.operands[0]
            else:
                _Q = And(*condition.operands[:_nQ])
            _nR = condition.operands.num_entries() - _nQ
            if _nR == 0:
                _R = And()
            elif _nR == 1:
                _R = condition.operands[-1]
            else:
                _R = And(*condition.operands[_nQ:])
        elif first_param_vars.isdisjoint(free_vars(condition,
                                                   err_inclusively=True)):
            _Q = condition
            _R = And()
        else:
            _Q = And()
            _R = condition
        m, n = unbundle_thm.instance_vars
        P, Q, R = unbundle_thm.instance_expr.instance_vars
        correspondence = unbundle_thm.instance_expr.instance_expr
        if isinstance(correspondence, Implies):
            if (not isinstance(correspondence.antecedent,
                               OperationOverInstances) or not 
                    correspondence.antecedent.instance_params.num_entries() == 2):
                raise ValueError("'unbundle_thm', %s, does not have the "
                                 "expected form with the bundled form as "
                                 "the antecedent of the implication, %s"
                                 % (unbundle_thm, correspondence))
            x_1_to_m, y_1_to_n = correspondence.antecedent.instance_params
        elif isinstance(correspondence, Equals):
            if not isinstance(
                correspondence.rhs, OperationOverInstances or not 
                    correspondence.antecedent.instance_params.num_entries() == 2):
                raise ValueError("'unbundle_thm', %s, does not have the "
                                 "expected form with the bundled form on "
                                 "right of the an equality, %s"
                                 % (unbundle_thm, correspondence))
            x_1_to_m, y_1_to_n = correspondence.rhs.instance_params
        else:
            raise ValueError("'unbundle_thm', %s, does not have the expected "
                             "form with an equality or implication  "
                             "correspondence, %s"
                             % (unbundle_thm, correspondence))

        Qx = Function(Q, first_params)
        Rxy = Function(R, unbundled.instance_params)
        Pxy = Function(P, unbundled.instance_params)
        x_1_to_m = x_1_to_m.replaced({m: _m})
        y_1_to_n = y_1_to_n.replaced({n: _n})
        instantiation = unbundle_thm.instantiate(
            {m: _m, n: _n, ExprTuple(x_1_to_m): first_params,
             ExprTuple(y_1_to_n): remaining_params,
             Pxy: _P, Qx: _Q, Rxy: _R}, assumptions=assumptions)
        if isinstance(instantiation.expr, Implies):
            unbundled = instantiation.derive_consequent()
        elif isinstance(instantiation.expr, Equals):
            if eq is None:
                eq = TransRelUpdater(unbundled)
            try:
                unbundled = eq.update(instantiation)
            except ValueError:
                raise ValueError(
                    "Instantiation of bundle_thm %s is %s but "
                    "should match %s on one side of the equation."
                    % (unbundle_thm, instantiation, unbundled))
        else:
            raise ValueError("Instantiation of bundle_thm %s is %s but "
                             "should be an Implies or Equals expression."
                             % (unbundle_thm, instantiation))
    if eq is None:
        # Return the unbundled result.
        return unbundled
    else:
        # Return the equality between the original expression and
        # the unbundled result.
        return eq.relation


class InstanceSubstitutionException(Exception):
    def __init__(self, msg, operation_over_instances, universality):
        self.msg = msg
        self.operation_over_instances = operation_over_instances
        self.universality = universality

    def __str__(self):
        return self.msg + '.\n  operation_over_instances: ' + \
            str(self.operation_over_instances) + '\n  universality: ' + str(self.universality)

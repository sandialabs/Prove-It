import inspect
from proveit._core_.defaults import defaults
from proveit._core_.expression.expr import (
    Expression, MakeNotImplemented, free_vars)
from proveit._core_.expression.label.var import Variable
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda, get_param_var
from proveit._core_.expression.composite import (
    ExprTuple, is_single, single_or_composite_expression, 
    composite_expression, ExprRange)
from proveit._core_.expression.conditional import Conditional
from proveit.decorators import prover, equality_prover
from .operation import Operation, OperationError
from .function import Function


def _extract_domain_from_condition(ivar, condition):
    '''
    Given a "domain" condition (e.g., "x in S" or "(x_1 in S), ..., (x_n in S)")
    return the domain (e.g., "S").  Return None if the condition is not
    a "domain" condition for the given instance variable(s).
    '''
    from proveit.logic import InClass
    if isinstance(ivar, ExprRange):
        # See if the condition is a range of domain conditions
        # matching the instance variable range.
        # For example, x_1, ..., x_n as the instance variable
        # range matching x_1 in S_1, ..., x_n in S_n.
        if (isinstance(condition, ExprRange)
                and isinstance(condition.body, InClass)
                and condition.true_start_index == ivar.true_start_index
                and condition.true_end_index == ivar.true_end_index):
            # Replace the condition parameter with the ivar parameter
            # and see if the InSet element matches ivar.body.
            cond_body_elem_with_repl_param = (
                    condition.body.element.basic_replaced(
                            {condition.parameter: ivar.parameter}))
            if cond_body_elem_with_repl_param == ivar.body:
                if condition.parameter in free_vars(condition.body.domain):
                    # There is a range of domains matching a range of
                    # parameters.
                    return ExprRange(
                        condition.parameter, condition.body.domain,
                        condition.true_start_index, condition.true_end_index)
            return condition.body.domain
    elif isinstance(condition, InClass) and condition.element == ivar:
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
        'condition': 'condition',
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
        OperationOverInstances is effected as an Operation over a Lambda map.
        
        Conditions are handled differently for different kinds of operations
        and is effected as a style option.  For forall and exists, the 
        conditions are effected, respectively, via implication or conjunction;
        for example, forall_{x | Q(x)} P(x) is a style for 
        forall_{x} [Q(x) ⇒ P(x)]. exists_{x | Q(x)} P(x) is a style for
        exists_{x} [Q(x) ∧ P(x)].  For summation, its effected via a
        ConditionalSet with a default of zero.  These choices are made for
        convenience.  We could have chosen to use ConditionalSets for all of
        these, but implication and conjunction are more convenient condition
        implementations for universal and existential quantifiers.

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
        from proveit.logic import InSet, InClass
        from proveit._core_.expression.lambda_expr.lambda_expr import get_param_var
        if _lambda_map is not None:
            # Use the provided 'lambda_map' instead of creating one.
            from proveit.logic import And
            lambda_map = _lambda_map
            instance_params = lambda_map.parameters
            condition, instance_expr = (
                self.__class__._extract_condition_and_instance_expr(
                    lambda_map.body))
            if condition is not None:
                # Has conditions.
                if (isinstance(condition, And) and
                        not is_single(condition.operands)):
                    conditions = composite_expression(condition.operands)
                else:
                    conditions = composite_expression(condition)
            else:
                # No conditions.
                instance_expr = lambda_map.body
                conditions = ExprTuple()
        else:
            instance_params = composite_expression(instance_param_or_params)
            if domains is not None:
                # Some initial checks regarding domain specifications
                if len(domains) != instance_params.num_entries():
                    raise ValueError(
                        "When specifying multiple domains, the number "
                        "should be the same as the number of instance "
                        "variables.")
                if domain is not None:
                    raise ValueError(
                        "Provide a single domain or multiple domains, "
                        "not both")
            if condition is not None and conditions is not None:
                raise ValueError("Cannot specify both 'conditions' and "
                                 "'condition'")
            
            auto_nest_multi_params = self.auto_nest_multi_params()
            if auto_nest_multi_params and instance_params.num_entries() > 1:
                # Make a nested Operation and use the nesting='bundled' style.
                assert _lambda_map is None, ("Not expected '_lambda_map' with "
                                             "'instance_params_or_params'")
                kwargs = {arg_name:locals()[var_name] for arg_name, var_name 
                          in self.__class__._init_argname_mapping_.items()
                          if var_name != 'instance_param_or_params'}
                inner_instance_params = instance_params[1:]
                inner_instance_vars = [get_param_var(param) for param in
                                       inner_instance_params]
                if domain is None and domains is not None:
                    kwargs['domains'] = domains[1:]
                    domain, domains = domains[0], None
                if conditions is not None:
                    # Put conditions on the outer layer where possible.
                    outer_conditions, inner_conditions = [], []
                    if isinstance(conditions, ExprRange):
                        conditions = ExprTuple(conditions)
                    for _cond in conditions:
                        if free_vars(_cond).isdisjoint(inner_instance_vars):
                            outer_conditions.append(_cond)
                        else:
                            inner_conditions.append(_cond)
                    kwargs['conditions'] = inner_conditions
                    conditions = outer_conditions
                nested_operation = self.__class__(
                    inner_instance_params, **kwargs, styles=styles)
                if styles is None: styles = dict()
                styles['nesting'] = 'bundled'
                instance_expr = nested_operation
                instance_param_or_params = instance_params[0]
                instance_params = composite_expression(instance_param_or_params)
                condition = None # handled by nested operation

            if instance_params.num_entries() == 0:
                raise ValueError(
                    "Expecting at least one instance parameter when "
                    "constructing an OperationOverInstances")

            auto_nested_range_of_parameters = False
            if auto_nest_multi_params and isinstance(instance_params[0], ExprRange):
                # When using auto_nest_multi_params, take an ExprRange of
                # parameters to be a single parameter as a function with
                # the start/end indices represented in style options.
                param_range = instance_params[0]
                start_indices = param_range.start_indices()
                end_indices = param_range.end_indices()
                if len(start_indices) == 1:
                    assert len(end_indices) == 1
                    _start, _end = start_indices[0], end_indices[0]
                else:
                    _start = ExprTuple(start_indices)
                    _end = ExprTuple(end_indices)
                if styles is None: styles = dict()
                styles['param_range_start'] = _start
                styles['param_range_end'] = _end
                auto_nested_range_of_parameters = True
            
            # We will need to generate the Lambda sub-expression.
            # Do some initial preparations w.r.t. instance_params, domain(s), and
            # conditions.
            
            if condition is not None:
                assert conditions is None, "should have been checked above"
                conditions = (condition,)
            elif conditions is None:
                conditions = tuple()
            elif isinstance(conditions, ExprTuple):
                conditions = conditions.entries            
            
            # Add appropriate conditions for the domains:
            if domain is not None:
                # prepend domain conditions
                assert domains is None, "should have been checked above"
                if not isinstance(domain, Expression):
                    raise TypeError(
                        "The domain should be an 'Expression' type")
                domains = [domain] * instance_params.num_entries()

            if domains is not None:
                # Prepend domain conditions.  Note that although we start with
                # all domain conditions at the beginning,
                # some may later get pushed back as "inner conditions"
                # (see below),
                assert len(domains) == instance_params.num_entries(), (
                    "should have been checked above")
                domain_conditions = []
                for iparam, domain in zip(instance_params, domains):
                    if domain is None: continue # skip domains of None
                    # If the domain is a proper class, indicated via
                    # an 'is_proper_class' attribute, use InClass
                    # instead of InSet.
                    if (hasattr(domain, 'is_proper_class')
                            and domain.is_proper_class):
                        in_class = InClass
                    else:
                        in_class = InSet
                    if isinstance(iparam, ExprRange):
                        if isinstance(domain, ExprRange):
                            if ((iparam.true_start_index != domain.true_start_index) or
                                    (iparam.true_end_index != domain.true_end_index)):
                                raise ValueError(
                                    "A range of parameters must match "
                                    "in start and end indices with the "
                                    "corresponding range of domains: "
                                    "%s vs %s and %s vs %s" %
                                    (iparam.true_start_index,
                                     domain.true_start_index,
                                     iparam.true_end_index, domain.true_end_index))
                            # Use the same parameter for the domain
                            # as the instance parameter.
                            domain_body_with_new_param = \
                                domain.body.basic_replaced(
                                        {domain.parameter: iparam.parameter})
                            condition = ExprRange(
                                iparam.parameter,
                                in_class(iparam.body, domain_body_with_new_param),
                                iparam.true_start_index, iparam.true_end_index)
                        else:
                            condition = ExprRange(
                                iparam.parameter, 
                                in_class(iparam.body, domain),
                                iparam.true_start_index, iparam.true_end_index)
                    else:
                        condition = in_class(iparam, domain)
                    domain_conditions.append(condition)
                conditions = domain_conditions + list(conditions)
            conditions = composite_expression(conditions)
            
            if auto_nested_range_of_parameters:
                instance_params = ExprTuple(get_param_var(param_range))

        if _lambda_map is None:
            # Now do the actual lambda_map creation
            if instance_params.num_entries() == 1:
                instance_param_or_params = instance_params[0]
            # Generate the Lambda sub-expression.
            lambda_map = self.__class__._create_operand(
                instance_param_or_params, instance_expr, conditions)

        self._instance_params = tuple(instance_params)
        if (instance_params.num_entries() > 1 or
                isinstance(instance_params[0], ExprRange)):
            '''Instance parameters of the OperationOverInstance.'''
            self._instance_vars = tuple([get_param_var(parameter) for
                                         parameter in instance_params])
            """
            '''Instance parameter variables of the OperationOverInstance.'''
            if domains is not None:
                # Domain for each instance variable
                self._domains = domains
                '''Domains of the instance parameters (may be None)'''
                n_domains = len(self._domains)
                if (not any(isinstance(entry, ExprRange) for entry
                            in self._domains)
                        and self._domains == tuple([self._domains[0]] * n_domains)):
                    # Multiple domains that are all the same.
                    self._domain = self._domains[0]
            """
        else:
            self._instance_param = instance_params[0]
            '''Outermost instance parameter of the OperationOverInstance.'''
            self._instance_var = get_param_var(self._instance_param)
            """
            '''Outermost instance parameter variable of the OperationOverInstance.'''
            if domains is not None:
                self._domain = domains[0]
            '''Domain of the outermost instance parameter (may be None)'''
            """

        _condition, _inst_expr = (
            self.__class__._extract_condition_and_instance_expr(lambda_map.body))
        
        self._instance_expr = _inst_expr

        if _condition is not None:
            self._condition = _condition
            if _lambda_map is None and len(conditions)==0:
                # Don't display as a compact condition since there
                # was no given 'domain' or 'condition', just an instance_expr
                # that happens to be in the form of a condition
                # (e.g., an Implies in the case of Forall).
                styles = dict() if styles is None else dict(styles)
                styles['condition'] = 'expanded'
                # We need this in case of a 'condition':'compact' switch:
                conditions = ExprTuple(_condition)
        self._conditions = conditions
        '''Conditions applicable to the outermost instance variable (or iteration of indexed variables) of the OperationOverInstance.  May include an implicit 'domain' condition.'''

        Operation.__init__(self, operator, [lambda_map], styles=styles)

    @classmethod
    def auto_nest_multi_params(cls):
        '''
        For OperationOverInstance classes for which 'auto_nest_multi_params'
        is True and there are multiple parameter entries, put parameter 
        entries into multiple, nested operation occurrences and set the 
        nesting='bundled' style . Also, if there are mutliple parameters in 
        ExprRange(s), place the start/end indices as muliparam_start and 
        multipparam_end style options and just use the single Variable as the 
        internally used parameter, acting as a function parameter where the 
        index/indices are arguments to the function.
        THIS FEATURE WAS INTENDED FOR UNIVERSAL AND EXISTENTIAL QUANTIFICATION
        BUT WE DECIDED AGAINST IT AND MAY NOW BE MOOT BUT REMAINS AS AN OPTION
        IN CASE WE WANT TO MAKE USE OF IT IN THE FUTURE.
        '''
        return False

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        OperationOverInstances class is to include appropriate
        'wrapping', 'justification', 'condition', 'nesting',
        'wrap_param_positions', 'param_justification', 'suchthat_wrapping', 
        'suchthat_justification', 'wrap_condition_positions', and
        'condition_justification', calls.
        '''
        with_wrapping = (self.get_style('with_wrapping', 'False') == 'True')
        justification = self.get_style('justification', 'center')
        condition_style = self.get_style('condition', 'compact')
        nesting_style = self.get_style('nesting', 'unbundled')
        wrap_param_positions = self.wrap_param_positions()
        param_justification = self.get_style('param_justification', 'left')
        suchthat_wrapping = self.get_style('suchthat_wrapping', 'No')
        suchthat_justification = self.get_style('suchthat_justification', 'left')
        wrap_condition_positions = self.wrap_condition_positions()
        condition_justification = self.get_style('condition_justification', 'left')
        call_strs = []
        if with_wrapping:
            call_strs.append('with_wrapping()')
        if justification != 'center':
            call_strs.append('with_justification("' + justification + '")')
        if condition_style == 'expanded':
            call_strs.append('with_expanded_condition()')      
        if nesting_style == 'bundled':
            call_strs.append('with_bundled_nesting()')      
        if len(wrap_param_positions) > 0:
            call_strs.append('with_param_wrapping_at(' + ','.join(
                str(pos) for pos in wrap_param_positions) + ')')
        if param_justification != 'left':
            call_strs.append('with_param_justification("' + 
                             param_justification + '")')
        if suchthat_wrapping == 'before':
            call_strs.append('with_wrap_before_suchthat()')
        elif suchthat_wrapping == 'after':
            call_strs.append('with_wrap_after_suchthat()')            
        if suchthat_justification != 'left':
            call_strs.append('with_suchthat_justification("' + 
                             condition_justification + '")')
        if len(wrap_condition_positions) > 0:
            call_strs.append('with_condition_wrapping_at(' + ','.join(
                str(pos) for pos in wrap_condition_positions) + ')')
        if param_justification != 'left':
            call_strs.append('with_condition_justification("' + 
                             param_justification + '")')
        return call_strs

    @classmethod
    def _create_operand(cls, instance_param_or_params, instance_expr, conditions):
        if conditions.num_entries() == 0:
            return Lambda(instance_param_or_params, instance_expr)
        else:
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
        # Return the instance expression that includes the condition
        # explicitly (e.g., a ConditionalSet, implication in the case of
        # forall, conjunction in the case of exists).
        if cls is OperationOverInstances:
            if condition is not None:
                raise ValueError("Cannot create a generic OperationOverInstances"
                                 " with a condition")
            return instance_expr
        raise NotImplementedError("_create_conditioned_instance_expr must be "
                                  "implemented for %s"%cls)
        
    @classmethod
    def _extract_condition_and_instance_expr(cls, lambda_body):
        # Given the lambda body, return the condition and instance_expr
        # (independent of the condition) as a tuple pair.
        if cls is OperationOverInstances:
            return None, lambda_body
        raise NotImplementedError("_extract_condition_and_instance_expr must be "
                                  "implemented for %s"%cls)

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
            return self.instance_param_or_params
        elif arg_name == 'instance_expr':
            # return the inner instance expression after joining the
            # instance variables according to the style
            return self.instance_expr
        elif arg_name == 'domain' or arg_name == 'domains':
            # return the proper single domain or list of domains
            domains = OperationOverInstances.explicit_domains(self)
            if (not hasattr(self, 'domain') or 
                    domains != tuple([self.domain] * len(domains))):
                if arg_name == 'domains' and len(domains) > 0:
                    return domains
                else:
                    return None
            if self.domain is None:
                return None
            return self.domain if arg_name == 'domain' else None
        elif arg_name == 'condition' or arg_name == 'conditions':
            # return the joined conditions excluding domain conditions
            conditions = composite_expression(
                OperationOverInstances.non_domain_conditions(self))
            if conditions.num_entries() == 1 and arg_name == 'condition':
                return conditions[0]
            elif conditions.num_entries() > 1 and arg_name == 'conditions':
                return conditions
            return None

    @classmethod
    def _make(cls, core_info, sub_expressions, *, styles):
        if len(core_info) != 1 or core_info[0] != 'Operation':
            raise ValueError(
                "Expecting Operation core_info to contain exactly one item: 'Operation'")
        if len(sub_expressions) != 2:
            raise ValueError("Expecting exactly two sub_expressions for an "
                             "OperationOverInstances object: an operator and "
                             "operands with a single lambda_map entry.")

        implicit_operator = cls._implicit_operator()
        operator = sub_expressions[0]
        operands = sub_expressions[1]
        
        if (not isinstance(operands, ExprTuple) or 
                not len(operands.entries) == 1):
            raise ValueError("Expecting operands to have a single entry.")

        if isinstance(operands[0], Variable) and hasattr(cls, '_operator_'):
            # If the operand is not a Variable, make an
            # Operation instead.  This can come up when creating
            # an InnerExpr replacement map when the inner expression
            # the the operand of an OperationOverInstances.
            return Function(cls._operator_, operands, styles=styles)
            
        lambda_map = operands[0]
        if not isinstance(lambda_map, Lambda):
            # If the operand isn't a Lambda, use Operation._make
            # and create a gerneric function-style operation.
            return Operation._make(core_info, sub_expressions,
                                   styles=styles)
        
        if implicit_operator is None or operator != implicit_operator:
            # If there is no implicit operator for the class or
            # the operator is no longer that implicit operator, make
            # a generic OperationOverInstance.
            return OperationOverInstances(
                    operator, None, None, 
                    styles=styles, _lambda_map=lambda_map)
        
        sig = inspect.signature(cls.__init__)
        Parameter = inspect.Parameter
        if ('_lambda_map' not in sig.parameters or
                sig.parameters['_lambda_map'].kind != Parameter.KEYWORD_ONLY):
            raise OperationError(
                "'_lambda_map' must be a keyword only argument "
                "for a constructor of a class %s derived from "
                "OperationOverInstances." %
                str(cls))

        npositional = 0
        for param in sig.parameters.values():
            if param.kind in (Parameter.POSITIONAL_ONLY, 
                              Parameter.POSITIONAL_OR_KEYWORD):
                npositional += 1
        npositional -= 1 # exclude 'self'
        made_operation = cls(
            *[None] * npositional,
            styles=styles, _lambda_map=lambda_map)
        return made_operation

    def _build_canonical_form(self):
        '''
        Build the canonical form of this OperationOverInstances.
        This override Expression._build_canonical_form to make
        sure that the domain conditions are kept in their proper place.
        '''
        from proveit.logic import InClass
        canonical_operator = self.operator.canonical_form()
        assert self.operands.num_entries()==1
        lambda_map = self.operands[0]
        instance_expr = self.instance_expr
        condition = self.condition if hasattr(self, 'condition') else None
        if condition is None:
            # If there are not conditions, there is nothing special
            # to worry about.
            return Operation._build_canonical_form(self)
        # parameters should be unchanged:
        parameters = lambda_map.parameters
        # Keep the domain conditions in their proper place.
        # For domain conditions, just use the canonical form
        # for the domain.
        def processed_domain_cond(domain_cond):
            assert isinstance(domain_cond, InClass)
            return type(domain_cond)(
                    domain_cond.element,
                    domain_cond.domain.canonical_form())
        if len(parameters)==1:
            # Designed to work when using 'auto_nest_multi_params'.
            if hasattr(self, 'domains') and self.domains[0] is not None:
                domain_conditions = ExprTuple(next(iter(self.domain_conditions())))
                domain_conditions = domain_conditions.map_elements(
                    processed_domain_cond)
                non_domain_conditions = self._conditions[1:]
            else:
                domain_conditions = tuple()
                non_domain_conditions = self._conditions
        else:
            assert not self.auto_nest_multi_params()
            domain_conditions = ExprTuple(*self.domain_conditions()).map_elements(
                processed_domain_cond)
            non_domain_conditions = self.non_domain_conditions()
        if len(domain_conditions) > 0:
            non_domain_conditions = sorted(
                (_cond.canonical_form() for _cond in non_domain_conditions),
                key=hash)
            canonical_conditions = ExprTuple(*domain_conditions,
                                             *non_domain_conditions)
            canonical_instance_expr = instance_expr.canonical_form()
            canonical_lambda = self.__class__._create_operand(
                    parameters, canonical_instance_expr,
                    canonical_conditions)
        else:
            canonical_lambda = lambda_map.canonical_form()
        if canonical_operator==self.operands and canonical_lambda==lambda_map:
            return self # No change.
        return self._checked_make(
                self._core_info, (canonical_operator, 
                                  ExprTuple(canonical_lambda)),
                style_preferences=self._style_data.styles)

    def _is_properly_nested(self, *, must_be_bundled):
        '''
        Return True if this is a nested operation is of the same type and
        must_be_bundled is False or the nesting syle is 'bundled'.
        '''
        if self.get_style('condition', 'compact') == 'expanded':
            # With an expanded condition, it isn't properly nested.
            return False
        return type(self._instance_expr) == type(self) and (
            not must_be_bundled or 
            self.get_style('nesting', 'unbundled') == 'bundled')

    def _is_bundled(self):
        '''
        Return True if this is a nested operation is of the same type and
        the nesting syle is 'bundled'.
        '''
        return self._is_properly_nested(must_be_bundled=True)

    @property
    def instance_param(self):
        '''
        Return a single, unbunded instance parameter if applicable
        or raise an AttributeError.
        '''
        if hasattr(self, '_instance_param') and not self._is_bundled() and (
                self.get_style('param_range_start', None) is None and
                self.get_style('param_range_end', None) is None):
            return self._instance_param
        raise AttributeError("No single 'instance_param'")

    def _effective_instance_param_entries(self, *, include_nested_only_if_bundled):
        '''
        Yield all bundled instance parameter entries.
        '''
        from proveit._core_.expression.composite.expr_range import var_range
        if hasattr(self, '_instance_param'):
            param_range_start = self.get_style('param_range_start', None)
            param_range_end = self.get_style('param_range_end', None)
            if param_range_start is None and param_range_end is None:
                yield self._instance_param
            else:
                # yield a multi-parameter in an ExprRange
                yield var_range(self._instance_param, param_range_start,
                                param_range_end)
        else:
            for instance_param in self._instance_params:
                yield instance_param
        if self._is_properly_nested(must_be_bundled=include_nested_only_if_bundled):
            # Include the nested instance parameters bundled with this one.
            for instance_param in (
                    self._instance_expr._effective_instance_param_entries(
                        include_nested_only_if_bundled=include_nested_only_if_bundled)):
                yield instance_param
    
    @property
    def instance_params(self):
        '''
        Return instance parameters, including bundled ones, as an ExprTuple.
        '''
        return composite_expression(list(self._effective_instance_param_entries(
            include_nested_only_if_bundled=True)))

    @property
    def instance_param_or_params(self):
        '''
        If there is a single, unbundled instance parameter, return that;
        otherwise, return the 'instance_params'.
        '''
        try:
            return self.instance_param
        except AttributeError:
            return self.instance_params

    def _instance_param_lists(self):
        '''
        Yield lists of instance vars that include all of the instance
        paramaters (see all_instance_params method) but grouped together
        according to the style joining instance variables together.
        '''
        expr = self
        while True:
            param_list = []
            if hasattr(expr, '_instance_param'):
                param_list.append(expr._instance_param)
            else:
                param_list.extend(expr._instance_params)
            if not expr._is_properly_nested(must_be_bundled=True):
                yield param_list
            if not expr._is_properly_nested(must_be_bundled=False):
                return # end of the road
            expr = expr._instance_expr

    def instance_param_lists(self):
        '''
        Returns lists of instance parameters that include all of the instance
        parameters (see all_instance_params method) but grouped together
        according to nesting styles.
        '''
        return list(self._instance_param_lists())

    def all_instance_params(self):
        '''
        Returns all instance parameters of this OperationOverInstances and
        nested OperationOverInstances of the same type regardless of the
        'nesting' style.
        '''
        return [param for param_list in self.instance_param_lists
                for param in param_list]

    @property
    def instance_var(self):
        '''
        Return a single, unbunded instance variable if applicable
        or raise an AttributeError.
        '''
        if hasattr(self, '_instance_var') and not self._is_bundled():
            return self._instance_var
        raise AttributeError("No single 'instance_var'")

    def _effective_instance_vars(self, *, include_nested_only_if_bundled):
        '''
        Yield all bundled instance variables.
        '''
        if hasattr(self, '_instance_var'):
            yield self._instance_var
        else:
            for instance_var in self._instance_vars:
                yield instance_var
        if self._is_properly_nested(must_be_bundled=include_nested_only_if_bundled):
            # Include the nested instance parameters bundled with this one.
            for instance_var in self._instance_expr._effective_instance_vars(
                    include_nested_only_if_bundled=include_nested_only_if_bundled):
                yield instance_var

    @property
    def instance_vars(self):
        '''
        Return instance variables, including bundled ones, as a tuple.
        '''
        return tuple(self._effective_instance_vars(
            include_nested_only_if_bundled=True))

    def all_instance_vars(self):
        '''
        Returns all instance parameter variables of this OperationOverInstances
        and all instance parameters variables of nested OperationOverInstances
        regardless of the 'nesting' style.
        '''
        return tuple(self._effective_instance_vars(
            include_nested_only_if_bundled=False))

    @property
    def instance_expr(self):
        '''
        Expression corresponding to each 'instance' in the 
        OperationOverInstances.  When there are conditions, this can
        depend on the 'condition' style.  For example, the instance_expr
        of forall_{x | Q(x)} P(x) is P(x) if that style is 'compact' but
        will display as forall_{x} [Q(x) ⇒ P(x)] with [Q(x) ⇒ P(x)] as the
        instance_expr if that style is 'expanded'.  It can also depend
        on the 'nesting' style being 'bundled' or 'unbundled'.
        '''
        if self.get_style('nesting', 'unbundled') == 'bundled' and (
                type(self._instance_expr) == type(self)):
            return self._instance_expr.instance_expr
        if self.get_style('condition', 'compact') == 'compact':
            return self._instance_expr
        else:
            # Show the condition with the 'expanded' style.
            return self.operand.body
    
    def _all_instance_exprs(self):
        expr = self
        while hasattr(expr, 'instance_expr'):
            yield expr.instance_expr
            expr = expr.instance_expr

    def all_instance_exprs(self):
        '''
        Return a list of all nested instance expressions.
        '''
        return list(self._all_instance_exprs())

    @property
    def domain(self):
        '''
        Return the single, only domain if applicable or raise an 
        AttributeError.
        '''
        domains = self.domains
        if len(domains) == 0:
            raise AttributeError("No 'domain'")
        domain = domains[0]
        if domains[0] is None:
            raise AttributeError("No 'domain'")
        if not all(_domain==domain for _domain in domains):
            raise AttributeError("No single 'domain'")
        return domain

    def _effective_domains(self, *, include_nested_only_if_bundled):
        '''
        Yield all bundled domains where the condition style is 'compact'.
        '''
        if self.get_style('condition', 'compact') == 'expanded':
            raise AttributeError('No explicit domains')
        instance_params = self._instance_params
        conditions_iter = iter(self._conditions)
        next_condition = None
        for iparam in instance_params:
            if next_condition is None:
                try:
                    next_condition = next(conditions_iter)
                except StopIteration:
                    yield None
                    continue
            condition = next_condition
            domain = _extract_domain_from_condition(iparam, condition)
            if domain is not None:
                next_condition = None # move on to the next, next_condition
            yield domain
        if self._is_properly_nested(must_be_bundled=include_nested_only_if_bundled):
            # Include the nested instance parameters bundled with this one.
            for domain in self._instance_expr._effective_domains(
                    include_nested_only_if_bundled=include_nested_only_if_bundled):
                yield domain

    @property
    def domains(self):
        '''
        Return the domains, including bundled ones, as a tuple.
        '''
        return tuple(self._effective_domains(include_nested_only_if_bundled=True))

    def all_domains(self):
        '''
        Returns all domains of this OperationOverInstances
        including domains of nested OperationOverInstances
        of the same type, regardless of the 'nesting' style.
        '''
        return tuple(self._effective_domains(include_nested_only_if_bundled=False))

    def explicit_domains(self):
        '''
        Return the domains of the instance variables that are to be
        displayed explicitly (not with an 'expanded' condition) as a tuple.
        '''
        if self.get_style('condition', 'compact') == 'expanded':
            # No explicit domains when using style 'condition':'expanded'.
            return tuple()
        return self.domains

    def has_domain(self):
        '''
        Return True if and only if each instance parameter has
        the some explicit domain.
        '''
        if hasattr(self, 'domain'):
            return True
        return False

    def _parameters_with_applicable_domain_conditions(self, remaining_conditions):
        '''
        Return a list of all parameters or applicable domain conditions
        bundled according to 'nesting' style.
        '''
        instance_params = self.instance_params
        if not hasattr(self, 'domains'):
            return instance_params
        domains_iter = iter(self._effective_domains(
            include_nested_only_if_bundled=True))
        cond_index = 0
        for iparam in instance_params:
            try:
                domain = next(domains_iter)
            except StopIteration:
                domain = None
            if domain is None:
                yield iparam
            else:
                while True:
                    cond = remaining_conditions[cond_index]
                    if domain == _extract_domain_from_condition(iparam, cond):
                        break # found the next domain condition
                    cond_index += 1
                remaining_conditions.pop(cond_index)
                yield cond
 
    def domain_conditions(self):
        '''
        Return the domain conditions of all instance variables that
        are joined together at this level according to the style.
        '''
        if hasattr(self, 'domains'):
            num_domains = 0
            conditions_iter = iter(self.conditions)
            for iparam, domain in zip(self.instance_params, self.domains):
                if domain is None: continue
                condition = next(conditions_iter)
                assert domain == _extract_domain_from_condition(
                    iparam, condition)
                num_domains += 1
            return self.conditions[:num_domains]
        else:
            return tuple()
    
    def _effective_conditions(self, *, include_nested_only_if_bundled):
        '''
        Yield all bundled conditions where the condition style is 'compact'.
        '''
        if self.get_style('condition', 'compact') == 'expanded':
            return
        for condition in self._conditions:
            yield condition
        if self._is_properly_nested(must_be_bundled=include_nested_only_if_bundled):
            # Include the nested conditions bundled with this one.
            for condition in self._instance_expr._effective_conditions(
                    include_nested_only_if_bundled=include_nested_only_if_bundled):
                yield condition

    @property
    def condition(self):
        if self.get_style('condition', 'compact') == 'expanded':
            raise AttributeError("No compact 'condition'")
        return self._condition

    @property
    def conditions(self):
        '''
        Return the conditions, including domain conditions and bundled ones, 
        as a tuple.
        '''
        return tuple(self._effective_conditions(include_nested_only_if_bundled=True))

    def all_conditions(self):
        '''
        Returns the conditions, including domain conditions, of this 
        OperationOverInstances and nested OperationOverInstances
        of the same type, regardless of the 'nesting' style.
        '''
        return tuple(self._effective_conditions(include_nested_only_if_bundled=False))

    def non_domain_conditions(self):
        '''
        Return a list of conditions that exclude the domain conditions.
        '''
        remaining_conditions = list(self.conditions)
        list(self._parameters_with_applicable_domain_conditions(
            remaining_conditions))
        return remaining_conditions
        
    def non_domain_condition(self):
        '''
        Return the condition that excludes domain condition(s); this
        will be a conjunction if there are more than one non-domain
        conditions or TRUE if there are zero.
        '''
        from proveit.logic import And, TRUE
        non_domain_conditions = self.non_domain_conditions()
        if len(non_domain_conditions) == 0:
            return TRUE
        if len(non_domain_conditions) == 1:
            return non_domain_conditions[0]
        return And(non_domain_conditions)
        
    """
    def explicit_conditions(self):
        '''
        Return the conditions that are to be shown explicitly in the formatting
        (after the "such that" symbol "|") at this level according to the
        style.  By default, this includes all of the 'joined' conditions except
        implicit 'domain' conditions.
        If using 'condition':'expanded' style, there are no 'explicit'
        conditions.
        '''
        if self.get_style('condition', 'compact') == 'expanded':
            return tuple()
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
    """

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions
        auto_nest_multi_params = self.auto_nest_multi_params()
        options = StyleOptions(self)
        options.add_option(
            name = 'with_wrapping',
            description = ("If 'True', wrap the Expression after "
                           "the parameters"),
            default = None, 
            related_methods = ('with_wrapping', 'without_wrapping'))
        options.add_option(
            name = 'justification',
            description = ("justify to the 'left', 'center', or 'right' "
                           "in the array cells when 'with_wrapping' is True"),
            default = 'center',
            related_methods = ('with_justification', 'with_wrapping'))
        options.add_option(
            name = 'condition',
            description = ("Show the condition (if there is one) as 'compact' "
                           "or 'expanded' (as internally represented)."),
            default = 'compact',
            related_methods = ('with_compact_condition', 'with_expanded_condition',
                               'has_compact_condition', 'has_expanded_condition')),
        if auto_nest_multi_params and (
                isinstance(self._instance_expr, self.__class__)):
            options.add_option(
                name = 'nesting',
                description = ("If 'bundled', combine the next nested operation "
                               "with this one to appear as one operation"),
                default = 'unbundled',
                related_methods = ('with_bundled_nesting', 
                                   'without_bundled_nesting'))
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
        if auto_nest_multi_params:
            options.add_option(
                name = 'param_range_start',
                description = ("Expression of start index/indices for a "
                               "range of parameters"),
                default = None,
                style_type = Expression,
                related_methods = ('with_param_range_indices',))
            options.add_option(
                name = 'param_range_end',
                description = ("Expression of end index/indices for a "
                               "range of parameters"),
                default = None,
                style_type = Expression,
                related_methods = ('with_param_range_indices',))
        return options

    def with_wrapping(self, wrap=True):
        '''
        Wraps the 'instance_expr' onto the next line. For example
        \forall_{a, b, c, d, e, f, g}
        P(a, b, c, d, e, f, g)

        rather than
        \forall_{a, b, c, d, e, f, g} P(a, b, c, d, e, f, g)
        '''
        return self.with_styles(with_wrapping=str(wrap))
    
    def without_wrapping(self):
        '''
        Disable 'with_wrapping'.
        '''
        return self.with_wrapping(False)

    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    def with_compact_condition(self):
        return self.with_styles(condition='compact')
    
    def with_expanded_condition(self):
        return self.with_styles(condition='expanded')

    def has_compact_condition(self):
        return hasattr(self, '_condition') and (
            self.get_style('condition', 'compact') == 'compact')

    def has_expanded_condition(self):
        return hasattr(self, '_condition') and (
            self.get_style('condition', 'compact') == 'expanded')

    def with_bundled_nesting(self):
        return self.with_styles(nesting='bundled')

    def without_bundled_nesting(self):
        return self.with_styles(nesting='unbundled')

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

    def with_param_range_indices(self, start_index_or_indices,
                                end_index_or_indices):
        '''
        Return a list of wrap conditions according to the current style setting.
        '''
        if not isinstance(start_index_or_indices, Expression) or (
                not isinstance(end_index_or_indices, Expression)):
            start_index_or_indices = composite_expression(start_index_or_indices)
            end_index_or_indices = composite_expression(end_index_or_indices)
        return self.with_styles(param_range_start=start_index_or_indices,
                                param_range_end=end_index_or_indices)

    def wrap_condition_positions(self):
        '''
        Return a list of wrap conditions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.get_style(
            'wrap_condition_positions', '').strip('()').split(' ')
            if pos_str != '']

    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)

    def _formatted(self, format_type, fence=False):
        '''
        Format the OperationOverInstances according to the style
        which may join nested operations of the same type.
        '''
        from proveit.logic import InSet, InClass

        # style call to wrap the expression after the parameters
        with_wrapping = (
                self.get_style('with_wrapping', 'False') == 'True')
        show_expanded_condition = (self.get_style('condition', 'compact')
                                       == 'expanded')
        justification = self.get_style('justification', 'center')
        suchthat_wrapping = self.get_style('suchthat_wrapping', 'No')
        if suchthat_wrapping == 'No': suchthat_wrapping=None
        suchthat_justification = self.get_style('suchthat_justification', 'left')
        param_justification = self.get_style('param_justification', 'left')
        condition_justification = self.get_style('condition_justification', 'left')
        instance_expr = self.instance_expr
        try:
            # Is there a single domain?
            domain = self.domain
            if (hasattr(domain, 'is_proper_class')
                    and domain.is_proper_class):
                domain_membership_op = InClass._operator_
            else:
                domain_membership_op = InSet._operator_
        except AttributeError:
            domain = None
        
        has_any_domain_condition = False
        if show_expanded_condition or len(self.conditions)==0:
            # The condition, including domain conditions, if there are any,
            # will be included in the instance_expr.
            params_with_applicable_domain_conds = self.instance_params
            explicit_conditions = tuple()      
            formatted_instance_expr = instance_expr.formatted(
                    format_type, fence=True)
        else:
            # Show 'compact' conditions.
            remaining_conditions = list(self.conditions)
            num_starting_conditions = len(remaining_conditions)
            params_with_applicable_domain_conds = composite_expression(
                list(self._parameters_with_applicable_domain_conditions(
                    remaining_conditions)))
            if len(remaining_conditions) < num_starting_conditions:
                has_any_domain_condition = True
            explicit_conditions = composite_expression(remaining_conditions)
            with defaults.temporary() as temp_defaults:
                # Add the conditions as assumptions when formatting 
                # the instance expression.
                temp_defaults.automation = False
                temp_defaults.assumptions = defaults.assumptions + (
                        self.conditions)
                formatted_instance_expr =  instance_expr.formatted(
                    format_type, fence=True)
        out_str = ''
        if fence:
            if format_type == 'latex':
                out_str += r'\left['
            else:
                out_str += '['
        if format_type == 'latex' and with_wrapping:
            out_str += r'\begin{array}{%s}'%justification[0]  
        out_str += self.operator.formatted(format_type) + '_{'
        if format_type == 'latex' and suchthat_wrapping is not None:
            out_str += r'\scriptsize \begin{array}{%s}'%suchthat_justification[0]
        if domain is None and has_any_domain_condition:
            # A different domain for each instance parameter
            out_str += params_with_applicable_domain_conds.formatted(
                format_type, operator_or_operators=';', 
                wrap_positions=self.wrap_param_positions(),
                justification=param_justification, fence=False)
        else:
            # No domains or 1 domain for all instance parameters
            out_str += self.instance_params.formatted(
                format_type, operator_or_operators=',', 
                wrap_positions=self.wrap_param_positions(), 
                justification=param_justification, fence=False)
            if domain is not None:
                out_str += ' %s '%domain_membership_op.formatted(format_type)
                out_str += self.domain.formatted(format_type, fence=False)
        if len(explicit_conditions) > 0:
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
            wrap_condition_positions = self.wrap_condition_positions()
            if len(wrap_condition_positions) > 0 and format_type == 'latex':
                out_str += r'\scriptsize'
            out_str += explicit_conditions.formatted(
                format_type, fence=False,
                wrap_positions=self.wrap_condition_positions(),
                justification=condition_justification)
        if format_type == 'latex' and suchthat_wrapping is not None:
            out_str += r'\end{array}'
        out_str += '}'
        if with_wrapping:
            if format_type == 'latex':
                out_str += r'\\'
            out_str += '\n'
        else:
            out_str += ' '
        out_str += formatted_instance_expr
        if format_type == 'latex' and with_wrapping:
            out_str += r'\end{array}'
        if fence:
            if format_type == 'latex':
                out_str += r'\right]'
            else:
                out_str += ']'
        return out_str

    @equality_prover('instance_substituted', 'instance_substitute')
    def instance_substitution(self, universal_eq, **defaults_config):
        '''
        Equate this OperationOverInstances, 
        Upsilon_{x_1, ..., x_n | Q(x_1, ..., x_n)} f(x_1, ..., x_n),
        with one that substitutes instance expressions given some
        universal_eq:
            forall_{x_1, ..., x_n | Q(x_1, ..., x_n)} 
                f(x_1, ..., x_n) = g(x_1, ..., x_n).
        Derive and return the following type of equality assuming 
        universal_eq:
        Upsilon_{x_1, ..., x_n | Q(x_1, ..., x_n)} f(x_1, ..., x_n) 
          = Upsilon_{x_1, ..., x_n | Q(x_1, ..., x_n)} g(x_1, ..., x_n)
        '''
        lambda_eq = self.operand.substitution(universal_eq)
        return lambda_eq.substitution(self.inner_expr().operand)
        
    """
    @prover
    def substitute_instances(self, universality, **defaults_config):
        '''
        Assuming this OperationOverInstances, Upsilon_{..x.. in S | ..Q(..x..)..} f(..x..)
        to be a true statement, derive and return Upsilon_{..x.. in S | ..Q(..x..)..} g(..x..)
        given some 'universality' = forall_{..x.. in S | ..Q(..x..)..} f(..x..) = g(..x..).
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        substitution = self.instance_substitution(universality, assumptions=assumptions)
        return substitution.derive_right_via_equality(assumptions=assumptions)
    """

@prover
def bundle(expr, bundle_thm, num_levels=2, **defaults_config):
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
        x_1_to_m = x_1_to_m.basic_replaced({m: _m})
        y_1_to_n = y_1_to_n.basic_replaced({n: _n})

        # We may need to auto-simplify, but we must preserve the
        # different parts.
        preserved_exprs = {expr, expr.instance_expr}
        preserved_exprs.update(expr.conditions)
        # Determine inner-most instance_expr and add it to the 
        # preserved_exprs set
        innermost_instance_expr = expr.all_instance_exprs()[-1]
        preserved_exprs.update([innermost_instance_expr])

        instantiation = bundle_thm.instantiate(
            {m: _m, n: _n, ExprTuple(x_1_to_m): bundled.instance_params,
             ExprTuple(y_1_to_n): bundled.instance_expr.instance_params,
             Pxy: _P, Qx: _Q, Rxy: _R}, preserved_exprs=preserved_exprs,
             auto_simplify=True)
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

@prover
def unbundle(expr, unbundle_thm, num_param_entries=(1,), 
             **defaults_config):
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
        first_params = unbundled.instance_params[:-n_last_entries]
        first_param_vars = {get_param_var(param) for param in first_params}
        remaining_params = unbundled.instance_params[-n_last_entries:]
        _m = first_params.num_elements()
        _n = remaining_params.num_elements()
        _P = unbundled.instance_expr
        # Split up the conditions between the outer
        # OperationOverInstances and inner OperationOverInstances
        condition = unbundled.effective_condition()
        if isinstance(condition, And):
            _nQ = 0
            for cond in condition.operands:
                cond_vars = free_vars(cond)
                if first_param_vars.isdisjoint(cond_vars):
                    break
                _nQ += 1
            if _nQ == 0:
                _Q = And()
            elif _nQ == 1:
                _Q = condition.operands[0]
            else:
                _Q = And(*condition.operands[:_nQ].entries)
            _nR = condition.operands.num_entries() - _nQ
            if _nR == 0:
                _R = And()
            elif _nR == 1:
                _R = condition.operands[-1]
            else:
                _R = And(*condition.operands[_nQ:].entries)
        elif first_param_vars.isdisjoint(free_vars(condition)):
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
        x_1_to_m = x_1_to_m.basic_replaced({m: _m})
        y_1_to_n = y_1_to_n.basic_replaced({n: _n})
        # We may need to auto-simplify, but we must also preserve the
        # various different original parts.
        preserved_exprs = {expr, expr.instance_expr}
        preserved_exprs.update(expr.conditions)
        instantiation = unbundle_thm.instantiate(
            {m: _m, n: _n, ExprTuple(x_1_to_m): first_params,
             ExprTuple(y_1_to_n): remaining_params,
             Pxy: _P, Qx: _Q, Rxy: _R},
             preserved_exprs=preserved_exprs, auto_simplify=True)
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

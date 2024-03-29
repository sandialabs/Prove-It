import inspect
from proveit.decorators import equality_prover
from proveit._core_.expression.expr import Expression, ImproperReplacement
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.defaults import defaults, USE_DEFAULTS

class Operation(Expression):
    # Map _operator_ Literals to corresponding Operation classes.
    # This is populated automatically when the _operator_ attribute
    # is accessed (see ExprType in proveit._core_.expression.expr).
    operation_class_of_operator = dict()

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store
        Prove-It state information must implement _clear_ to clear that
        information.
        '''
        Operation.operation_class_of_operator.clear()

    def __init__(self, operator, operand_or_operands=None, *, 
                 operands=None, styles):
        '''
        Create an operation with the given operator and operands.
        The operator must be a Label (a Variable or a Literal).
        If a composite expression is provided as the 
        'operand_or_operands' it is taken to be the 'operands' of the
        Operation; otherwise the 'operands' will be the the provided
        Expression wrapped as a single entry in an ExprTuple.
        When there is a single operand that is not an ExprRange, there
        will be an 'operand' attribute as well as 'operands' as an 
        ExprTuple containing the one operand.
        '''
        from proveit._core_.expression.composite import (
            composite_expression, single_or_composite_expression, 
            Composite, ExprTuple, NamedExprs)
        from proveit._core_.expression.lambda_expr import Lambda
        from .indexed_var import IndexedVar
        if self.__class__ == Operation:
            raise TypeError("Do not create an object of type Operation; "
                            "use a derived class (e.g., Function) instead.")
        self.operator = operator
        if (operand_or_operands==None) == (operands==None):
            if operands==None:
                raise ValueError(
                    "Must supply either 'operand_or_operands' or 'operands' "
                    "when constructing an Operation")
            else:
                raise ValueError(
                    "Must supply 'operand_or_operands' or 'operands' but not "
                    "both when constructing an Operation")
        if operands is not None:
            if not isinstance(operands, Expression):
                operands = composite_expression(operands)
            self.operands = operands
        else:
            orig_operand_or_operands = operand_or_operands
            operand_or_operands = single_or_composite_expression(
                operand_or_operands, do_singular_reduction=True)
            if isinstance(operand_or_operands, Composite):
                # a composite of multiple operands
                self.operands = operand_or_operands
            else:
                if isinstance(orig_operand_or_operands, Composite):
                    self.operands = orig_operand_or_operands
                else:
                    self.operands = ExprTuple(operand_or_operands)

        def raise_bad_operator_type(operator):
            raise TypeError("An operator may not be an explicit Lambda map "
                            "like %s; this is necessary to avoid a Curry's "
                            "paradox." % str(operator))
        if isinstance(self.operator, Lambda):
            raise_bad_operator_type(self.operator)
        if (isinstance(self.operands, ExprTuple) and 
                self.operands.is_single()):
            # This is a single operand.
            self.operand = self.operands[0]
        sub_exprs = (self.operator, self.operands)
        if isinstance(self, IndexedVar):
            core_type = 'IndexedVar'
        else:
            core_type = 'Operation'
        if isinstance(self.operands, NamedExprs):
            # Make attributes to make the keys of the NamedExprs 
            # operands.
            for key in self.operands.keys():
                setattr(self, key, self.operands[key])
        Expression.__init__(self, [core_type], sub_exprs, styles=styles)

    def style_options(self):
        '''
        Return the StyleOptions object for the Operation.
        '''
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        trivial_op = not (isinstance(self.operands, ExprTuple) and 
                          len(self.operands.entries) > 0  and
                          not self.operands.is_single())
        options = StyleOptions(self)
        # Note: when there are no operands or 1 operand, 'infix'
        # is like the 'function' style except the operator is
        # wrapped in square braces.
        options.add_option(
                name = 'operation',
                description = "'infix' or 'function' style formatting",
                default = 'infix',
                related_methods = ())
        if not trivial_op:
            # Wrapping is only relevant if there is more than one
            # operand.
            options.add_option(
                name = 'wrap_positions',
                description = (
                        "position(s) at which wrapping is to occur; "
                        "'2 n - 1' is after the nth operand, '2 n' is "
                        "after the nth operation."),
                default = '()',
                related_methods = (
                        'with_wrapping_at', 'with_wrap_before_operator',
                        'with_wrap_after_operator', 
                        'without_wrapping',
                        'wrap_positions'))
            options.add_option(
                name = 'justification',
                description = (
                        "if any wrap positions are set, justify to the 'left', "
                        "'center', or 'right'"),
                default = 'center',
                related_methods = ('with_justification',))
        return options

    def with_wrapping_at(self, *wrap_positions):
        return self.with_styles(
            wrap_positions='(' +
            ' '.join(
                str(pos) for pos in wrap_positions) +
            ')')

    def without_wrapping(self, *wrap_positions):
        return self.with_wrapping_at()

    def with_wrap_before_operator(self):
        if self.operands.num_entries() != 2:
            raise NotImplementedError(
                "'with_wrap_before_operator' only valid when there are 2 operands")
        return self.with_wrapping_at(1)

    def with_wrap_after_operator(self):
        if self.operands.num_entries() != 2:
            raise NotImplementedError(
                "'with_wrap_after_operator' only valid when there are 2 operands")
        return self.with_wrapping_at(2)

    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    @classmethod
    def _implicit_operator(operation_class):
        if hasattr(operation_class, '_operator_'):
            return operation_class._operator_
        return None

    @classmethod
    def extract_init_arg_value(cls, arg_name, operator, operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).

        Except when this is an OperationOverInstances, this method should
        be overridden if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        from proveit import NamedExprs
        if isinstance(operands, NamedExprs):
            # If the operands are NamedExprs, presume the arguments
            # correspond to the names of the sub-expressions.
            if arg_name in operands:
                return operands[arg_name]
            else:
                return None
        raise NotImplementedError(
            "'%s.extract_init_arg_value' must be appropriately implemented; "
            "__init__ arguments do not fall into a simple 'default' "
            "scenarios."%str(cls))

    def extract_my_init_arg_value(self, arg_name):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value appropriate for reconstructing self.
        The default calls the extract_init_arg_value static method.  Overload
        this when the most proper way to construct the expression is style
        dependent.  Then "remake_arguments" will use this overloaded method.
        "_make" will do it via the static method but will fix the styles
        afterwards.
        '''
        return self.__class__.extract_init_arg_value(
            arg_name, self.operator, self.operands)

    def _extract_my_init_args(self):
        '''
        Call the _extract_init_args class method but will set "obj" to "self".
        This will cause extract_my_init_arg_value to be called instead of
        the extract_init_arg_value static method.
        '''
        return self.__class__._extract_init_args(
            self.operator, self.operands, obj=self)

    @classmethod
    def _extract_init_args(cls, operator, operands, obj=None):
        '''
        For a particular Operation class and given operator and 
        operands, yield (name, value) pairs to pass into the 
        initialization method for creating the operation consistent 
        with the given operator and operands.

        First attempt to call 'extract_init_arg_value' (or 
        'extract_my_init_arg_value' if 'obj' is provided, or if the
        operands is a NamedExprs then get the associated NamedExprs 
        value) for each of the __init__ arguments to determine how to 
        generate the appropriate __init__ parameters from the given 
        operators and operands.  If that is not implemented, fall back 
        to one of the following default scenarios.

        If the particular Operation class has an 'implicit operator' 
        defined via an _operator_ attribute and the number of __init__
        arguments matches the number of operands or it takes only a
        single *args variable-length argument list: construct the 
        Operation by passing each operand individually.

        Otherwise, if there is no 'implicit operator' and __init__ 
        accepts only two arguments (no variable-length or keyward
        arguments): construct the Operation by passeng the operation(s) 
        as the first argument and operand(s) as the second argument.  
        If the length of either of these is 1, then the single 
        expression is passed rather than a composite.

        Otherwise, if there is no 'implicit operator' and __init__ 
        accepts one formal  argument and a variable-length argument and 
        no keyword arguments, or a number of formal arguments equal to
        the number of operands plus 1 and no variable-length argument 
        and no keyword arguments: construct the Operation by passing 
        the operator(s) and each operand individually.
        '''
        from .function import Function
        from proveit._core_.expression.composite import (
            ExprTuple, Composite, NamedExprs)
        implicit_operator = cls._implicit_operator()
        matches_implicit_operator = (operator == implicit_operator)
        if implicit_operator is not None and not matches_implicit_operator:
            raise OperationError("An implicit operator may not be changed "
                                 "(%s vs %s)"%(operator, implicit_operator))
        sig = inspect.signature(cls.__init__)
        Parameter = inspect.Parameter
        init_params = sig.parameters
        
        if isinstance(operands, NamedExprs):
            extract_init_arg_value_fn = (
                    lambda arg : operands.get(arg))
        elif obj is None:
            def extract_init_arg_value_fn(arg): 
                return cls.extract_init_arg_value(arg, operator, operands)
        else:
            extract_init_arg_value_fn = \
                lambda arg: obj.extract_my_init_arg_value(arg)
        try:
            first_param = True
            for param_name, param in init_params.items():
                if first_param:
                    # Skip the 'self' parameter.
                    first_param = False
                    continue
                if param_name=='styles':
                    continue # skip the styles parameter
                param = init_params[param_name]
                default = param.default
                val = extract_init_arg_value_fn(param_name)
                if val is None: 
                    if isinstance(operands, NamedExprs) and (
                            default is param.empty):
                        raise TypeError(
                                "'%s' not in the NamedExprs operand, %s, "
                                "extracting init args of a %s"
                                %(param_name, operands, cls))
                    val = default
                if default is param.empty or val != default:
                    # Override the default if there is one.
                    if not isinstance(val, Expression):
                        raise TypeError(
                            "extract_init_arg_val for %s should return "
                            "an Expression but is returning a %s" %
                            (param_name, type(val)))
                    if param.kind == Parameter.POSITIONAL_ONLY:
                        yield val
                    else:
                        yield (param_name, val)
        except NotImplementedError:
            # Try some default scenarios that don't require
            # extract_init_arg_value_fn to be implemented.
            pos_params = []
            var_params = None
            kwonly_params = []
            varkw = None
            for name, param in init_params.items():
                if param.kind in (Parameter.POSITIONAL_ONLY,
                                  Parameter.POSITIONAL_OR_KEYWORD):
                    pos_params.append(name)
                elif param.kind == Parameter.VAR_POSITIONAL:
                    var_params = name
                elif param.kind == Parameter.KEYWORD_ONLY:
                    kwonly_params.append(name)
                elif param.kind == Parameter.VAR_KEYWORD:
                    varkw = name
            pos_params = pos_params[1:] # skip 'self'

            # Note: None keyword indicates that we should create a 
            # generic Function for these all-in-one operands 
            # (e.g. a variable representing an ExprTuple).
            if cls==Function:
                operands_kw = 'operands'
            else:
                operands_kw = None
            
            num_operands = (operands.num_entries() if 
                            isinstance(operands, ExprTuple) else 1)
            if implicit_operator and num_operands < len(pos_params):
                raise ValueError(
                        "Not enough supplied operands for extracting "
                        "init args of a %s: needed %d got %d"%(
                                cls, len(pos_params), num_operands))
            if (varkw is None):
                # handle default implicit operator case
                if implicit_operator and (
                    (len(pos_params) == 0 and var_params is not None) or (
                        len(pos_params) == num_operands 
                        and var_params is None)):
                    if isinstance(operands, ExprTuple):
                        # yield each operand separately
                        for operand in operands:
                            yield operand
                        return
                    elif not isinstance(operands, Composite):
                        # Create a generic Operation
                        yield operator
                        yield (operands_kw, operands) 
                        return
                # handle default explicit operator case
                elif (implicit_operator is None) and (varkw is None):
                    if var_params is None and len(pos_params) == 2:
                        # assume one argument for the operator and one
                        # argument for the operands
                        yield operator
                        if isinstance(operands, Composite):
                            yield operands
                        else:
                            yield (operands_kw, operands)
                        return
                    elif ((var_params is not None and len(pos_params) == 1) or 
                          (len(pos_params) == operands.num_entries() + 1 
                           and var_params is None)):
                        # yield the operator
                        yield operator
                        if isinstance(operands, ExprTuple):
                            # yield each operand separately
                            for operand in operands:
                                yield operand
                            return
                        elif not isinstance(operands, Composite):
                            yield (operands_kw, operands)
                            return
                raise NotImplementedError(
                    "Must implement 'extract_init_arg_value' for the "
                    "Operation of type %s if it does not fall into "
                    "one of the default cases for 'extract_init_args'"
                    % str(cls))

    @classmethod
    def _make(operation_class, core_info, sub_expressions, *, styles):
        '''
        Make the appropriate Operation.  core_info should equal 
        ('Operation',).  The first of the sub_expressions should be 
        the operator and the second should be the operands.  This 
        implementation expects the Operation sub-class to have a
        class variable named '_operator_' that defines the Literal 
        operator of the class.  It will instantiate the Operation 
        sub-class with just *operands and check that the operator is 
        consistent.  Override this method if a different behavior is 
        desired.
        '''
        from proveit._core_.expression.label.var import Variable
        from .function import Function
        if len(core_info) != 1 or core_info[0] != 'Operation':
            raise ValueError(
                "Expecting Operation core_info to contain exactly one item: 'Operation'")
        if len(sub_expressions) == 0:
            raise ValueError(
                'Expecting at least one sub_expression for an Operation, for the operator')
        operator, operands = sub_expressions[0], sub_expressions[1]
        implicit_operator = operation_class._implicit_operator()
        if implicit_operator is not None and isinstance(operator, Variable):
            # Convert an implicit operator to a variable.
            return Function(operator, operands, styles=styles)
        if operation_class == Operation:
            return Function(operator, operands, styles=styles)
        args = []
        kw_args = dict()
        for arg in operation_class._extract_init_args(
                operator, operands):
            if isinstance(arg, Expression):
                args.append(arg)
            else:
                kw, val = arg
                if kw==None:
                    # kw=None used to indicate that
                    # we should create a generic Function
                    # and use the 'operands' keyword
                    # (e.g. to represent an ExprTuple of
                    # operands with a variable).
                    operation_class = Function
                    kw = 'operands'
                kw_args[kw] = val
        return operation_class(*args, **kw_args, styles=styles)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        for arg in self._extract_my_init_args():
            yield arg

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        wrap_positions = self.wrap_positions()
        call_strs = []
        if len(wrap_positions) > 0:
            call_strs.append('with_wrapping_at(' + ','.join(str(pos)
                                                            for pos in wrap_positions) + ')')
        justification = self.get_style('justification', 'center')
        if justification != 'center':
            call_strs.append('with_justification("' + justification + '")')
        return call_strs

    def string(self, **kwargs):
        # When there is a single operand, we must use the "function"-style
        # formatting.
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        if (isinstance(self.operands, ExprTuple) and 
                self.get_style('operation', 'function') == 'function'):
            return self._function_formatted('string', **kwargs)
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        # When there is a single operand, we must use the "function"-style
        # formatting.
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        if (isinstance(self.operands, ExprTuple) and
                self.get_style('operation', 'function') == 'function'):
            return self._function_formatted('latex', **kwargs)
        return self._formatted('latex', **kwargs)

    def wrap_positions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.get_style(
            'wrap_positions', '').strip('()').split(' ') if pos_str != '']

    def _function_formatted(self, format_type, **kwargs):
        from proveit._core_.expression.composite.expr_tuple import ExprTuple
        formatted_operator = self.operator.formatted(format_type, fence=True)
        lparen = r'\left(' if format_type=='latex' else '('
        rparen = r'\right)' if format_type=='latex' else ')'
        if (hasattr(self, 'operand') and 
                not isinstance(self.operand, ExprTuple)):
            formatted_operand = self.operand.formatted(
                    format_type, fence=False)
        else:
            formatted_operand = self.operands.formatted(
                    format_type, fence=False, sub_fence=False)

        return (formatted_operator + lparen + formatted_operand + rparen)


    def _formatted(self, format_type, **kwargs):
        '''
        Format the operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(format_type).

        '''
        return Operation._formatted_operation(
            format_type, self.operator, self.operands,
            implicit_first_operator=True,
            wrap_positions=self.wrap_positions(),
            justification=self.get_style('justification', 'center'),
            **kwargs)

    @staticmethod
    def _formatted_operation(
            format_type, operator_or_operators, operands, *,
            wrap_positions, justification, implicit_first_operator=True,
            **kwargs):
        from proveit import ExprRange, ExprTuple, composite_expression
        if (isinstance(operator_or_operators, Expression) and 
                not isinstance(operator_or_operators, ExprTuple)):
            # Single operator case.
            operator = operator_or_operators
            if isinstance(operands, ExprTuple):
                # An ExprTuple of operands.
                # Different formatting when there is 0 or 1 element, unless
                # it is an ExprRange.
                if operands.num_entries() < 2:
                    if operands.num_entries() == 0 or not isinstance(
                            operands[0], ExprRange):
                        if format_type == 'string':
                            return ('[' + operator.string(fence=True) + '](' 
                                    + operands.string(fence=False, sub_fence=False) + ')')
                        else:
                            return (r'\left[' + operator.latex(fence=True) + r'\right]\left(' 
                                    + operands.latex(fence=False, sub_fence=False) + r'\right)')
                        raise ValueError(
                            "Unexpected format_type: " + str(format_type))
                fence = kwargs.get('fence', False)
                sub_fence = kwargs.get('sub_fence', True)
                do_wrapping = len(wrap_positions) > 0
                formatted_str = ''
                formatted_str += operands.formatted(
                        format_type, fence=fence, sub_fence=sub_fence,
                        operator_or_operators=operator,
                        implicit_first_operator=implicit_first_operator,
                        wrap_positions=wrap_positions,
                        justification=justification)
                return formatted_str
            else:
                # The operands ExprTuple are being represented by a Variable
                # (or Operation) equating to an ExprTuple.  We will format this
                # similarly as when we have 1 element except we drop the
                # round parantheses.  For example, [+]a, where a represents
                # the ExprTuple of operands for the '+' operation.
                if format_type == 'string':
                    return '[' + operator.string(fence=True) + ']' + operands.string(
                        fence=False, sub_fence=False)
                else:
                    return (r'\left[' + operator.latex(fence=True) + r'\right]' 
                            + operands.latex(fence=False, sub_fence=False))
        else:
            operators = operator_or_operators
            operands = composite_expression(operands)
            # Multiple operator case.
            # Different formatting when there is 0 or 1 element, unless it is
            # an ExprRange
            if operands.num_entries() < 2:
                if operands.num_entries() == 0 or not isinstance(
                        operands[0], ExprRange):
                    raise OperationError(
                        "No defaut formatting with multiple operators and zero operands")
            fence = kwargs['fence'] if 'fence' in kwargs else False
            sub_fence = kwargs['sub_fence'] if 'sub_fence' in kwargs else True
            do_wrapping = len(wrap_positions) > 0
            formatted_str = ''
            if fence:
                formatted_str = '(' if format_type == 'string' else r'\left('
            if do_wrapping and format_type == 'latex':
                formatted_str += r'\begin{array}{%s} ' % justification[0]
            formatted_str += operands.formatted(
                    format_type, fence=False, sub_fence=sub_fence,
                    operator_or_operators=operators,
                    implicit_first_operator=implicit_first_operator,
                    wrap_positions=wrap_positions)
            if do_wrapping and format_type == 'latex':
                formatted_str += r' \end{array}'
            if fence:
                formatted_str += ')' if format_type == 'string' else r'\right)'
            return formatted_str

    def basic_replaced(self, repl_map, *, 
                       allow_relabeling=False, requirements=None):
        '''
        Returns this expression with sub-expressions substituted
        according to the replacement map (repl_map) dictionary.

        When an operater of an Operation is substituted by a Lambda map,
        the operation itself will be substituted with the Lambda map
        applied to the operands.  For example, substituting
        f : (x,y) -> x+y
        on f(a, b) will result in a+b.  When performing operation
        substitution with a range of parameters, the Lambda map
        application will require the number of these parameters
        to equal with the number of corresponding operand elements.
        For example,
        f : (a, b_1, ..., b_n) -> a*b_1 + ... + a*b_n
        n : 3
        applied to f(w, x, y, z) will result in w*x + w*y + w*z provided
        that |(b_1, ..., b_3)| = |(x, y, z)| is proven.
        Assumptions may be needed to prove such requirements.
        Requirements will be appended to the 'requirements' list if one
        is provided.

        There are limitations with respect the Lambda map application involving
        iterated parameters when perfoming operation substitution in order to
        keep derivation rules (i.e., instantiation) simple.  For details,
        see the ExprRange.substituted documentation.
        '''
        from proveit import Lambda, ExprRange

        if len(repl_map) > 0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]

        # Perform substitutions for the operator(s) and operand(s).
        subbed_operator = \
            self.operator.basic_replaced(
                    repl_map, allow_relabeling=allow_relabeling,
                    requirements=requirements)
        subbed_operands = \
            self.operands.basic_replaced(
                    repl_map, allow_relabeling=allow_relabeling,
                    requirements=requirements)

        # Check if the operator is being substituted by a Lambda map in
        # which case we should perform full operation substitution.
        if isinstance(subbed_operator, Lambda):
            # Substitute the entire operation via a Lambda map
            # application.  For example, f(x, y) -> x + y,
            # or g(a, b_1, ..., b_n) -> a * b_1 + ... + a * b_n.

            if isinstance(subbed_operator.body, ExprRange):
                raise ImproperReplacement(
                    self, repl_map,
                    "The function %s cannot be defined using this "
                    "lambda, %s, that has an ExprRange for its body; "
                    "that could lead to tuple length contradictions."
                    % (self.operator, subbed_operator))
            return Lambda._apply(
                subbed_operator.parameters, subbed_operator.body,
                *subbed_operands.entries, requirements=requirements)
        
        # If the operator is a literal operator of
        # an Operation class defined via an "_operator_" class
        # attribute, then create the Operation of that class.
        if subbed_operator in Operation.operation_class_of_operator:
            op_class = Operation.operation_class_of_operator[subbed_operator]
            if op_class != self.__class__:
                # Don't transfer the styles; they may not apply in
                # the same manner in the setting of the new
                # operation.
                subbed_sub_exprs = (subbed_operator, subbed_operands)
                return op_class._checked_make(
                    ['Operation'], sub_expressions=subbed_sub_exprs,
                    style_preferences=self._style_data.styles)
        
        subbed_sub_exprs = (subbed_operator,
                            subbed_operands)
        return self.__class__._checked_make(
            self._core_info, subbed_sub_exprs, 
            style_preferences=self._style_data.styles)

    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        If possible, return a Judgment of this expression equal to an
        irreducible value.  This Operation.evaluation version
        simplifies the operands and then calls shallow_simplification
        with must_evaluat=True.
        '''
        from proveit import UnsatisfiedPrerequisites, ProofFailure
        from proveit.logic import EvaluationError, SimplificationError
        
        # Try to simplify the operands first.
        reduction = self.simplification_of_operands(
            simplify_with_known_evaluations=True)
        
        # After making sure the operands have been simplified,
        # try 'shallow_simplification' with must_evaluate=True.
        try:
            if reduction.lhs == reduction.rhs:
                # _no_eval_check is a directive to the @equality_prover wrapper 
                # to tell it not to check for an existing evaluation if we have
                # already checked.
                return self.shallow_simplification(
                    must_evaluate=True, _no_eval_check=True)
            evaluation = reduction.rhs.shallow_simplification(
                    must_evaluate=True)
        except (SimplificationError, UnsatisfiedPrerequisites,
                NotImplementedError, ProofFailure):
            raise EvaluationError(self)
        return reduction.apply_transitivity(evaluation)

    @equality_prover('simplified', 'simplify')
    def simplification(self, **defaults_config):
        '''
        If possible, return a Judgment of this expression equal to a
        simplified form (according to strategies specified in 
        proveit.defaults). 
        
        This Operation.simplification version tries calling
        simplifies the operands and then calls 'shallow_simplification'.
        '''
        # Try to simplify the operands first.
        reduction = self.simplification_of_operands()

        # After making sure the operands have been simplified,
        # try 'shallow_simplification'.
        # Use the 'reduction' as a replacement in case it is needed.
        # For example, consider 
        #       1*b + 3*b
        #   It's reduction is
        #       1*b + 3*b = b + 3*b
        #   But in the shallow simplification, we'll do a factorization
        #   that will exploit the "reduction" fact which wouldn't
        #   otherwise be used because (1*b + 3*b) is a preserved
        #   expression since simplification is an @equality_prover.

        if reduction.lhs == reduction.rhs:
            # _no_eval_check is a directive to the @equality_prover wrapper 
            # to tell it not to check for an existing evaluation if we have
            # already checked.
            return self.shallow_simplification(_no_eval_check=True)
        else:
            simplification = reduction.rhs.shallow_simplification(
                replacements=[reduction])
            return reduction.apply_transitivity(simplification)
    
    @equality_prover('simplified_operands', 'operands_simplify')
    def simplification_of_operands(self, **defaults_config):
        '''
        Prove this Operation equal to a form in which its operands
        have been simplified.
        '''
        from proveit.relation import TransRelUpdater
        from proveit import ExprRange, NamedExprs
        from proveit.logic import is_irreducible_value
        if any(isinstance(operand, ExprRange) for operand in self.operands):
            # If there is any ExprRange in the operands, simplify the
            # operands together as an ExprTuple.
            return self.inner_expr().operands[:].simplification()
        else:
            expr = self
            eq = TransRelUpdater(expr)
            with defaults.temporary() as temp_defaults:
                # No auto-simplification or replacements here;
                # just simplify operands one at a time.
                temp_defaults.preserve_all = True
                operands = self.operands
                if isinstance(operands, NamedExprs):
                    # operands as NamedExprs
                    for key in operands.keys():
                        operand = operands[key]
                        if not is_irreducible_value(operand):
                            inner_operand = getattr(expr.inner_expr(), key)
                            expr = eq.update(inner_operand.simplification())
                else:
                    # operands as ExprTuple
                    for k, operand in enumerate(operands):
                        if not is_irreducible_value(operand):
                            inner_operand = expr.inner_expr().operands[k]
                            expr = eq.update(inner_operand.simplification())
        return eq.relation

    @equality_prover('operator_substituted', 'operator_substitute')
    def operator_substitution(self, equality, **defaults_config):
        from proveit import f, g, n, x
        from proveit.core_expr_types.operations import (
                operator_substitution)
        _n = self.operands.num_elements()
        if equality.lhs == self.operator:
            return operator_substitution.instantiate(
                    {n:_n, x:self.operands, f:equality.lhs, g:equality.rhs})
        elif equality.rhs == self.operator:
            return operator_substitution.instantiate(
                    {n:_n, x:self.operands, f:equality.rhs, g:equality.lhs})
        else:
            raise ValueError("%s is not an appropriate 'equality' for "
                             "operator_substitution on %s (the 'operator' "
                             "is not matched on either side)"
                             %(equality, self))

    @equality_prover('operands_substituted', 'operands_substitute')
    def operands_substitution(self, equality, **defaults_config):
        from proveit import f, n, x, y
        from proveit.core_expr_types.operations import (
                operands_substitution)
        from proveit.logic.equality import substitution
        if equality.lhs == self.operands:
            _x, _y = equality.lhs, equality.rhs
        elif equality.rhs == self.operands:
            _x, _y = equality.rhs, equality.lhs
        else:
            raise ValueError("%s is not an appropriate 'equality' for "
                             "operator_substitution on %s (the 'operator' "
                             "is not matched on either side)"
                             %(equality, self))
        
        if self.operands.is_single():
            # This is a simple single-operand substitution.
            return substitution.instantiate(
                    {f:self.operator, x:_x[0], y:_y[0]})
        
        # More general mult-operand substitution:
        _n = self.operands.num_elements()
        if equality.lhs == self.operands:
            return operands_substitution.instantiate(
                    {n:_n, f:self.operator, x:equality.lhs, y:equality.rhs})
        elif equality.rhs == self.operands:
            return operands_substitution.instantiate(
                    {n:_n, f:self.operator, x:equality.rhs, y:equality.lhs})
        else:
            raise ValueError("%s is not an appropriate 'equality' for "
                             "operator_substitution on %s (the 'operator' "
                             "is not matched on either side)"
                             %(equality, self))
     
    @equality_prover('sub_expr_substituted', 'sub_expr_substitute')
    def sub_expr_substitution(self, new_sub_exprs, **defaults_config):
        '''
        Given new sub-expressions to replace existing sub-expressions,
        return the equality between this Expression and the new
        one with the new sub-expressions.
        '''
        from proveit.logic import Equals
        from proveit.relation import TransRelUpdater
        assert len(new_sub_exprs)==2, (
                "Expecting 2 sub-expressions: operator and operands")
        eq = TransRelUpdater(self)
        expr = self
        if new_sub_exprs[0] != self.sub_expr(0):
            expr = eq.update(expr.operator_substitution(
                    Equals(self.sub_expr(0), new_sub_exprs[0])))
        if new_sub_exprs[1] != self.sub_expr(1):
            expr = eq.update(expr.operands_substitution(
                    Equals(self.sub_expr(1), new_sub_exprs[1])))
        return eq.relation

    def operands_are_irreducible(self):
        '''
        Return True iff all of the operands of this Operation are
        irreducible.
        '''
        from proveit.logic import is_irreducible_value
        return all(is_irreducible_value(operand) for operand
                   in self.operands.entries)


class OperationError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message

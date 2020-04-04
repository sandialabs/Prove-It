import inspect
from proveit._core_.expression.expr import Expression, ImproperSubstitution
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.expression.fencing import maybeFenced
from proveit._core_.defaults import USE_DEFAULTS

class Operation(Expression):
    # Map _operator_ Literals to corresponding Operation classes.
    # This is populated automatcally when the _operator_ attribute
    # is accessed (see ExprType in proveit._core_.expression.expr).
    operationClassOfOperator = dict()
    
    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        Operation.operationClassOfOperator.clear()
        
    def __init__(self, operator_or_operators, operand_or_operands, styles=None):
        '''
        Create an operation with the given operator(s) and operand(s).
        The operator(s) must be Label(s) (a Variable or a Literal).
        When there is a single operator, there will be an 'operator'
        attribute.  When there is a single operand, there will be
        an 'operand' attribute.  In any case, there will be
        'operators' and 'operands' attributes that bundle
        the one or more Expressions into a composite Expression.
        '''
        from proveit._core_.expression.composite import Composite, compositeExpression, singleOrCompositeExpression, Iter
        from proveit._core_.expression.label.label import Label
        from .indexed_var import IndexedVar
        if styles is None: styles = dict()
        if hasattr(self.__class__, '_operator_') and operator_or_operators==self.__class__._operator_:
            operator = operator_or_operators
            if Expression.contexts[operator._style_id] != operator.context:
                raise OperationError("Expecting '_operator_' Context to match the Context of the Operation sub-class.  Use 'context=__file__'.")
        if isinstance(operator_or_operators, Iter):
            operator_or_operators = [operator_or_operators]
        if isinstance(operand_or_operands, Iter):
            operand_or_operands = [operand_or_operands]
        self.operator_or_operators = singleOrCompositeExpression(operator_or_operators)
        self.operand_or_operands = singleOrCompositeExpression(operand_or_operands)
        def raiseBadOperatorType(operator):
            raise TypeError('operator(s) must be a Label, an indexed variable '
                            '(IndexedVar), or iteration (Iter) over indexed'
                            'variables (IndexedVar). %s is none of those.'
                            %str(operator))            
        if isinstance(self.operator_or_operators, Composite):
            # a composite of multiple operators:
            self.operators = self.operator_or_operators 
            for operator in self.operators:
                if isinstance(operator, Iter):
                    if not isinstance(operator.body, IndexedVar):
                        raiseBadOperatorType(operator)
                elif not isinstance(operator, Label) and not isinstance(operator, IndexedVar):
                    raiseBadOperatorType(operator)
        else:
            # a single operator
            self.operator = self.operator_or_operators
            if not isinstance(self.operator, Label) and not isinstance(self.operator, IndexedVar):
                raiseBadOperatorType(self.operator)
            # wrap a single operator in a composite for convenience
            self.operators = compositeExpression(self.operator)
        if isinstance(self.operand_or_operands, Composite):
            # a composite of multiple operands
            self.operands = self.operand_or_operands
        else:
            # a single operand
            self.operand = self.operand_or_operands
            # wrap a single operand in a composite for convenience
            self.operands = compositeExpression(self.operand)
        if 'operation' not in styles:
            styles['operation'] = 'normal' # vs 'function
        if 'wrapPositions' not in styles:
            styles['wrapPositions'] = '()' # no wrapping by default
        if 'justification' not in styles:
            styles['justification'] = 'center'
        sub_exprs = (self.operator_or_operators, self.operand_or_operands)
        if isinstance(self, IndexedVar):
            core_type = 'IndexedVar'
        else:
            core_type = 'Operation'
        Expression.__init__(self, [core_type], sub_exprs, styles=styles)

    def styleOptions(self):
        options = StyleOptions(self)
        options.addOption('wrapPositions', 
                          ("position(s) at which wrapping is to occur; '2 n - 1' "
                           "is after the nth operand, '2 n' is after the nth "
                           "operation."))
        options.addOption('justification', 
                          ("if any wrap positions are set, justify to the 'left', "
                           "'center', or 'right'"))
        return options

    def withWrappingAt(self, *wrapPositions):
        return self.withStyles(wrapPositions='(' + ' '.join(str(pos) for pos in wrapPositions) + ')')
    
    def withWrapBeforeOperator(self):
        if len(self.operands)!=2:
            raise NotImplementedError("'withWrapBeforeOperator' only valid when there are 2 operands")
        return self.withWrappingAt(1)

    def withWrapAfterOperator(self):
        if len(self.operands)!=2:
            raise NotImplementedError("'withWrapAfterOperator' only valid when there are 2 operands")
        return self.withWrappingAt(2)

    def withJustification(self, justification):
        return self.withStyles(justification=justification)
                                            
    @classmethod
    def _implicitOperator(operationClass):
        if hasattr(operationClass, '_operator_'):
            return operationClass._operator_
        return None
    
    @classmethod
    def extractInitArgValue(cls, argName, operator_or_operators, operand_or_operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        
        Except when this is an OperationOverInstances, this method should
        be overridden if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        raise NotImplementedError("'extractInitArgValue' must be appropriately implemented if __init__ arguments do not fall into a simple 'default' scenario")

    def extractMyInitArgValue(self, argName):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value appropriate for reconstructing self.
        The default calls the extractInitArgValue static method.  Overload
        this when the most proper way to construct the expression is style
        dependent.  Then "remakeArguments" will use this overloaded method.
        "_make" will do it via the static method but will fix the styles
        afterwards.
        '''
        return self.__class__.extractInitArgValue(argName, self.operator_or_operators, self.operand_or_operands)

    def _extractMyInitArgs(self):
        '''
        Call the _extractInitArgs class method but will set "obj" to "self".
        This will cause extractMyInitArgValue to be called instead of
        the extractInitArgValue static method.
        '''
        return self.__class__._extractInitArgs(self.operator_or_operators, self.operand_or_operands, obj=self)
    
    @classmethod
    def _extractInitArgs(operationClass, operator_or_operators, operand_or_operands, obj=None):
        '''
        For a particular Operation class and given operator(s) and operand(s),
        yield (name, value) pairs to pass into the initialization method
        for creating the operation consistent with the given operator(s) and operand(s).
        
        First attempt to call 'extractInitArgValue' (or 'extractMyInitArgValue' if
        'obj' is provided) for each of the __init__ arguments to determine how
        to generate the appropriate __init__ parameters from the given operators
        and operands.  If that is not implemented, fall back to one of the 
        following default scenarios.
        
        If the particular Operation class has an 'implicit operator' defined
        via an _operator_ attribute and the number of __init__ arguments matches the
        number of operands or it takes only a single *args variable-length argument
        list: construct the Operation by passing each operand individually.
        
        Otherwise, if there is no 'implicit operator' and __init__ accepts 
        only two arguments (no variable-length or keyward arguments): construct
        the Operation by passeng the operation(s) as the first argument
        and operand(s) as the second argument.  If the length of either of
        these is 1, then the single expression is passed rather than a
        composite.
        
        Otherwise, if there is no 'implicit operator' and __init__ accepts 
        one formal  argument and a variable-length argument and no keyword 
        arguments, or a number of formal arguments equal to the number of operands
        plus 1 and no variable-length argument and no keyword arguments:
        construct the Operation by passing the operator(s) and
        each operand individually.
        '''
        from proveit._core_.expression.composite.composite import compositeExpression
        implicit_operator = operationClass._implicitOperator()
        matches_implicit_operator = (operator_or_operators == implicit_operator)
        if implicit_operator is not None and not matches_implicit_operator:
            raise OperationError("An implicit operator may not be changed")
        operands = compositeExpression(operand_or_operands)
        args, varargs, varkw, defaults = inspect.getargspec(operationClass.__init__)
        args = args[1:] # skip over the 'self' arg
        if len(args)>0 and args[-1]=='styles':
            args = args[:-1] # NOT TREATING 'styles' FULLY AT THIS TIME; THIS NEEDS WORK.
            defaults = defaults[:-1]
        if obj is None:
            extract_init_arg_value_fn = lambda arg : operationClass.extractInitArgValue(arg, operator_or_operators, operand_or_operands)
        else:
            extract_init_arg_value_fn = lambda arg : obj.extractMyInitArgValue(arg)
        try:
            arg_vals = [extract_init_arg_value_fn(arg) for arg in args]
            if varargs is not None:
                arg_vals += extract_init_arg_value_fn(varargs)
            if defaults is None: defaults = []
            for k, (arg, val) in enumerate(zip(args, arg_vals)):
                if len(defaults)-len(args)+k < 0:
                    if not isinstance(val, Expression):
                        raise TypeError("extractInitArgVal for %s should return an Expression but is returning a %s"%(arg, type(val)))
                    yield val # no default specified; just supply the value, not the argument name
                else:
                    if val == defaults[len(defaults)-len(args)+k]:
                        continue # using the default value
                    else:
                        yield (arg, val) # override the default
            if varkw is not None:
                kw_arg_vals = extract_init_arg_value_fn(varkw)
                for arg, val in kw_arg_vals.items():
                    yield (arg, val)
        except NotImplementedError:
            if (varkw is None): # and (operationClass.extractInitArgValue == Operation.extractInitArgValue):
                # try some default scenarios (that do not involve keyword arguments)
                # handle default implicit operator case
                if implicit_operator and ((len(args)==0 and varargs is not None) or \
                                            (len(args)==len(operands) and varargs is None)):
                    # yield each operand separately
                    for operand in operands:
                        yield operand
                    return
                
                # handle default explicit operator(s) case
                if (not implicit_operator) and (varkw is None):
                    if varargs is None and len(args)==2: 
                        # assume one argument for the operator(s) and one argument for the operand(s)
                        yield operator_or_operators
                        yield operand_or_operands
                        return
                    elif (varargs is not None and len(args)==1) or (len(args)==len(operands)+1 and varargs is None):
                        # yield the operator(s) and each operand separately
                        yield operator_or_operators
                        for operand in operands:
                            yield operand
                        return
                raise NotImplementedError("Must implement 'extractInitArgValue' for the Operation of type %s if it does not fall into one of the default cases for 'extractInitArgs'"%str(operationClass))

    @classmethod
    def _make(operationClass, coreInfo, styles, subExpressions):
        '''
        Make the appropriate Operation.  coreInfo should equal ['Operation'].  The first 
        of the subExpressions should be the operator(s) and the second should be the
        operand(s).  This implementation expects the Operation sub-class to have a
        class variable named '_operator_' that defines the Literal operator
        of the class.  It will instantiate the Operation sub-class with just *operands 
        and check that the operator is consistent.  Override this method
        if a different behavior is desired.
        '''
        if len(coreInfo) != 1 or coreInfo[0] != 'Operation':
            raise ValueError("Expecting Operation coreInfo to contain exactly one item: 'Operation'")
        if len(subExpressions) == 0:
            raise ValueError('Expecting at least one subExpression for an Operation, for the operator')
        operator_or_operators, operand_or_operands = subExpressions[0], subExpressions[1]
        args = []
        kw_args = dict()
        for arg in operationClass._extractInitArgs(operator_or_operators, operand_or_operands):
            if isinstance(arg, Expression):
                args.append(arg)
            else: 
                kw, val = arg
                kw_args[kw] = val 
        made_operation = operationClass(*args, **kw_args)
        if styles is not None:
            made_operation.withStyles(**styles)
        return made_operation
    
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        for arg in self._extractMyInitArgs():
            yield arg

    def remakeWithStyleCalls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a 
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'withWrappingAt'
        and 'withJustification' calls.
        '''
        wrap_positions = self.wrapPositions()
        call_strs = []
        if len(wrap_positions) > 0:
            call_strs.append('withWrappingAt(' + ','.join(str(pos) for pos in wrap_positions) + ')')
        justification = self.getStyle('justification')
        if justification != 'center':
            call_strs.append('withJustification(' + justification + ')')
        return call_strs
    
    def string(self, **kwargs):
        if self.getStyle('operation')=='function' or not hasattr(self, 'operands'): # When there is a single operand, we must use the "function"-style formatting.
            return self.operator.string(fence=True) +  '(' + self.operand_or_operands.string(fence=False, subFence=False) + ')'            
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        if self.getStyle('operation')=='function' or not hasattr(self, 'operands'): # When there is a single operand, we must use the "function"-style formatting.
            return self.operator.latex(fence=True) +  r'\left(' + self.operand_or_operands.latex(fence=False, subFence=False) + r'\right)'
        return self._formatted('latex', **kwargs)
    
    def wrapPositions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        '''
        return [int(pos_str) for pos_str in self.getStyle('wrapPositions').strip('()').split(' ') if pos_str != '']
    
    def _formatted(self, formatType, **kwargs):
        '''
        Format the operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        
        '''
        if hasattr(self, 'operator'):
            return Operation._formattedOperation(formatType, self.operator, self.operands, 
                                                 wrapPositions=self.wrapPositions(), justification=self.getStyle('justification'), 
                                                 **kwargs)
        else:
            return Operation._formattedOperation(formatType, self.operators, self.operands, 
                                                 wrapPositions=self.wrapPositions(), justification=self.getStyle('justification'), 
                                                 **kwargs)
    
    @staticmethod
    def _formattedOperation(formatType, operatorOrOperators, operands, wrapPositions, justification, implicitFirstOperator=False, **kwargs):
        from proveit import Iter, ExprTuple, compositeExpression
        if isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operator = operatorOrOperators
            # Single operator case.
            # Different formatting when there is 0 or 1 element, unless it is an Iter
            if len(operands) < 2:
                if len(operands) == 0 or not isinstance(operands[0], Iter):
                    if formatType == 'string':
                        return '[' + operator.string(fence=True) +  '](' + operands.string(fence=False, subFence=False) + ')'
                    else:
                        return '\left[' + operator.latex(fence=True) +  r'\right]\left(' + operands.latex(fence=False, subFence=False) + r'\right)'
                    raise ValueError("Unexpected formatType: " + str(formatType))  
            fence =  kwargs.get('fence', False)
            subFence =  kwargs.get('subFence', True)
            do_wrapping = len(wrapPositions)>0
            formatted_str = ''
            formatted_str += operands.formatted(formatType, fence=fence, subFence=subFence, operatorOrOperators=operator, 
                                                wrapPositions=wrapPositions, justification=justification)
            return formatted_str
        else:
            operators = operatorOrOperators
            operands = compositeExpression(operands)
            # Multiple operator case.
            # Different formatting when there is 0 or 1 element, unless it is an Iter
            if len(operands) < 2:
                if len(operands) == 0 or not isinstance(operands[0], Iter):
                    raise OperationError("No defaut formatting with multiple operators and zero operands")
            fence =  kwargs['fence'] if 'fence' in kwargs else False
            subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
            do_wrapping = len(wrapPositions)>0
            formatted_str = ''
            if fence: formatted_str = '(' if formatType=='string' else  r'\left('
            if do_wrapping and formatType=='latex': 
                formatted_str += r'\begin{array}{%s} '%justification[0]
            formatted_str += operands.formatted(formatType, fence=False, subFence=subFence, operatorOrOperators=operators, implicitFirstOperator=implicitFirstOperator, wrapPositions=wrapPositions)
            if do_wrapping and formatType=='latex': 
                formatted_str += r' \end{array}'
            if fence: formatted_str += ')' if formatType=='string' else  r'\right)'
            return formatted_str            
            
    def substituted(self, repl_map, reserved_vars=None, 
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary.
        
        reserved_vars is used internally to protect the "scope" of a
        Lambda map.  For more details, see the Lambda.substitution
        documentation.
        
        When an operater of an Operation is substituted by a Lambda map, the 
        operation itself will be substituted with the Lambda map applied to the
        operands.  For example, substituting 
        f : (x,y) -> x+y
        on f(a, b) will result in a+b.  When performing operation
        substitution with iterated parameters, the Lambda map application
        will require the length of the iterated parameters to equal with 
        the number of corresponding operand elements.  For example,
        f : (a, b_1, ..., b_n) -> a*b_1 + ... + a*b_n
        n : 3
        applied to f(w, x, y, z) will result in w*x + w*y + w*z provided that
        |(b_1, ..., b_3)| = |(x, y, z)| is proven.
        Assumptions may be needed to prove such requirements.  Requirements
        will be appended to the 'requirements' list if one is provided.
        
        There are limitations with respect the Lambda map application involving
        iterated parameters when perfoming operation substitution in order to
        keep derivation rules (i.e., instantiation) simple.  For details,
        see the Iter.substituted documentation.
        '''
        from proveit import Lambda, compositeExpression
        
        # Check reserved variable restrictions for scoping volations.
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]._restrictionChecked(reserved_vars)      
        
        # Perform substitutions for the operator(s) and operand(s).
        subbed_operator_or_operators = \
            self.operator_or_operators.substituted(repl_map, reserved_vars, 
                                                   assumptions, requirements)
        subbed_operators = compositeExpression(subbed_operator_or_operators)
        subbed_operand_or_operands = \
            self.operand_or_operands.substituted(repl_map, reserved_vars, 
                                                 assumptions, requirements)
        
        # Check if the operator is being substituted by a Lambda map in which
        # case we should perform full operation substitution.
        if len(subbed_operators)==1:
            subbed_operator = subbed_operators[0]
            if isinstance(subbed_operator, Lambda):
                # Substitute the entire operation via a Lambda map
                # application.  For example, f(x, y) -> x + y,
                # or g(a, b_1, ..., b_n) -> a * b_1 + ... + a * b_n.
                
                subbed_op_lambda = subbed_operator
                if not reserved_vars is None:
                    # The reserved variables of the lambda body excludes the 
                    # lambda parameters (i.e., the parameters mask externally 
                    # reserved variables).
                    lambda_expr_res_vars = \
                        {k:v for k, v in reserved_vars.items() 
                         if k not in subbed_op_lambda.parameterVarSet}
                else: 
                    lambda_expr_res_vars = None
                subbed_operator_body = subbed_op_lambda.body
                subbed_operator_body._restrictionChecked(lambda_expr_res_vars)
                subbed_operands = \
                    compositeExpression(subbed_operand_or_operands)

                return subbed_operator.apply(*subbed_operands, 
                                             assumptions=assumptions, 
                                             requirements=requirements)
        
        # Remake the Expression with substituted operator and/or operands
        if len(subbed_operators)==1:
            # If it is a single operator that is a literal operator of an 
            # Operation class  defined via an "_operator_" class attribute, 
            # then create the Operation of that class.
            operator = subbed_operators[0]
            if operator in Operation.operationClassOfOperator:
                op_class = Operation.operationClassOfOperator[operator]
                if op_class != self.__class__:
                    # Don't transfer the styles; they may not apply in the same 
                    # manner in the setting of the new operation.
                    return op_class._make(['Operation'], styles=None, 
                                          subExpressions=[operator, 
                                                          subbed_operand_or_operands])
        return self.__class__._make(self._coreInfo, self.getStyles(), 
                                    [subbed_operator_or_operators, 
                                     subbed_operand_or_operands])

    
class OperationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
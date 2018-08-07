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
    
    def __init__(self, operator_or_operators, operand_or_operands, styles=dict(), requirements=tuple()):
        '''
        Create an operation with the given operator(s) and operand(s).
        The operator(s) must be Label(s) (a Variable or a Literal).
        When there is a single operator, there will be an 'operator'
        attribute.  When there is a single operand, there will be
        an 'operand' attribute.  In any case, there will be
        'operators' and 'operands' attributes that bundle
        the one or more Expressions into a composite Expression.
        '''
        from proveit._core_.expression.composite import Composite, compositeExpression, singleOrCompositeExpression, Iter, Indexed
        from proveit._core_.expression.label.label import Label
        from proveit import Context
        if hasattr(self.__class__, '_operator_') and operator_or_operators==self.__class__._operator_:
            operator = operator_or_operators
            context = Context(inspect.getfile(self.__class__))
            if Expression.contexts[operator] != context:
                raise OperationError("Expecting '_operator_' Context to match the Context of the Operation sub-class.  Use 'context=__file__'.")
        self.operator_or_operators = singleOrCompositeExpression(operator_or_operators)
        self.operand_or_operands = singleOrCompositeExpression(operand_or_operands)
        if isinstance(self.operator_or_operators, Composite):
            # a composite of multiple operators:
            self.operators = self.operator_or_operators 
            for operator in self.operators:
                if isinstance(operator, Iter):
                    if not isinstance(operator.lambda_map.body, Indexed):
                        raise TypeError('operators must be Labels, Indexed variables, or iteration (Iter) over Indexed variables.')                
                elif not isinstance(operator, Label) and not isinstance(operator, Indexed):
                    raise TypeError('operator must be a Label, Indexed variable, or iteration (Iter) over Indexed variables.')
        else:
            # a single operator
            self.operator = self.operator_or_operators
            if not isinstance(self.operator, Label) and not isinstance(self.operator, Indexed):
                raise TypeError('operator must be a Label, Indexed variable, or iteration (Iter) over Indexed variables.')
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
        Expression.__init__(self, ['Operation'], [self.operator_or_operators, self.operand_or_operands], styles=styles, requirements=requirements)

    def styleOptions(self):
        options = StyleOptions(self)
        options.addOption('wrapPositions', "position(s) at which wrapping is to occur; '2 n - 1' is after the nth operand, '2 n' is after the nth operation.")
        options.addOption('justification', "if any wrap positions are set, justify to the 'left', 'center', or 'right'")
        return options

    def withWrappingAt(self, *wrapPositions):
        return self.withStyles(wrapPositions='(' + ','.join(str(pos) for pos in wrapPositions) + ')')
    
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

    @staticmethod
    def extractInitArgValue(argName, operator_or_operators, operand_or_operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        
        Override this method if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        raise NotImplementedError("'extractInitArgValue' must be appropriately implemented if __init__ arguments do not fall into a simple 'default' scenario")
    
    @classmethod
    def _extractInitArgs(operationClass, operator_or_operators, operand_or_operands):
        '''
        For a particular Operation class and given operator(s) and operand(s),
        yield (name, value) pairs to pass into the initialization method
        for creating the operation consistent with the given operator(s) and operand(s).
        
        First attempt to call 'extractInitArgValue' for each of the __init__
        arguments to determine how to generate the appropriate __init__ parameters
        from the given operators and operands.  If that is not implemented,
        fall back to one of the following default scenarios.
        
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
        implicit_operator = (operator_or_operators == operationClass._implicitOperator())
        operands = compositeExpression(operand_or_operands)
        args, varargs, varkw, defaults = inspect.getargspec(operationClass.__init__)
        args = args[1:] # skip over the 'self' arg
        if len(args)>0 and args[-1]=='requirements':
            args = args[:-1] # NOT TREATING 'requirements' FULLY AT THIS TIME; THIS NEEDS WORK.
        if len(args)>0 and args[-1]=='styles':
            args = args[:-1] # NOT TREATING 'styles' FULLY AT THIS TIME; THIS NEEDS WORK.
        
        try:
            arg_vals = [operationClass.extractInitArgValue(arg, operator_or_operators, operand_or_operands) for arg in args]
            if varargs is not None:
                arg_vals += operationClass.extractInitArgValue(varargs, operator_or_operators, operand_or_operands)
            if defaults is None: defaults = []
            for k, (arg, val) in enumerate(zip(args, arg_vals)):
                if len(defaults)-len(args)+k >= 0:
                    if val == defaults[len(defaults)-len(args)+k]:
                        continue # using the default value
                yield (arg, val)
            if varkw is not None:
                kw_arg_vals = operationClass.extractInitArgValue(varkw, operator_or_operators, operand_or_operands)
                for arg, val in kw_arg_vals.iteritems():
                    yield (arg, val)
        except NotImplementedError:
            if (varkw is None) and (operationClass.extractInitArgValue == Operation.extractInitArgValue):
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
        from proveit._core_.expression.composite.composite import compositeExpression
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
        return operationClass(*args, **kw_args).withStyles(**styles)
    
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        operationClass = self.__class__
        for arg in operationClass._extractInitArgs(self.operator_or_operators, self.operand_or_operands):
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
        return [int(pos_str) for pos_str in self.getStyle('wrapPositions').strip('()').split(',') if pos_str != '']
    
    def _formatted(self, formatType, **kwargs):
        '''
        Format the operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        
        '''
        from proveit import Iter
        if not hasattr(self, 'operator'):
            raise OperationError("No default formatting for a multi-operator Operation; see OperationSequence")
        # Different formatting when there is 0 or 1 element, unless it is an Iter
        if len(self.operands) < 2:
            if len(self.operands) == 0 or not isinstance(self.operands[0], Iter):
                if formatType == 'string':
                    return '[' + self.operator.string(fence=True) +  '](' + self.operands.string(fence=False, subFence=False) + ')'
                else:
                    return '\left[' + self.operator.latex(fence=True) +  r'\right]\left(' + self.operands.latex(fence=False, subFence=False) + r'\right)'
                raise ValueError("Unexpected formatType: " + str(formatType))  
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
        formattedOperator = self.operator.formatted(formatType)
        wrap_positions = self.wrapPositions()
        do_wrapping = len(wrap_positions)>0
        formatted_str = ''
        if fence: formatted_str = '(' if formatType=='string' else  r'\left('
        if do_wrapping and formatType=='latex': 
            formatted_str += r'\begin{array}{%s} '%self.getStyle('justification')[0]
        formatted_str += self.operands.formatted(formatType, fence=False, subFence=subFence, formattedOperator=formattedOperator, wrapPositions=wrap_positions)
        if do_wrapping and formatType=='latex': 
            formatted_str += r' \end{array}'
        if fence: formatted_str += ')' if formatType=='string' else  r'\right)'
        return formatted_str

    def _formatMultiOperator(self, formatType, **kwargs):
        '''
        When there are multiple operators, the default formatting assumes there is one more operator than operands
        and the operators should come between successive operands.
        '''
        if len(self.operators)+1 != len(self.operands):
            raise NotImplementedError("Default formatting for multiple operators only applies when there is one more operand than operators")
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
        formatted_operators = [operator.formatted(formatType) for operator in self.operators]
        formatted_operands = [operand.formatted(formatType, fence=subFence) for operand in self.operands]
        inner_str = ' '.join(formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in zip(formatted_operands, formatted_operators)) + ' ' + formatted_operands[-1]
        return maybeFenced(formatType, inner_str, fence=fence)
            
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from proveit._core_.expression.composite.composite import compositeExpression
        from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        subbed_operand_or_operands = self.operand_or_operands.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        subbed_operands = compositeExpression(subbed_operand_or_operands)
        subbed_operator_or_operators = self.operator_or_operators.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        subbed_operators = compositeExpression(subbed_operator_or_operators)
        if len(subbed_operators)==1:
            subbedOperator = subbed_operators[0]
            if isinstance(subbedOperator, Lambda):
                # Substitute the entire operation via a Lambda body
                # For example, f(x, y) -> x + y.
                if len(subbed_operands) != len(subbedOperator.parameters):
                    raise ImproperSubstitution('Cannot substitute an Operation with the wrong number of parameters')
                operandSubMap = {param:operand for param, operand in zip(subbedOperator.parameters, subbed_operands)}
                if not reservedVars is None:
                    # the reserved variables of the lambda body excludes the lambda parameters
                    # (i.e., the parameters mask externally reserved variables).
                    lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if k not in subbedOperator.parameterSet}
                else: lambdaExprReservedVars = None
                return subbedOperator.body._restrictionChecked(lambdaExprReservedVars).substituted(operandSubMap, assumptions=assumptions, requirements=requirements)
        # remake the Expression with substituted operator and/or operands
        if len(subbed_operators)==1:
            # If it is a single operator that is a literal operator of an Operation class
            # defined via an "_operator_" class attribute, then create the Operation of that class.
            operator = subbed_operators[0]
            if operator in Operation.operationClassOfOperator:
                OperationClass = Operation.operationClassOfOperator[operator]
                return OperationClass._make(['Operation'], self.getStyles(), [operator, subbed_operand_or_operands])
        return self.__class__._make(['Operation'], self.getStyles(), [subbed_operator_or_operators, subbed_operand_or_operands])
    
    def _expandingIterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        # Collect the iteration ranges for all of the operators and operands.
        iter_ranges = set()
        for iter_range in self.operator_or_operators._expandingIterRanges(iterParams, startArgs, endArgs, exprMap, relabelMap, reservedVars, assumptions, requirements):
            iter_ranges.add(iter_range)
        for iter_range in self.operand_or_operands._expandingIterRanges(iterParams, startArgs, endArgs, exprMap, relabelMap, reservedVars, assumptions, requirements):
            iter_ranges.add(iter_range)
        for iter_range in iter_ranges:
            yield iter_range            
    
class OperationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
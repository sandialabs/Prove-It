import inspect
from proveit._core_.expression.expr import Expression, ImproperSubstitution
from proveit._core_.defaults import USE_DEFAULTS

class Operation(Expression):
    # map _operator_ Literals to corresponding Operation classes
    operationClassOfOperator = dict()
    
    def __init__(self, operator_or_operators, operand_or_operands):
        '''
        Create an operation with the given operator(s) and operand(s).
        The operator(s) must be Label(s) (a Variable or a Literal).
        When there is a single operator, there will be an 'operator'
        attribute.  When there is a single operand, there will be
        an 'operand' attribute.  In any case, there will be
        'operators' and 'operands' attributes that bundle
        the one or more Expressions into a composite Expression.
        '''
        from proveit._core_.expression.composite.composite import Composite, compositeExpression, singleOrCompositeExpression
        from proveit._core_.expression.label.label import Label
        from proveit import Context
        if hasattr(self.__class__, '_operator_') and operator_or_operators==self.__class__._operator_:
            operator = operator_or_operators
            context = Context(inspect.getfile(self.__class__))
            if Expression.contexts[operator] != context:
                raise OperationError("Expecting '_operator_' Context to match the Context of the Operation sub-class.  Use 'context=__file__'.")
            Operation.operationClassOfOperator[operator] = self.__class__
        self.operator_or_operators = singleOrCompositeExpression(operator_or_operators)
        self.operand_or_operands = singleOrCompositeExpression(operand_or_operands)
        if isinstance(self.operator_or_operators, Composite):
            # a composite of multiple operators:
            self.operators = self.operator_or_operators 
            for operator in self.operators:
                if not isinstance(operator, Label):
                    raise TypeError('operator must be a Label-type Expression')
        else:
            # a single operator
            self.operator = self.operator_or_operators
            if not isinstance(self.operator, Label):
                raise TypeError('operator must be a Label-type Expression')
            # wrap a single operator in a composite for convenience
            self.operators = compositeExpression(self.operator)
        if isinstance(self.operator_or_operators, Composite):
            # a composite of multiple operands
            self.operands = self.operand_or_operands
        else:
            # a single operand
            self.operand = self.operand_or_operands
            # wrap a single operand in a composite for convenience
            self.operands = compositeExpression(self.operand)
        Expression.__init__(self, ['Operation'], [self.operator_or_operators, self.operand_or_operands])
    
    @classmethod
    def _implicitOperator(operationClass):
        if hasattr(operationClass, '_operator_'):
            return operationClass._operator_
        return None

    @staticmethod
    def extractInitArgValue(argName, operators, operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        
        Override this method if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        raise NotImplementedError("'extractInitArgValue' must be appropriately implemented if __init__ arguments do not fall into a simple 'default' scenario")
    
    @classmethod
    def _extractInitArgs(operationClass, operators, operands):
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
        implicit_operator = (len(operators)==1 and operators[0] == operationClass._implicitOperator())
        args, varargs, varkw, defaults = inspect.getargspec(operationClass.__init__)
        args = args[1:] # skip over the 'self' arg
        
        try:
            arg_vals = [operationClass.extractInitArgValue(arg, operators, operands) for arg in args]
            if varargs is not None:
                arg_vals += operationClass.extractInitArgValue(varargs, operators, operands)
            if defaults is None: defaults = []
            for k, (arg, val) in enumerate(zip(args, arg_vals)):
                if len(defaults)-len(args)+k >= 0:
                    if val == defaults[len(defaults)-len(args)+k]:
                        continue # using the default value
                yield (arg, val)
            if varkw is not None:
                kw_arg_vals = operationClass.extractInitArgValue(varkw, operators, operands)
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
                        yield operators[0] if len(operators)==1 else operators
                        yield operands[0] if len(operands)==1 else operands
                        return
                    elif (varargs is not None and len(args)==1) or (len(args)==len(operands)+1 and varargs is None):
                        # yield the operator(s) and each operand separately
                        yield operators[0] if len(operators)==1 else operators
                        for operand in operands:
                            yield operands
                        return
                raise NotImplementedError("Must implement 'extractInitArgValue' for the particular Operation if it does not fall into one of the default cases for 'extractInitArgs'")
        

    @classmethod
    def make(operationClass, coreInfo, subExpressions):
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
        # wrap even singular expressions as composites for convenience (1 size fits all)
        operators, operands = compositeExpression(subExpressions[0]), compositeExpression(subExpressions[1])
        args = []
        kw_args = dict()
        for arg in operationClass._extractInitArgs(operators, operands):
            if isinstance(arg, Expression):
                args.append(arg)
            else: 
                kw, val = arg
                kw_args[kw] = val 
        return operationClass(*args, **kw_args)
    
    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        operationClass = self.__class__
        for arg in operationClass._extractInitArgs(self.operators, self.operands):
            yield arg
    
    def string(self, **kwargs):
        if not hasattr(self, 'operator'):
            return self._formatMultiOperator('string', **kwargs)
        return self.operator.string(fence=True) +  '(' + self.operands.string(fence=False, subFence=False) + ')'
    
    def latex(self, **kwargs):
        if not hasattr(self, 'operator'):
            return self._formatMultiOperator('latex', **kwargs)
        return self.operator.latex(fence=True) +  r'\left(' + self.operands.latex(fence=False, subFence=False) + r'\right)'

    def _formatMultiOperator(self, formatType, **kwargs):
        '''
        When there are multiple operators, the default formatting assumes there is one more operator than operands
        and the operators should come between successive operands.
        '''
        from proveit._generic_ import maybeFenced
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
        from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        subbed_operands = self.operands.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        subbed_operators = self.operators.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
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
        return self.__class__.make(['Operation'], [subbed_operators, subbed_operands])
    
    def iterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        subbed_operands = self.operands.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        
        # Collect the iteration ranges for all of the operands.
        iter_ranges = set()
        for operand in subbed_operands:
            for iter_range in operand.iterRanges(iterParams, startArgs, endArgs, exprMap, relabelMap, reservedVars, assumptions, requirements):
                iter_ranges.add(iter_range)
        
        for iter_range in iter_ranges:
            yield iter_range            

    def usedVars(self):
        '''
        Returns the union of the operator and operands used variables.
        '''
        return self.operators.usedVars().union(self.operands.usedVars())
        
    def freeVars(self):
        '''
        Returns the union of the operator and operands free variables.
        '''
        return self.operators.freeVars().union(self.operands.freeVars())
    
class OperationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
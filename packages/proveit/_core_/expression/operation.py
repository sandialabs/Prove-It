import inspect
from expr import Expression, ImproperSubstitution

class Operation(Expression):
    # map _operator_ Literals to corresponding Operation classes
    operationClassOfOperator = dict()
    
    def __init__(self, operator, operands):
        '''
        Create an operation with the given operator and operands.  The operator must be
        a Label (such as a Variable or a Literal).  The operands may be single expression that 
        will be then be wrapped by ExpressionList.
        '''
        from composite.composite import compositeExpression
        from label.label import Label
        from proveit import Context
        if hasattr(self.__class__, '_operator_') and operator==self.__class__._operator_:
            context = Context(inspect.getfile(self.__class__))
            if operator.context != context:
                raise OperationError("Expecting '_operator_' Context to match the Context of the Operation sub-class.  Use 'context=__file__'.")
            Operation.operationClassOfOperator[operator] = self.__class__
        if not isinstance(operator, Label):
            raise TypeError('operator must be a Label-type Expression')
        self.operator = operator
        self.operands = compositeExpression(operands)
        Expression.__init__(self, ['Operation'], [self.operator, self.operands])
    
    @classmethod
    def _implicitOperator(operationClass):
        if hasattr(operationClass, '_operator_'):
            return operationClass._operator_
        return None

    @staticmethod
    def extractInitArgValue(argName, operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        
        Override this method if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        raise Exception("'extractInitArgValue' must be appropriately implemented if __init__ arguments do not fall into a simple 'default' scenario")
    
    @classmethod
    def _extractInitArgs(operationClass, operator, operands):
        '''
        For a particular Operation class and given an operator and operands,
        yield (name, value) pairs to pass into the initialization method
        for creating the operation consistent with the given operator and operands.
        '''
        implicit_operator = (operator == operationClass._implicitOperator())
        args, varargs, varkw, defaults = inspect.getargspec(operationClass.__init__)
        args = args[1:] # skip over the 'self' arg
        
        if (varkw is None) and (operationClass.extractInitArgValue == Operation.extractInitArgValue):
            # try some default scenarios (that do not involve keyword arguments
            
            # handle default implicit operator case
            if implicit_operator and ((len(args)==0 and varargs is not None) or \
                                        (len(args)==len(operands) and varargs is None)):
                # yield each operand separately
                for operand in operands:
                    yield operand
                return
            
            # handle default explicit operator case
            if (not implicit_operator) and (varkw is None):
                if varargs is None and len(args)==2: 
                    # yield the operator and the operands as one
                    yield operator
                    yield operands
                    return
                if (varargs is not None and len(args)==1) or (len(args)==len(operands) and varargs is None):
                    # yield the operator and each operand separately
                    yield operator
                    for operand in operands:
                        yield operands
                    return
        
        arg_vals = [operationClass.extractInitArgValue(arg, operands) for arg in args]
        if varargs is not None:
            arg_vals += operationClass.extractInitArgValue(varargs, operands)
        if defaults is None: defaults = []
        supplied_operator = False
        for k, (arg, val) in enumerate(zip(args, arg_vals)):
            if len(defaults)-len(args)+k >= 0:
                if val == defaults[len(defaults)-len(args)+k]:
                    continue # using the default value
            if not implicit_operator and val is None:
                if supplied_operator:
                     raise Exception("Expecting 'extractInitArgValue' to assign the operator, and only the operator, to None (except when there is a default of None)"%operationClass)
                val = operator
                supplied_operator = True
            yield (arg, val)
        if not implicit_operator and not supplied_operator: 
            raise Exception("Expecting one 'operator' argument that 'extractInitArgValue' assigns to None (for %s)"%operationClass)
        if varkw is not None:
            kw_arg_vals = operationClass.extractInitArgValue(varkw, operands)
            for arg, val in kw_arg_vals.iteritems():
                yield (arg, val)

    @classmethod
    def make(operationClass, coreInfo, subExpressions):
        '''
        Make the appropriate Operation.  coreInfo should equal ['Operation'].  The first 
        of the subExpressions should be the operator and the subsequent ones should be 
        operands.  This implementation expects the Operation sub-class to have a
        class variable named '_operator_' that defines the Literal operator
        of the class.  It will instantiate the Operation sub-class with just *operands 
        and checking that the operator is consistent.  Override this method
        if a different behavior is desired.
        '''
        if len(coreInfo) != 1 or coreInfo[0] != 'Operation':
            raise ValueError("Expecting Operation coreInfo to contain exactly one item: 'Operation'")
        if len(subExpressions) == 0:
            raise ValueError('Expecting at least one subExpression for an Operation, for the operator')
        operator, operands = subExpressions[0], subExpressions[1]
        args = []
        kw_args = dict()
        for arg in operationClass._extractInitArgs(operator, operands):
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

        for arg in operationClass._extractInitArgs(self.operator, self.operands):
            yield arg
    
    def string(self, **kwargs):
        return self.operator.string(fence=True) +  '(' + self.operands.string(fence=False, subFence=False) + ')'
    
    def latex(self, **kwargs):
        return self.operator.latex(fence=True) +  r'\left(' + self.operands.latex(fence=False, subFence=False) + r'\right)'
                
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Return this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from lambda_expr import Lambda
        from label import MultiVariable
        from bundle import Etcetera
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        subbedOperands = self.operands.substituted(exprMap, relabelMap, reservedVars)
        subbedOperator = self.operator.substituted(exprMap, relabelMap, reservedVars)
        # Performing an operation substitution where the operation takes a single MultiVariable parameter
        # is treated as a special case
        performingMultiVarOperationSub = False
        if isinstance(subbedOperator, Lambda):
            if any(isinstance(param, MultiVariable) for param in subbedOperator.parameters):
                if len(subbedOperator.parameters) != 1:
                    raise ImproperSubstitution('Only a single MultiVariable parameter is allowed in the specification of operation substitution to avoid ambiguity')
                performingMultiVarOperationSub = True
        # Except when performing a MultiVariable operation substitution,
        # not allowed to substitute the operator or operation if there are Etcetera operands
        # because the number of operands should not be indeterminate when performing such a substition.
        if not performingMultiVarOperationSub:
            for subbedOperand in subbedOperands:
                if isinstance(subbedOperand, Etcetera):
                    if subbedOperator != self.operator:
                        raise Exception('Not allowed to perform a non-MultiVariable Operation substition with any remaining Etcetera operands because the number of operands should be determined when substititing the operation.')
        if isinstance(subbedOperator, Lambda):
            # Substitute the entire operation via a Lambda body
            # For example, f(x, y) -> x + y.
            if performingMultiVarOperationSub: # operation takes a single MultiVariable parameter
                operandSubMap = {subbedOperator.parameters[0] : subbedOperands}
            else:
                if len(subbedOperands) != len(subbedOperator.parameters):
                    raise ImproperSubstitution('Cannot substitute an Operation with the wrong number of parameters')
                operandSubMap = {param:operand for param, operand in zip(subbedOperator.parameters, subbedOperands)}
            if not reservedVars is None:
                # the reserved variables of the lambda body excludes the lambda parameters
                # (i.e., the parameters mask externally reserved variables).
                lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if k not in subbedOperator.parameterSet}
            else: lambdaExprReservedVars = None
            return subbedOperator.body._restrictionChecked(lambdaExprReservedVars).substituted(operandSubMap, None)
        # remake the Expression with substituted operator and/or operands
        return self.__class__.make(['Operation'], [subbedOperator, subbedOperands])

    def usedVars(self):
        '''
        Returns the union of the operator and operands used variables.
        '''
        return self.operator.usedVars().union(self.operands.usedVars())
        
    def freeVars(self):
        '''
        Returns the union of the operator and operands free variables.
        '''
        return self.operator.freeVars().union(self.operands.freeVars())
    
    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        return self.operator.freeMultiVars().union(self.operands.freeMultiVars())

class OperationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
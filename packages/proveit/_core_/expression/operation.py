import inspect
from expr import Expression, ImproperSubstitution

class Operation(Expression):    
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
        if not isinstance(operator, Label):
            raise TypeError('operator must be a Label-type Expression')
        self.operator = operator
        self.operands = compositeExpression(operands)
        Expression.__init__(self, ['Operation'], [self.operator, self.operands])

    @staticmethod
    def extractInitArgValue(argName, argIndex, operands):
        '''
        Given a name of one of the arguments of the __init__ method,
        return the corresponding value contained in the 'operands'
        composite expression (i.e., the operands of a constructed operation).
        
        Override this method if you cannot simply pass the operands directly
        into the __init__ method.
        '''
        return None

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
        import inspect
        if len(coreInfo) != 1 or coreInfo[0] != 'Operation':
            raise ValueError("Expecting Operation coreInfo to contain exactly one item: 'Operation'")
        if len(subExpressions) == 0:
            raise ValueError('Expecting at least one subExpression for an Operation, for the operator')
        operator, operands = subExpressions[0], subExpressions[1]
        
        if operationClass != Operation: 
            try:
                subClassOperator = operationClass._operator_
            except:
                raise OperationError("Operation sub-class is expected to have a class variable named '_operator_'")
            if subClassOperator != operator:
                raise ValueError('Unexpected operator, ' + str(operator) + ', when making ' + str(operationClass)) 
            if operationClass.extractInitArgValue == Operation.extractInitArgValue:
                # By default, simply pass the operands directly into the __init__ method.
                return operationClass(*operands)
            else:       
                # If extractInitArgValue is overridden, use it to determine how to pass
                # the arguments into the __init__ method based upon the operands object.
                args, varargs, varkw, defaults = inspect.getargsspec(operationClass.__init__)
                argVals = [operationClass.extractInitArgValue(arg, operands) for arg in args]
                if varargs is not None:
                    argVals += operationClass.extractInitArgValue(varargs, operands)
                kwArgVals = dict()
                if varkw is not None:
                    kwArgVals = operationClass.extractInitArgValue(varkw, operands)
                return operationClass(*argVals, **kwArgVals)
        return Operation(operator, operands)
    
    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Operation.
        '''
        from proveit import Literal
        import inspect
        operands = self.operands
        operationClass = self.__class__
        
        if hasattr(operationClass, '_operator_') and isinstance(operationClass._operator_, Literal):
            # The operationClass is for an Operation with a specific literal operator
            if hasattr(operationClass, 'extractInitArgValue') and operationClass.extractInitArgValue != Operation.extractInitArgValue:
                operands = self.operands
                args, varargs, varkw, defaults = inspect.getargsspec(operationClass.__init__)
                argVals = [operationClass.extractInitArgValue(arg, operands) for arg in args]
                if varargs is not None:
                    argVals += operationClass.extractInitArgValue(varargs, operands)
                for argVal, default in zip(reversed(argVals), reversed(defaults)):
                    if argVal != default: break # not the same as a default so everything before it must be explicitly specified
                    argVals.pop(-1) # don't need this last argVal because it is the same as the default
                for arg, val in zip(args, argVals):
                    yield (arg, val)
                if varkw is not None:
                    kwArgVals = operationClass.extractInitArgValue(varkw, operands)
                    for arg, val in kwArgVals.iteritems():
                        yield (arg, val)
            else:
                for operand in operands:
                    yield operand
        else:
            # An Operation with no specific literal operator
            yield self.operator
            yield self.operands
    
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
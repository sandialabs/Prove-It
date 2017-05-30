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

    @classmethod
    def make(operationClass, coreInfo, subExpressions):
        '''
        Make the appropriate Operation.  coreInfo should equal ['Operation'].  The first 
        of the subExpressions should be the operator and the subsequent ones should be 
        operands.  This implementation expects that the Operation sub-class to have a
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
        if operationClass != Operation: 
            try:
                subClassOperator = operationClass._operator_
            except:
                raise OperationError("Operation sub-class is expected to have a class variable named '_operator_'")
            if subClassOperator != operator:
                raise ValueError('Unexpected operator, ' + str(operator) + ', when making ' + str(operationClass)) 
            return operationClass(*operands)
        return Operation(operator, operands)

    @classmethod
    def operatorOfOperation(subClass):
        '''
        For Operation sub-classes that use a specific Literal operator, override this to return
        that specific Literal.  Then the default 'make' method will then work my instantiating
        the Operation sub-class with just the operands (and checking that the operator is
        consistent).
        '''
        raise NotImplementedError("operatorOfOperation not implemented. Cannot use default make method.")
    
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
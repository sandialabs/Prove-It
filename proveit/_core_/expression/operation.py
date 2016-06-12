from expr import Expression, ImproperSubstitution

class Operation(Expression):    
    def __init__(self, operator, operands):
        '''
        Create an operation with the given operator and operands.  The operator can be a 
        Label or Lambda function.  The operands may be single expression that
        will be then be wrapped by ExpressionList.
        '''
        from composite.composite import compositeExpression
        from label.label import Label
        from lambda_expr import Lambda
        if not isinstance(operator, Label):
            raise TypeError('operator must be a Label-type Expression')
        self.operator = operator
        self.operands = compositeExpression(operands)
        if isinstance(operator, Lambda):
            if len(self.operands) != len(operator.arguments):
                raise ValueError("Number of arguments and number of operands must match.")
        Expression.__init__(self, ['Operation'], [self.operator, self.operands])

    @classmethod
    def make(operationClass, coreInfo, subExpressions):
        '''
        Make the appropriate Operation.  coreInfo should equal ['Operation'].  The first 
        of the subExpressions should be the operator and the subsequent ones should be 
        operands.  For Operation sub-classes that use a specific Literal operator, override
        'operatorOfOperation' and the default behavior of 'make' will be to 
        instantiate the Operation sub-class with just *operands (and checking that
        the operator is consistent).  Override this method for any other behavior.
        '''
        if len(coreInfo) != 1 or coreInfo[0] != 'Operation':
            raise ValueError("Expecting Operation coreInfo to contain exactly one item: 'Operation'")
        if len(subExpressions) == 0:
            raise ValueError('Expecting at least one subExpression for an Operation, for the operator')
        operator, operands = subExpressions[0], subExpressions[1]
        if operationClass != Operation: 
            subClassOperator = operationClass.operatorOfOperation()
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
        from bundle import extractVar, Etcetera
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        operator = self.operator
        subbedOperands = self.operands.substituted(exprMap, relabelMap, reservedVars)
        subbedOperator = self.operator.substituted(exprMap, relabelMap, reservedVars)
        # Not allowed to substitute the operator or operation if there are Etcetera operands
        # because the number of operands should not be indeterminate when performing such a substition.
        for subbedOperand in subbedOperands:
            if isinstance(subbedOperand, Etcetera):
                if subbedOperator != operator:
                    raise Exception('Not allowed to perform an Operation substition with any remaining Etcetera operands because the number of operands should be determined when substititing the operation.')
        if isinstance(subbedOperator, Lambda):
            # Substitute the entire operation via a Lambda expression
            # For example, f(x, y) -> x + y.
            if len(subbedOperands) != len(subbedOperator.arguments):
                raise ImproperSubstitution('Cannot substitute an Operation with the wrong number of arguments')
            operandSubMap = {argument:operand for argument, operand in zip(subbedOperator.arguments, subbedOperands)}
            if not reservedVars is None:
                # the reserved variables of the lambda expression excludes the lambda arguments
                # (i.e., the arguments mask externally reserved variables).
                lambdaExprReservedVars = {k:v for k, v in reservedVars.iteritems() if extractVar(k) not in subbedOperator.argVarSet}
            else: lambdaExprReservedVars = None
            return subbedOperator.expression._restrictionChecked(lambdaExprReservedVars).substituted(operandSubMap, None)
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

from proveit.core.expression.expr import Expression, MakeNotImplemented, ImproperSubstitution, ImproperRelabeling

class Lambda(Expression):
    '''
    A lambda-function expr.  A lambda function maps arguments to
    an expression.  The arguments is an expr_list with each of its
    expressions being either a Variable or a Bundled Variable 
    (see multiExpression.py).  For example, (x, y) -> sin(x^2 + y).
    '''
    def __init__(self, arguments, expression):
        '''
        Initialize a Lambda expression given arguments and an expression.
        Each argument in arguments must be a Variable or a Bundled Variable.
        arguments may be an iterable of these or a single one that will be 
        wrapped by expr_list.
        '''
        from composite import ExpressionList, singleOrCompositeExpression
        from bundle.bundle import Bundle, isBundledVarOrVar, extractVar
        self.arguments = arguments if isinstance(arguments, ExpressionList) else ExpressionList(arguments)
        for var in self.arguments:
            if not isBundledVarOrVar(var):
                raise TypeError('Each element of the Lambda arguments must be a Variable or Bundled Variable')
        self.argVarSet = {extractVar(arg) for arg in self.arguments}
        if len(self.argVarSet) != len(self.arguments):
            raise ValueError('Lambda argument Variables must be unique with respect to each other.')
        expression = singleOrCompositeExpression(expression)
        if not isinstance(expression, Expression):
            raise TypeError('A Lambda expression must be of type Expression')
        if isinstance(expression, Bundle):
            raise TypeError('A Bundle must be within an ExpressionTensor or exprlist, not directly as a Lambda expression')
        self.expression = expression
        Expression.__init__(self, ['Lambda'], [self.arguments, self.expression])
        
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Lambda':
            raise ValueError("Expecting Lambda coreInfo to contain exactly one item: 'Lambda'")
        if subClass != Lambda: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions) != 2:
            raise ValueError('Expecting two subExpressions for a Lambda, not ' + str(len(subExpressions)))
        arguments, expression = subExpressions[0], subExpressions[1]
        return Lambda(arguments, expression)

    def string(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        outStr += '(' + ', '.join([var.string() for var in self.arguments]) + ') -> '
        outStr += self.expression.string()
        if fence: outStr += ']'
        return outStr
    
    def latex(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = r'\left[' if fence else ''
        outStr += r'\left(' + ', '.join([var.latex() for var in self.arguments]) + r'\right) \rightarrow '
        outStr += self.expression.latex()
        if fence: outStr += r'\right]'
        return outStr
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Return this expression with its variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        The Lambda argument(s) have their own scope within the Lambda 
        expression or domainCondition and do not get substituted.  They may be
        relabeled, however.  Substitutions within the Lambda expression are 
        restricted to exclude the Lambda argument(s) themselves (these Variables 
        are reserved), consistent with any relabeling.
        '''
        from composite import ExpressionList, NestedCompositeExpressionError
        from proveit.core.expression.bundle import extractVar
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)        
        # Can't substitute the lambda argument variables; they are in a new scope.
        innerExprMap = {key:value for (key, value) in exprMap.iteritems() if extractVar(key) not in self.argVarSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        try:
            newArgs = self.arguments.relabeled(relabelMap, reservedVars)
        except NestedCompositeExpressionError as e:
            raise ImproperRelabeling('May only relabel a Lambda argument with a composite expression if it was wrapped in the appropriate Bundle: ' + e.msg)
        for arg in self.arguments:
            # Here we enable an exception of relabeling to a reserved variable as
            # long as we are relabeling the Lambda argument and internal variable together.
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            # Also works with Etcetera: (x, ..y..) -> f(x, ..y..) relabeled to (x, y, z) -> f(x, y, z).
            newArg = arg.relabeled(relabelMap, reservedVars)
            if isinstance(newArg, ExpressionList):
                for x in newArg: innerReservations[extractVar(x)] = extractVar(arg)
            else: innerReservations[extractVar(newArg)] = extractVar(arg)
        # the lambda expression with the substitution:
        subbedExpr = self.expression.substituted(innerExprMap, relabelMap, innerReservations)
        try:
            newLambda = Lambda(newArgs, subbedExpr)
        except TypeError as e:
            raise ImproperSubstitution(e.message)
        except ValueError as e:
            raise ImproperSubstitution(e.message)            
        return newLambda
        
    def usedVars(self):
        '''
        The used variables the lambda function are the used variables of the expression
        plus the lambda argument variables.
        '''
        return self.expression.usedVars().union(set(self.argVarSet))
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the expression
        minus the lambda argument variables.  The lambda function binds those variables.
        '''
        innerFreeVs = set(self.expression.freeVars())
        return innerFreeVs - self.argVarSet
    
    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        innerFreeVs = set(self.expression.freeMultiVars())
        return innerFreeVs - self.argVarSet

from expr import Expression, MakeNotImplemented, ImproperSubstitution, ImproperRelabeling

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameters to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the 
    parameters and sin(x^2 + y) is the body.  Each parameter must be either
    a Variable or MultiVariable.
    '''
    def __init__(self, parameters, body):
        '''
        Initialize a Lambda function expression given parameters and a body.
        Each parameter in parameters must be a Variable or MultiVariable.
        A single Variable/MultiVarable may be passed as parameters, but
        will then become a list with a single element.
        '''
        from composite import singleOrCompositeExpression
        from bundle import Bundle
        from label import Variable, MultiVariable
        if isinstance(parameters, Variable) or isinstance(parameters, MultiVariable):
            self.parameters = [parameters]
        else:
            self.parameters = list(parameters)
        for parameter in self.parameters:
            if not isinstance(parameter, Variable) and not isinstance(parameter, MultiVariable):
                raise TypeError('Each element of the Lambda parameters must be a Variable or MultiVariable')
        self.parameterSet = set(self.parameters)
        if len(self.parameterSet) != len(self.parameters):
            raise ValueError('Lambda parameters Variables must be unique with respect to each other.')
        body = singleOrCompositeExpression(body)
        if not isinstance(body, Expression):
            raise TypeError('A Lambda body must be of type Expression')
        if isinstance(body, Bundle):
            raise TypeError('A Bundle must be within an ExpressionTensor or exprlist, not directly as a Lambda body')
        self.body = body
        Expression.__init__(self, ['Lambda'], self.parameters + [self.body])
        
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Lambda':
            raise ValueError("Expecting Lambda coreInfo to contain exactly one item: 'Lambda'")
        if subClass != Lambda: 
            raise MakeNotImplemented(subClass)
        parameters, body = subExpressions[:-1], subExpressions[-1]
        return Lambda(parameters, body)

    def string(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        parameterListStr = ', '.join([parameter.string() for parameter in self.parameters])
        if len(self.parameters) == 1:
            outStr += parameterListStr + ' -> '
        else:
            outStr += '(' + parameterListStr + ') -> '
        outStr += self.body.string(fence=True)
        if fence: outStr += ']'
        return outStr
    
    def latex(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = r'\left[' if fence else ''
        parameterListStr = ', '.join([parameter.latex() for parameter in self.parameters])
        if len(self.parameters) == 1:
            outStr +=  parameterListStr + r'\mapsto '
        else:
            outStr += r'\left(' + parameterListStr + r'\right) \mapsto '
        outStr += self.body.latex(fence=True)
        if fence: outStr += r'\right]'
        return outStr
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Return this expression with its variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        The Lambda parameters have their own scope within the Lambda 
        body and do not get substituted.  They may be relabeled, however. 
        Substitutions within the Lambda body are restricted to 
        exclude the Lambda parameters themselves (these Variables 
        are reserved), consistent with any relabeling.
        '''
        from proveit import ExpressionList, Composite, Variable, MultiVariable
        from composite import singleOrCompositeExpression
        if (exprMap is not None) and (self in exprMap):
            # the full expression is to be substituted
            return exprMap[self]._restrictionChecked(reservedVars)        
        if relabelMap is None: relabelMap = dict()
        # Can't substitute the lambda parameters; they are in a new scope.
        innerExprMap = {key:value for (key, value) in exprMap.iteritems() if key not in self.parameterSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        newParams = []
        for parameter in self.parameters:
            # Note that lambda parameters introduce a new scope and don't need to,
            # themselves, be restriction checked.  But they generate new inner restrictions
            # that disallow any substitution from a variable that isn't in the new scope
            # to a variable that is in the new scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            # Also works with MultiVariables: (x, y*) -> f(x, ..,y*,..) relabeled to (x, y, z*) -> f(x, y, ..,z*,..).
            if parameter in relabelMap:
                relabeledParam = singleOrCompositeExpression(relabelMap[parameter])
                if isinstance(parameter, Variable) and isinstance(relabeledParam, Composite):
                    raise ImproperSubstitution('May not relabel a Variable to a Composite')
                if isinstance(parameter, Variable) and isinstance(relabeledParam, MultiVariable):
                    raise ImproperSubstitution('May not relabel a Variable to a MultiVariable')
                if isinstance(relabeledParam, ExpressionList):
                    # MultiVariable to a list
                    for newParam in relabeledParam: 
                        newParams.append(newParam)
                        innerReservations[newParam] = parameter
                elif isinstance(relabeledParam, Composite): # ExpressionTensor or NamedExpressions (why not?)
                    # MultiVariable to a tensor
                    for tensorKey in relabeledParam.keys():
                        newParam = relabeledParam[tensorKey]
                        newParams.append(newParam)
                        innerReservations[newParam] = parameter
                else: 
                    # Variable to a Variable or MultiVariable to MultiVariable
                    newParams.append(relabeledParam)
                    innerReservations[relabeledParam] = parameter
            else:
                # Not relabeled
                newParams.append(parameter)
                innerReservations[parameter] = parameter
        # the lambda body with the substitution:
        subbedExpr = self.body.substituted(innerExprMap, relabelMap, innerReservations)
        try:
            newLambda = Lambda(newParams, subbedExpr)
        except TypeError as e:
            raise ImproperSubstitution(e.message)
        except ValueError as e:
            raise ImproperSubstitution(e.message)            
        return newLambda
                        
    def usedVars(self):
        '''
        The used variables of the lambda function are the used variables of the 
        body plus the lambda parameters.
        '''
        return self.body.usedVars().union(set(self.parameterSet))
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the body
        minus the lambda parameters.  The lambda function binds those variables.
        '''
        innerFreeVs = set(self.body.freeVars())
        return innerFreeVs - self.parameterSet
    
    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        innerFreeVs = set(self.body.freeMultiVars())
        return innerFreeVs - self.parameterSet

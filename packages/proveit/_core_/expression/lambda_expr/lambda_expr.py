from proveit._core_.expression.expr import Expression, MakeNotImplemented, ImproperSubstitution
from proveit._core_.defaults import USE_DEFAULTS

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameter(s) to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the 
    parameters and sin(x^2 + y) is the body.  Each parameter must be a
    Variable.
    '''
    def __init__(self, parameter_or_parameters, body, styles=tuple(), requirements=tuple()):
        '''
        Initialize a Lambda function expression given parameter(s) and a body.
        Each parameter must be a Variable.
        When there is a single parameter, there will be a 'parameter'
        attribute. Either way, there will be a 'parameters' attribute
        that bundles the one or more Variables into an ExprList.
        The 'body' attribute will be the lambda function body
        Expression (that may or may not be a Composite).
        '''
        from proveit._core_.expression.composite import compositeExpression, singleOrCompositeExpression, Iter
        from proveit._core_.expression.label import Variable
        self.parameters = compositeExpression(parameter_or_parameters)
        for parameter in self.parameters:
            if not isinstance(parameter, Variable):
                raise TypeError('parameter must be a Variable-type Expression')
        if len(self.parameters) == 1:
            # has a single parameter
            self.parameter = self.parameters[0]
        self.parameterSet = set(self.parameters)
        if len(self.parameterSet) != len(self.parameters):
            raise ValueError('Lambda parameters Variables must be unique with respect to each other.')
        body = singleOrCompositeExpression(body)
        if not isinstance(body, Expression):
            raise TypeError('A Lambda body must be of type Expression')
        if isinstance(body, Iter):
            raise TypeError('An Iter must be within an ExprList or ExprTensor, not directly as a Lambda body')
        self.body = body
        for requirement in self.body.requirements:
            if not self.parameterSet.isdisjoint(requirement.freeVars()):
                raise LambdaError("Cannot generate a Lambda expression with parameters involved in Lambda body requirements: " + str(requirement))
        Expression.__init__(self, ['Lambda'], list(self.parameters) + [self.body], styles=styles, requirements=requirements)
        
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Lambda':
            raise ValueError("Expecting Lambda coreInfo to contain exactly one item: 'Lambda'")
        if subClass != Lambda: 
            raise MakeNotImplemented(subClass)
        parameters, body = subExpressions[:-1], subExpressions[-1]
        return Lambda(parameters, body)
    
    def mapped(self, *args):
        '''
        Perform and lambda mapping, replacing the parameters with the given arguments.
        '''
        return self.body.substituted({param:arg for param, arg in zip(self.parameters, args)})
    
    def extractParameter(self, mapped_expr):
        '''
        
        '''
        pass

    def extractParameters(self, mapped_expr):
        '''
        
        '''
        pass

    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Lambda expression.
        '''
        if hasattr(self, 'parameter'):
            yield self.parameter
        else:
            yield self.parameters
        yield self.body

    def string(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        parameterListStr = ', '.join([parameter.string(abbrev=True) for parameter in self.parameters])
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
        parameterListStr = ', '.join([parameter.latex(abbrev=True) for parameter in self.parameters])
        if len(self.parameters) == 1:
            outStr +=  parameterListStr + r'\mapsto '
        else:
            outStr += r'\left(' + parameterListStr + r'\right) \mapsto '
        outStr += self.body.latex(fence=True)
        if fence: outStr += r'\right]'
        return outStr
        
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return this expression with its variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        The Lambda parameters have their own scope within the Lambda 
        body and do not get substituted.  They may be relabeled, however. 
        Substitutions within the Lambda body are restricted to 
        exclude the Lambda parameters themselves (these Variables 
        are reserved), consistent with any relabeling.
        '''
        from proveit import Variable
        if (exprMap is not None) and (self in exprMap):
            # the full expression is to be substituted
            return exprMap[self]._restrictionChecked(reservedVars)        
        if relabelMap is None: relabelMap = dict()
        # Can't substitute the lambda parameters; they are in a new scope.
        innerExprMap = {key:value for (key, value) in exprMap.iteritems() if key not in self.parameterSet}
        # Can't use assumptions involving lambda parameters
        innerAssumptions = [assumption for assumption in assumptions if self.parameterSet.isdisjoint(assumption.freeVars())]
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        newParams = []
        for parameter in self.parameters:
            # Note that lambda parameters introduce a new scope and don't need to,
            # themselves, be restriction checked.  But they generate new inner restrictions
            # that disallow any substitution from a variable that isn't in the new scope
            # to a variable that is in the new scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            if parameter in relabelMap:
                relabeledParam = relabelMap[parameter]
                if not isinstance(relabeledParam, Variable):
                    raise ImproperSubstitution('May only relabel a Variable to another Variable')
                newParams.append(relabeledParam)
                innerReservations[relabeledParam] = parameter
            else:
                # Not relabeled
                newParams.append(parameter)
                innerReservations[parameter] = parameter
        # the lambda body with the substitution:
        subbedExpr = self.body.substituted(innerExprMap, relabelMap, innerReservations, innerAssumptions, requirements)
        try:
            newLambda = Lambda(newParams, subbedExpr)
        except TypeError as e:
            raise ImproperSubstitution(e.message)
        except ValueError as e:
            raise ImproperSubstitution(e.message)            
        return newLambda

    def iterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap = None, reservedVars = None, assumptions=USE_DEFAULTS, requirements=None):
        subbed_body = self.body.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        
        for iter_range in subbed_body.iterRanges(iterParams, startArgs, endArgs, exprMap, relabelMap, reservedVars, assumptions, requirements):
            yield iter_range
                                                                        
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

class LambdaError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

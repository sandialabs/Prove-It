from proveit._core_.expression.expr import Expression, MakeNotImplemented, ImproperSubstitution, ScopingViolation
from proveit._core_.defaults import defaults, USE_DEFAULTS

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameter(s) to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the 
    parameters and sin(x^2 + y) is the body.  Each parameter must be a
    Variable.  A Lambda may have conditions so that the map is only
    defined when the conditions are met.  For example,
        (x, y) -> x / y | x in Reals, y in Reals, y != 0
    defines the mapping (x, y) -> x / y as long as x and y are Reals
    and y is not zero.
    '''
    def __init__(self, parameter_or_parameters, body, conditions=tuple(), styles=dict(), requirements=tuple()):
        '''
        Initialize a Lambda function expression given parameter(s) and a body.
        Each parameter must be a Variable.
        When there is a single parameter, there will be a 'parameter'
        attribute. Either way, there will be a 'parameters' attribute
        that bundles the one or more Variables into an ExprList.
        The 'body' attribute will be the lambda function body
        Expression (that may or may not be a Composite).  Zero or
        more expressions may be provided.
        '''
        from proveit._core_.expression.composite import compositeExpression, singleOrCompositeExpression, Iter, Indexed
        from proveit._core_.expression.label import Variable
        self.parameters = compositeExpression(parameter_or_parameters)
        parameterVars = list()
        for parameter in self.parameters:
            if isinstance(parameter, Iter) and isinstance(parameter.lambda_map.body, Indexed):
                parameterVars.append(parameter.lambda_map.body.var)     
            elif isinstance(parameter, Indexed):
                parameterVars.append(parameter.var)
            elif isinstance(parameter, Variable):
                parameterVars.append(parameter)
            else:
                raise TypeError('parameters must be a Variables, Indexed variable, or iteration (Iter) over Indexed variables.')
        if len(self.parameters) == 1:
            # has a single parameter
            self.parameter = self.parameters[0]
            self.parameter_or_parameters = self.parameter
        else:
            self.parameter_or_parameters = self.parameters
        self.parameterVars = tuple(parameterVars)
        self.parameterVarSet = frozenset(parameterVars)
        if len(self.parameterVarSet) != len(self.parameters):
            raise ValueError('Lambda parameters Variables must be unique with respect to each other.')
        body = singleOrCompositeExpression(body)
        if not isinstance(body, Expression):
            raise TypeError('A Lambda body must be of type Expression')
        if isinstance(body, Iter):
            raise TypeError('An Iter must be within an ExprList or ExprTensor, not directly as a Lambda body')
        self.body = body
        self.conditions = compositeExpression(conditions)
        for requirement in self.body.getRequirements():
            if not self.parameterVarSet.isdisjoint(requirement.freeVars()):
                raise LambdaError("Cannot generate a Lambda expression with parameter variables involved in Lambda body requirements: " + str(requirement))
        sub_exprs = [self.parameter_or_parameters, self.body]
        if len(self.conditions)>0: sub_exprs.append(self.conditions)
        Expression.__init__(self, ['Lambda'], sub_exprs, styles=styles, requirements=requirements)
        
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Lambda':
            raise ValueError("Expecting Lambda coreInfo to contain exactly one item: 'Lambda'")
        if subClass != Lambda: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions)==3:
            parameters, body, conditions = subExpressions
        else:
            parameters, body = subExpressions
            conditions = tuple()
        return Lambda(parameters, body, conditions).withStyles(**styles)
    
    def mapped(self, *args):
        '''
        Perform and lambda mapping, replacing the parameters with the given arguments.
        '''
        return self.body.substituted({param:arg for param, arg in zip(self.parameters, args)})
    
    def extractParameter(self, mappedExpr):
        '''
        Given a mapped expression, return the parameter that will transform
        this Lambda expression into the mapped expression.  For example,
        if the Lambda expression is x -> x + 1 and the mapped expression
        is 2 + 1, this will return 2.  If there is more than one parameter
        in this Lambda expression, use extractParameters instead.
        '''
        assert len(self.parameters) == 1, "Use the 'extractParameters' method when there is more than one parameter"
        return self.extractParameters(mappedExpr)[0]

    def extractParameters(self, mappedExpr):
        '''
        Given a mapped expression, return the parameters that will transform
        this Lambda expression into the mapped expression.  For example,
        if the Lambda expression is (x, y) -> x + y and the mapped expression
        is 1 + 2, this will return (1, 2).
        '''
        # Perform a simulataneous depth-first search to find the parameters
        # of the lambda map and corresponding values from the mapped_expr.
        parameters = self.parameters
        param_values = [None]*len(parameters)
        lambda_sub_expr = self.body
        mapped_sub_expr = mappedExpr
        if lambda_sub_expr.numSubExpr() != mapped_sub_expr.numSubExpr():
            raise ParameterExtractionError("# of sub-expressions, %d vs %d"%(lambda_sub_expr.numSubExpr(), mapped_sub_expr.numSubExpr()))
        if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
            raise ParameterExtractionError("Expression class, %s vs %s"%(str(lambda_sub_expr.__class__), str(mapped_sub_expr.__class__)))
        if lambda_sub_expr._coreInfo != mapped_sub_expr._coreInfo:
            raise ParameterExtractionError("core information, %s vs %s"%(str(lambda_sub_expr._coreInfo), str(mapped_sub_expr._coreInfo)))
        lambda_sub_expr_iters = [lambda_sub_expr.subExprIter()]
        mapped_sub_expr_iters = [mapped_sub_expr.subExprIter()]
        while len(lambda_sub_expr_iters) > 0:
            try:
                lambda_sub_expr = lambda_sub_expr_iters[-1].next()
                mapped_sub_expr = mapped_sub_expr_iters[-1].next()
                if lambda_sub_expr in parameters:
                    # found a match
                    param_idx = parameters.index(lambda_sub_expr)
                    if param_values[param_idx] is not None and param_values[param_idx] != mapped_sub_expr:
                        raise ParameterExtractionError("inconsistent parameters values, %s vs %s"%(str(param_values[param_idx]), str(mapped_sub_expr)))
                    param_values[param_idx] = mapped_sub_expr
                else:
                    if lambda_sub_expr.numSubExpr() != mapped_sub_expr.numSubExpr():
                        raise ParameterExtractionError("# of sub-expressions, %d vs %d"%(lambda_sub_expr.numSubExpr(), mapped_sub_expr.numSubExpr()))
                    if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
                        raise ParameterExtractionError("Expression class, %s vs %s"%(str(lambda_sub_expr.__class__), str(mapped_sub_expr.__class__)))
                    if lambda_sub_expr._coreInfo != mapped_sub_expr._coreInfo:
                        raise ParameterExtractionError("core information, %s vs %s"%(str(lambda_sub_expr._coreInfo), str(mapped_sub_expr._coreInfo)))
                    if lambda_sub_expr.numSubExpr() > 0:
                        # going deeper
                        lambda_sub_expr_iters.append(lambda_sub_expr.subExprIter())
                        mapped_sub_expr_iters.append(mapped_sub_expr.subExprIter())
            except StopIteration:
                # exhausted the "deepest" of the sub-expressions
                lambda_sub_expr_iters.pop(-1) # pop back out to a shallower level
                mapped_sub_expr_iters.pop(-1)
        return param_values

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Lambda expression.
        '''
        if hasattr(self, 'parameter'):
            yield self.parameter
        else:
            yield self.parameters
        yield self.body
        if len(self.conditions) > 0:
            yield 'conditions', self.conditions

    def string(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        parameterListStr = ', '.join([parameter.string(abbrev=True) for parameter in self.parameters])
        if self.parameters.singular():
            outStr += parameterListStr + ' -> '
        else:
            outStr += '(' + parameterListStr + ') -> '
        outStr += self.body.string(fence=True)
        if len(self.conditions) > 0:
            outStr += ' | '
            outStr += self.conditions.formatted('string', fence=False)
        if fence: outStr += ']'
        return outStr
    
    def latex(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = r'\left[' if fence else ''
        parameterListStr = ', '.join([parameter.latex(abbrev=True) for parameter in self.parameters])
        if self.parameters.singular():
            outStr +=  parameterListStr + r' \mapsto '
        else:
            outStr += r'\left(' + parameterListStr + r'\right) \mapsto '
        outStr += self.body.latex(fence=True)
        if len(self.conditions) > 0:
            outStr += '~|~'
            outStr += self.conditions.formatted('latex', fence=False)
        if fence: outStr += r'\right]'
        return outStr
    
    def _innerScopeSub(self, exprMap, relabelMap, reservedVars, assumptions, requirements):
        '''
        Helper method for substituted (and used by Iter.substituted) which handles the change in
        scope properly as well as parameter relabeling (or iterated parameter expansion).
        '''
        
        from proveit import compositeExpression, Iter
        
        # Can't substitute the lambda parameter variables; they are in a new scope.
        inner_expr_map = {key:value for (key, value) in exprMap.iteritems() if key not in self.parameterVarSet}
        # Handle relabeling and variable reservations consistent with relabeling.
        inner_reservations = dict() if reservedVars is None else dict(reservedVars)
        new_params = []
        
        for parameter, parameterVar in zip(self.parameters, self.parameterVars):
            # Note that lambda parameters introduce a new scope and don't need to,
            # themselves, be restriction checked.  But they generate new inner restrictions
            # that disallow any substitution from a variable that isn't in the new scope
            # to a variable that is in the new scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            if parameterVar in relabelMap:
                if isinstance(parameter, Iter):
                    # expanding an iteration.  For example: x_1, ..., x_n -> a, b, c, d 
                    relabeledParams = parameter.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
                    if len(relabeledParams) != len(relabelMap[parameterVar]):
                        raise ImproperSubstitution("Relabeling of iterated parameters incomplete: %d length expansion versus %d length substitution"%(len(relabeledParams), len(relabelMap[parameterVar])))
                else:
                    relabeledParams = compositeExpression(relabelMap[parameterVar])
                for relabeledParam in relabeledParams:
                    new_params.append(relabeledParam)
                    inner_reservations[relabeledParam] = parameterVar
            else:
                # can perform a substition in indices of a parameter iteration: x_1, ..., x_n
                new_params.append(parameter.substituted(inner_expr_map, relabelMap, reservedVars, assumptions, requirements))
                inner_reservations[parameterVar] = parameterVar

        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = [assumption for assumption in assumptions if assumption.freeVars().isdisjoint(new_params)]
                                      
        return new_params, inner_expr_map, inner_assumptions, inner_reservations
        
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
        from proveit.logic import Forall
        
        self._checkRelabelMap(relabelMap)
        if (exprMap is not None) and (self in exprMap):
            # the full expression is to be substituted
            return exprMap[self]._restrictionChecked(reservedVars)        
        if relabelMap is None: relabelMap = dict()
        assumptions = defaults.checkedAssumptions(assumptions)
        
        new_params, inner_expr_map, inner_assumptions, inner_reservations = self._innerScopeSub(exprMap, relabelMap, reservedVars, assumptions, requirements)
        
        # conditions with substitutions:
        condition_requirements = []
        condition_assumptions = inner_assumptions
        subbedConditions = self.conditions.substituted(inner_expr_map, relabelMap, inner_reservations, condition_assumptions, condition_requirements)
        # The lambda body with the substitutions.  Add the conditions, with substitutions, as assumptions
        # since they must be satisfied for the mapping to be well-defined.
        body_requirements = []
        body_assumptions = list(inner_assumptions)+list(subbedConditions)
        subbedBody = self.body.substituted(inner_expr_map, relabelMap, inner_reservations, body_assumptions, body_requirements)
        
        for requirements, requirements_assumptions in zip((condition_requirements, body_requirements), ([], subbedConditions)):
            for requirement in requirements:
                if requirement.freeVars().isdisjoint(new_params):
                    requirements.append(requirement)
                else:
                    # When the requirement involves any of the lambda parameters, we must universally quantify
                    # over those parameters, with appropriate conditions.  Appropriate conditions are the
                    # applicable assumptions that involve the lambda parameters.  This excludes the 'inner_assumptions'
                    # because they cannot involve lambda parameters (those were excluded).
                    requirement_params = requirement.freeVars().intersection(new_params)
                    requirement_conditions = [condition for condition in requirements_assumptions if not new_params.isdisjoint(condition.freeVars())]
                    requirement = Forall(requirement_params, requirement, conditions=requirement_conditions)
                    requirements.append(requirement)
                    raise ScopingViolation("Substitution requirements must not involve Lambda parameters")
        
        try:
            newLambda = Lambda(new_params, subbedBody, subbedConditions)
        except TypeError as e:
            raise ImproperSubstitution(e.message)
        except ValueError as e:
            raise ImproperSubstitution(e.message)            
        return newLambda

    def _expandingIterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap = None, reservedVars = None, assumptions=USE_DEFAULTS, requirements=None):
        from proveit import Variable, compositeExpression
        # Can't substitute the lambda parameter variables; they are in a new scope.
        innerExprMap = {key:value for (key, value) in exprMap.iteritems() if key not in self.parameterVarSet}
        # Can't use assumptions involving lambda parameter variables
        innerAssumptions = [assumption for assumption in assumptions if self.parameterVarSet.isdisjoint(assumption.freeVars())]
        # Handle relabeling and variable reservations consistent with relabeling.
        innerReservations = dict() if reservedVars is None else dict(reservedVars)
        for parameterVar in self.parameterVars:
            # Note that lambda parameters introduce a new scope and don't need to,
            # themselves, be restriction checked.  But they generate new inner restrictions
            # that disallow any substitution from a variable that isn't in the new scope
            # to a variable that is in the new scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not f to x. 
            if parameterVar in relabelMap:
                relabeledParams = compositeExpression(relabelMap[parameterVar])
                for relabeledParam in relabeledParams:
                    if not isinstance(relabeledParam, Variable):
                        raise ImproperSubstitution('May only relabel a Variable to another Variable or list of Variables')
                    innerReservations[relabeledParam] = parameterVar
            else:
                # Not relabeled
                innerReservations[parameterVar] = parameterVar
        
        # collect the iter ranges from the body and all conditions
        iter_ranges = set()
        for iter_range in self.body.expandingIterRanges(iterParams, startArgs, endArgs, innerExprMap, relabelMap, innerReservations, innerAssumptions, requirements):
            iter_ranges.add(iter_range)
        for iter_range in self.conditions.expandingIterRanges(iterParams, startArgs, endArgs, innerExprMap, relabelMap, innerReservations, innerAssumptions, requirements):
            iter_ranges.add(iter_range)
        for iter_range in iter_ranges:
            yield iter_range
    
    def compose(self, lambda2):
        '''
        Given some x -> f(x) for self (lambda1) and y -> g(y) for lambda2,
        return x -> f(g(x)).  Also works with multiple parameters:
        x1, x2, ..., xn -> f(x1, x2, ..., xn)  for lambda 1 and  
        y1, y2, ..., yn -> g1(y1, y2, ..., yn), 
        y1, y2, ..., yn -> g2(y1, y2, ..., yn), 
        ...
        y1, y2, ..., yn -> gn(y1, y2, ..., yn) for lambda2 returns
        x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
        '''
        lambda1 = self
        if len(lambda1.parameters) == 1:
            if len(lambda2.parameters) != 1:
                raise TypeError("lambda2 may only take 1 parameter if lambda1 takes only 1 parameter")
            # g(x)
            relabeledExpr2 = lambda2.body.relabeled({lambda2.parameters[0]:lambda1.parameters[0]})
            # x -> f(g(x))
            return Lambda(lambda1.parameters[0], lambda1.body.substituted({lambda1.parameters[0]:relabeledExpr2}))
        else:
            if len(lambda2) != len(lambda1.parameters):
                raise TypeError("Must supply a list of lambda2s with the same length as the number of lambda1 parameters")
            relabeledExpr2s = []
            for lambda2elem in lambda2:
                if len(lambda2elem.parameters) != len(lambda1.parameters):
                    raise TypeError("Each lambda2 must have the same number of parameters as lambda1")
                # gi(x1, x2, ..., xn)
                paramReplMap = {param2:param1 for param1, param2 in zip(lambda1.parameters, lambda2elem.parameters)}
                relabeledExpr2s.append(lambda2elem.body.substituted(paramReplMap))
            # x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
            lambda1ExprSubMap = {param1:relabeledExpr2 for param1, relabeledExpr2 in zip(lambda1.parameters, relabeledExpr2s)}
            return Lambda(lambda1.parameters, lambda1.body.substituted(lambda1ExprSubMap))
    
    @staticmethod
    def globalRepl(masterExpr, subExpr):
        '''
        Returns the Lambda map for replacing the given sub-Expression
        everywhere that it occurs in the master Expression.
        '''
        lambdaParam = masterExpr.safeDummyVar()
        return Lambda(lambdaParam, masterExpr.substituted({subExpr:lambdaParam}))
    
    def usedVars(self):
        '''
        The used variables of the lambda function are the used variables of the 
        body+conditions plus the lambda parameter variables.
        '''
        return self.body.usedVars().union(set(self.parameterVarSet)).union(self.conditions.usedVars())
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the body+conditions
        minus the lambda parameter variables.  The lambda function binds those variables.
        '''
        innerFreeVs = set(self.body.freeVars()).union(self.conditions.freeVars())
        return innerFreeVs - self.parameterVarSet

class LambdaError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ParameterExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics
    def __str__(self):
        return "Cannot extract parameter; mappedExpr does not match this Lambda expression: " + self.specifics
from proveit._core_.expression.expr import Expression, MakeNotImplemented, ImproperSubstitution, ScopingViolation
from proveit._core_.expression.conditional import Conditional
from proveit._core_.expression.label.var import safeDummyVars
from proveit._core_.defaults import defaults, USE_DEFAULTS

def getParamVar(parameter):
    '''
    Parameters may be variables, indexed variables, or iterations over indexed
    variables.  If it is either of the latter, the associated, intrinsic
    parameter variable (that is introduced in the new scopse) 
    is the variable of the Indexed expression.
    '''
    from proveit._core_.expression.label import Variable
    from proveit._core_.expression.composite import Iter, Indexed
    if isinstance(parameter, Iter) and isinstance(parameter.lambda_map.body, Indexed):
        from proveit.number import num
        indexed_var = parameter.lambda_map.body
        if parameter.start_index != num(indexed_var.base):
            raise TypeError('An iteration parameter must start with the base '
                            'of the indexed variable')
        return indexed_var.var
    elif isinstance(parameter, Indexed):
        return parameter.var
    elif isinstance(parameter, Variable):
        return parameter
    else:
        raise TypeError('parameters must be a Variables, Indexed variable, or '
                        'iteration (Iter) over Indexed variables.')

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameter(s) to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the 
    parameters and sin(x^2 + y) is the body.  Each parameter must be a
    Variable.  Note that the body of a Lambda may be a Conditional
    such that the mapping is only defined when one of the conditions is
    satisfied.
    '''
    def __init__(self, parameter_or_parameters, body, _generic_expr=None):
        '''
        Initialize a Lambda function expression given parameter(s) and a body.
        Each parameter must be a Variable or an iteration (Iter) of 
        indexed variables (IndexedVar).
        When there is a single parameter, there will be a 'parameter'
        attribute. Either way, there will be a 'parameters' attribute
        that bundles the one or more Variables into an ExprTuple.
        The 'body' attribute will be the lambda function body
        Expression.  The body may be singular or a composite.
        
        _generic_expr is used internally for efficiently rebuilding a Lambda.
        '''
        from proveit._core_.expression.composite import (compositeExpression, 
                                                         singleOrCompositeExpression, 
                                                         Iter)
        if styles is None: styles = dict()
        self.parameters = compositeExpression(parameter_or_parameters)
        parameterVars = [getParamVar(parameter) for parameter in self.parameters]
        if len(self.parameters) == 1:
            # has a single parameter
            self.parameter = self.parameters[0]
            self.parameter_or_parameters = self.parameter
        else:
            self.parameter_or_parameters = self.parameters
        self.parameterVars = tuple(parameterVars)
        self.parameterVarSet = frozenset(parameterVars)
        if len(self.parameterVarSet) != len(self.parameters):
            raise ValueError("Lambda parameters Variables must be unique with "
                             "respect to each other.")
        body = singleOrCompositeExpression(body)
        if not isinstance(body, Expression):
            raise TypeError('A Lambda body must be of type Expression')
        if isinstance(body, Iter):
            raise TypeError('An Iter must be within an ExprTuple or ExprArray, "
                            "not directly as a Lambda body')
        self.body = body
                
        if _generic_expr is None:
            # Create a "generic" version (if not already) of the Lambda 
            # expression since the choice of parameter labeling is irrelevant.
            # If there are multiple parameters and any of them are iterations,
            # combine them together into one iteration parameter.  TODO
            generic_body = self.body._generic_version()
            generic_body_vars = generic_body.usedVars()
            disallowed_vars = (generic_body_vars-self.parameterVarSet)
            generic_param_vars = tuple(safeDummyVars(len(self.parameterVars), 
                                                     *disallowed_vars))
            if generic_param_vars != self.parameterVars:
                relabel_map = {param:generic_param for param, generic_param 
                               in zip(self.parameterVars, generic_param_vars)}
                # temporarily disable automation during the relabeling process
                prev_automation = defaults.automation
                defaults.automation = False
                generic_parameters = self.parameters._generic_version()
                generic_parameters = generic_parameters.relabeled(relabel_map)
                generic_body = generic_body.relabeled(relabel_map)
                genericExpr = Lambda(generic_parameters, generic_body)\
                                .withStyles(**styles)
                defaults.automation = prev_automation # restore to previous value
            else:
                genericExpr = self
        elif _generic_expr == '.':
            genericExpr = self
        else:
            genericExpr = _generic_expr
        self._genericExpr = genericExpr
        sub_exprs = (self.parameter_or_parameters, self.body)
        Expression.__init__(self, ['Lambda'], sub_exprs, styles=styles)
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions, genericExpr=None):
        if len(coreInfo) != 1 or coreInfo[0] != 'Lambda':
            raise ValueError("Expecting Lambda coreInfo to contain exactly one "
                             "item: 'Lambda'")
        if subClass != Lambda: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions)!=2:
            raise ValueError("Expected Lambda to have two sub-expressions")
        parameters, body = subExpressions
        return Lambda(parameters, body, _generic_expr=genericExpr)\
                    .withStyles(**styles)
    
    def mapped(self, *args):
        '''
        Perform and lambda mapping, replacing the parameters with the given 
        arguments.
        '''
        return self.body.substituted({param:arg for param, arg 
                                      in zip(self.parameters, args)})
    
    def extractArgument(self, mappedExpr):
        '''
        Given a mapped expression, return the argument that will transform
        this Lambda expression into the mapped expression.  For example,
        if the Lambda expression is x -> x + 1 and the mapped expression
        is 2 + 1, this will return 2.  If there is more than one parameter
        in this Lambda expression, use extractArguments instead.
        '''
        assert len(self.parameters) == 1, ("Use the 'extractArguments' method "
                                           "when there is more than one parameter")
        return self.extractParameters(mappedExpr)[0]

    def extractArguments(self, mappedExpr):
        '''
        Given a mapped expression, return the arguments that will transform
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
            raise ArgumentExtractionError("# of sub-expressions, %d vs %d"
                                          %(lambda_sub_expr.numSubExpr(), 
                                            mapped_sub_expr.numSubExpr()))
        if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
            raise ArgumentExtractionError("Expression class, %s vs %s"
                                          %(str(lambda_sub_expr.__class__), 
                                            str(mapped_sub_expr.__class__)))
        if lambda_sub_expr._coreInfo != mapped_sub_expr._coreInfo:
            raise ArgumentExtractionError("core information, %s vs %s"
                                          %(str(lambda_sub_expr._coreInfo), 
                                            str(mapped_sub_expr._coreInfo)))
        lambda_sub_expr_iters = [lambda_sub_expr.subExprIter()]
        mapped_sub_expr_iters = [mapped_sub_expr.subExprIter()]
        while len(lambda_sub_expr_iters) > 0:
            try:
                lambda_sub_expr = next(lambda_sub_expr_iters[-1])
                mapped_sub_expr = next(mapped_sub_expr_iters[-1])
                extraction_err = ArgumentExtractionError # abbreviation
                if lambda_sub_expr in parameters:
                    # found a match
                    param_idx = parameters.index(lambda_sub_expr)
                    if param_values[param_idx] is not None \
                            and param_values[param_idx] != mapped_sub_expr:
                        raise extraction_err("inconsistent parameters values, "
                                             "%s vs %s"
                                             %(str(param_values[param_idx]), 
                                               str(mapped_sub_expr)))
                    param_values[param_idx] = mapped_sub_expr
                else:
                    if lambda_sub_expr.numSubExpr() != mapped_sub_expr.numSubExpr():
                        raise extraction_err("# of sub-expressions, %d vs %d"
                                             %(lambda_sub_expr.numSubExpr(), 
                                               mapped_sub_expr.numSubExpr()))
                    if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
                        raise extraction_err("Expression class, %s vs %s"
                                             %(str(lambda_sub_expr.__class__), 
                                               str(mapped_sub_expr.__class__)))
                    if lambda_sub_expr._coreInfo != mapped_sub_expr._coreInfo:
                        raise extraction_err("core information, %s vs %s"
                                             %(str(lambda_sub_expr._coreInfo), 
                                               str(mapped_sub_expr._coreInfo)))
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
        yield self.parameter_or_paramters
        yield self.body

    def string(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        parameterListStr = ', '.join([parameter.string(abbrev=True) for parameter 
                                      in self.parameters])
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
        parameterListStr = ', '.join([parameter.latex(abbrev=True) for parameter 
                                      in self.parameters])
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
    
    def _innerScopeSub(self, exprMap, relabelMap, reservedVars, assumptions):
        '''
        Helper method for substituted (and used by Iter.substituted) which 
        handles the change in scope properly as well as parameter relabeling 
        (or iterated parameter expansion).
        '''
        
        from proveit import compositeExpression, Iter, ExprTuple
        
        # Can't substitute the lambda parameter variables; 
        # they are in a new scope.
        inner_expr_map = {key:value for (key, value) in exprMap.items() 
                          if key not in self.parameterVarSet}
        # Handle relabeling and variable reservations consistent with 
        # relabeling.
        inner_reservations = dict() if reservedVars is None else dict(reservedVars)
        new_params = []
        
        for parameter, parameterVar in zip(self.parameters, self.parameterVars):
            # Note that lambda parameters introduce a new scope and don't need 
            # to, themselves, be restriction checked.  But they generate new 
            # inner restrictions that disallow any substitution from a variable 
            # that isn't in the new scope to a variable that is in the new 
            # scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not 
            # f to x. 
            if parameterVar in relabelMap:
                if isinstance(parameter, Iter):
                    relabeledParams = parameter.substituted(exprMap, relabelMap, 
                                                            reservedVars, assumptions)
                    if isinstance(relabeledParams, ExprTuple):
                        # Expanding an iteration.
                        # For example: x_1, ..., x_n -> a, b, c, d 
                        if len(relabeledParams) != len(relabelMap[parameterVar]):
                            raise ImproperSubstitution("Relabeling of iterated "
                                                       "parameters incomplete: %d "
                                                       "length expansion versus %d "
                                                       "length substitution"
                                                       %(len(relabeledParams), 
                                                         len(relabelMap[parameterVar])))
                    else:
                        # e.g., x_1, ..., x_n -> y_1, ..., y_n
                        relabeledParams = compositeExpression(relabeledParams)
                else:
                    relabeledParams = compositeExpression(relabelMap[parameterVar])
                for relabeledParam in relabeledParams:
                    new_params.append(relabeledParam)
                    inner_reservations[relabeledParam] = parameterVar
            else:
                # Can perform a substition in indices of a parameter iteration:
                # x_1, ..., x_n
                new_params.append(parameter.substituted(inner_expr_map, relabelMap, 
                                                        reservedVars, assumptions))
                inner_reservations[parameterVar] = parameterVar

        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = [assumption for assumption in assumptions 
                             if assumption.freeVars().isdisjoint(new_params)]
                                      
        return new_params, inner_expr_map, inner_assumptions, inner_reservations
        
    def substituted(self, exprMap, relabelMap=None, reservedVars=None,
                    assumptions=USE_DEFAULTS):
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
        if len(exprMap)>0 and (self in exprMap):
            # the full expression is to be substituted
            return exprMap[self]._restrictionChecked(reservedVars)        
        if relabelMap is None: relabelMap = dict()
        assumptions = defaults.checkedAssumptions(assumptions)
        
        new_params, inner_expr_map, inner_assumptions, inner_reservations \
            = self._innerScopeSub(exprMap, relabelMap, reservedVars)
        
        try:
            # The lambda body with the substitutions.
            subbedBody = self.body.substituted(inner_expr_map, relabelMap, 
                                               inner_reservations,
                                               inner_assumptions)
        except ScopingViolation as e:
            raise ScopingViolation("Scoping violation while substituting"
                                    "%s.  %s"%(str(self), e.message))
        
        try:
            newLambda = Lambda(new_params, subbedBody, subbedConditions)
        except TypeError as e:
            raise ImproperSubstitution(e.args[0])
        except ValueError as e:
            raise ImproperSubstitution(e.args[0])            
        return newLambda
    
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
        return self.body.usedVars().union(set(self.parameterVarSet))\
                .union(self.conditions.usedVars())
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the 
        body+conditions minus the lambda parameter variables.  The lambda 
        function binds those variables.
        '''
        innerFreeVs = set(self.body.freeVars()).union(self.conditions.freeVars())
        return innerFreeVs - self.parameterVarSet

def common_lambda_map(expr1, expr2):
    pass


class LambdaError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ArgumentExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics
    def __str__(self):
        return ("Cannot extract argument(s); mappedExpr does not match this Lambda "
                "expression: " + self.specifics)

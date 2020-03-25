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
    from proveit._core_.expression.composite import Iter
    from proveit._core_.expression.operation.indexed_var import IndexedVar 
    if isinstance(parameter, Iter) and isinstance(parameter.body, IndexedVar):
        if parameter.body.index != parameter.parameter:
            raise TypeError("Parameter may be an Iter over IndexedVar objects "
                            "(e.g., x_1, ..., x_n, but the IndexedVar index must "
                            "match the Iter parameter.  %s fails this criterion."
                            %parameter)
        indexed_var = parameter.body
        return indexed_var.var
    elif isinstance(parameter, IndexedVar):
        return parameter.var
    elif isinstance(parameter, Variable):
        return parameter
    else:
        raise TypeError('Parameter must be a Variables, Indexed variable, or '
                        'iteration (Iter) over Indexed variables.  %s fails '
                        'to meet this requirement.'%parameter)

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
            raise TypeError('An Iter must be within an ExprTuple or ExprArray, '
                            'not directly as a Lambda body')
        self.body = body
                
        if _generic_expr is None:
            # Create a "generic" version (if not already) of the Lambda 
            # expression since the choice of parameter labeling is irrelevant.
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
                genericExpr = Lambda(generic_parameters, generic_body)
                defaults.automation = prev_automation # restore to previous value
            else:
                genericExpr = self
        elif _generic_expr == '.':
            genericExpr = self
        else:
            genericExpr = _generic_expr
        self._genericExpr = genericExpr
        sub_exprs = (self.parameter_or_parameters, self.body)
        Expression.__init__(self, ['Lambda'], sub_exprs)
    
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
        yield self.parameter
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
        if fence: outStr += r'\right]'
        return outStr
    
    def apply(self, *operands, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Apply this lambda map onto the given operands, returning the
        expression that results from applying the map.  Assumptions
        may be necessary to prove requirements that will be passed back
        if a requirements list is provided.  Requirements may be needed
        to ensure that operands are an appropriate length to match
        a corresponding iterated parameter.  Specifically, the Len of
        an ExprTuple containing the operands must equal the Len of an
        ExprTuple containing the iterated indices of the iterated parameter
        (see the example below).  Automation of the length proof will only
        be used for the last parameter entry; otherwise, the length proof
        should be performed in advance.
        
        For example, applying the Lambda
        (x, y_1, ..., y_3, z_i, ..., z_j) -> 
            x*y_1 + ... + x*y_3 + z_i + ... + z_j
        to operands (a, b, c, d, e_m, ..., e_n, f)
        will result in a*b + a*c + a*d + e_m + ... _ e_n + f provided that
        |(b, c, d)| = |(1, ..., 3)| is proven in advance and that
        |(e_m, ..., e_n, f)| = |(i, ..., j)| can be proven via automation.
        
        There are limitations with respect the Lambda map application involving
        iterated parameters when perfoming operation substitution in order to
        keep derivation rules (i.e., instantiation) simple.  For details,
        see the Iter.substituted documentation.
        '''
        return Lambda._apply(self.parameters, self.body, *operands,
                             assumptions=assumptions, requirements=requirements)
        
    @staticmethod 
    def _apply(parameters, body, *operands, 
               assumptions=USE_DEFAULTS, requirements=None):
        '''
        Static method version of Lambda.apply which is convenient for 
        doing 'apply' with an 'on-the-fly' effective Lambda that does not
        need to be initialized (for the sake of efficiency for an 
        Instantiation proof).
        '''
        from proveit import ExprTuple, Iter, ProofFailure
        from proveit.logic import Equals
        from proveit.iteration import Len
        
        # We will be appending to the requirements list if it is given
        # (or a throw-away list if it is not).
        if requirements is None: requirements = []
        
        # We will be matching operands with parameters in the proper order.
        operands_iter = iter(operands) 
        repl_map = dict() # for the Lambda body substitution
        try:
            # Loop through each parameter entry and match it with corresponding
            # operand(s).  Singular parameter entries match with singular
            # operand entries.  Iterated parameter entries match with
            # one or more operand entries which match in element-wise length
            # For example, (x_1, ..., x_n, y) has an element-wise lenght of
            # n+1.
            for parameter in parameters:
                if isinstance(parameter, Iter):
                    # This is a iterated parameter which corresponds with
                    # one or more operand entries in order to match the
                    # element-wise length.
                    param_tuple = ExprTuple(parameter)
                    param_indices = Iter(i, i, parameter.start_index, 
                                         parameter.end_index)
                    param_len = Len(ExprTuple(param_indices))
                    if paramters[-1] == parameter:
                        # This iterated parameter is the last entry,
                        # so it must encompass all remaining operands.
                        # We can attempt to prove the length requirement
                        # via automation.
                        param_operands = list(operands_iter)
                        param_operands_len = Len(ExprTuple(*param_operands))
                        len_req = Equals(param_operands_len, param_len)
                        try:
                            requirements.append(len_req.prove(assumptions))
                        except ProofFailure as e:
                            raise LambdaApplicationError(self, operands, assumptions,
                                                         "Failed to prove operand "
                                                         "length requirement: %s"
                                                         %str(e))
                    else:
                        # Collect enough operands to match the length of the
                        # iterated parameter.
                        param_operands = []
                        while True:
                            param_operands.append(next(operands_iter))
                            param_operands_len = Len(ExprTuple(*param_operands))
                            len_req = Equals(param_operands_len, param_len)
                            if len_req.proven(assumptions):
                                requirements.append(len_req)
                    # For the iterated parameter replacement, we map the 
                    # parameter variable to the parameter iteration tuple
                    # (e.g., x : (x_i, ..., x_n)) to indicate the index
                    # range and then map that iteration tuple to the
                    # actual operands to be replaced.
                    repl_map[getParamVar(parameter)] = param_tuple
                    repl_map[param_tuple] = param_operands
                else:
                    # This is a singular parameter which should match with a
                    # singular operator.
                    operand = next(operands_iter)
                    if isinstance(operand, Iter):
                        raise LambdaApplicationError(self, operands, assumptions,
                                                     "Singular parameters must "
                                                     "correspond with singular "
                                                     "operands: %s vs %s."
                                                     %(parameter, operands))
                        raise error
                    repl_map[parameter] = operand
        except StopIteration:
            raise LambdaApplicationError(self, operands, assumptions,
                                         "Parameter/operand length mismatch "
                                         "or unproven length equality for "
                                         "correspondence with %s."
                                         %str(parameter))
        return body.substituted(repl_map, assumptions=assumptions, 
                                requirements=requirements)
    
    def _inner_scope_sub(self, repl_map, reserved_vars, 
                         assumptions, requirements):
        '''
        Helper method for substituted (and used by Iter.substituted) which 
        handles the change in scope properly as well as parameter relabeling.
        '''
        
        from proveit import compositeExpression, Iter, ExprTuple
        
        # Within the lambda scope, we can relabel lambda parameters
        # to a different Variable, but any other kind of substitution of
        # a variable that happens to match a Lambda parameter variable
        # must be left behind as an external substitution with no effect on
        # the inner scope of the Lambda.
        inner_repl_map = {key:value for key, value in repl_map.items()
                          if (isinstance(value, Variable) or 
                              key not in self.parameterVarSet)}
        
        # Handle relabeling and variable reservations consistent with 
        # relabeling.
        inner_reserved_vars = dict() if reserved_vars is None else dict(reserved_vars)
        new_params = []
        
        for parameter, param_var in zip(self.parameters, self.parameterVars):
            # Note that lambda parameters introduce a new scope and don't need 
            # to, themselves, be restriction checked.  But they generate new 
            # inner restrictions that disallow any substitution from a variable 
            # that isn't in the new scope to a variable that is in the new 
            # scope. 
            # For example, we can relabel y to z in (x, y) -> f(x, y), but not 
            # f to x. 
            if param_var in inner_repl_map:
                # The parameter is being relabeled, simultaneous with the
                # substitution, so track the change with respect to the
                # new_params and inner_reservations.
                if isinstance(parameter, Iter):
                    # e.g., x_1, ..., x_n -> y_1, ..., y_n.
                    # It could also change the index range.  For example,
                    # x_i, ..., x_j -> y_1, ..., y_n.
                    subbed_param = parameter.substituted(inner_repl_map, 
                                                         reserved_vars, 
                                                         assumptions, requirements)
                else:
                    subbed_param = inner_repl_map[param_var]
                inner_reserved_vars[relabeled_param] = param_var
            else:
                # The parameter is not being relabeled.  However, if it
                # is an iteration, there could be a substitution in the indices
                # that we must account for:
                # e.g., x_i, ..., x_j -> x_1, ..., x_n.
                subbed_param = parameter.substituted(inner_repl_map, reserved_vars, 
                                                     assumptions, requirements)
                inner_reserved_vars[param_var] = param_var
            # Append new_params with the substituted version of this parameter.
            try:
                # If subbed_param is iterable (i.e., the parameter is an Iter
                # since Iter.substituted acts as a generator), use extend.
                new_params.extend(subbed_param)
            except TypeError:
                # Otherwise use append.
                new_params.append(subbed_param)

        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = [assumption for assumption in assumptions 
                             if assumption.freeVars().isdisjoint(new_params)]
                                      
        return new_params, inner_repl_map, inner_reserved_vars, inner_assumptions
        
    def substituted(self, repl_map, reserved_vars=None, 
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary 
        which maps Expressions to Expressions.  When used for instantiation,
        this should specifically map Variables to Expressions.  When there
        is a replacement for a Lambda parameter variable, it only impacts the
        inner scope of the Lambda if the replacement is also a variable and
        thus only a relabeling of the parameter.  Otherwise, only occurrences
        of the Variable external to the Lambda map will be substituted.
        
        reserved_vars is used internally to protect the "scope" of a
        Lambda map.  It is a dictionary that maps reserved variables 
        (i.e., new lambda parameter variables) to relabeling exceptions (i.e.,
        the corresponding old lambda parameter variable).  You may substitute 
        in an expression that uses a restricted variable except to relabel
        the parameter.
        
        'assumptions' and 'requirements' are used when an operator is
        substituted with a lambda map that has iterated parameters such that 
        the length of the parameters and operands are required to be equal.
        For more details, see Operation.substituted, Lambda.apply, and
        Iter.substituted (which is the sequence of calls involved).
        '''
        from proveit.logic import Forall
        
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]._restrictionChecked(reserved_vars)

        assumptions = defaults.checkedAssumptions(assumptions)
        
        # Use a helper method to handle some inner scope transformations.
        new_params, inner_repl_map, inner_reserved_vars, inner_assumptions \
            = self._inner_scope_sub(repl_map, reserved_vars,
                                    assumptions, requirements)
        
        try:
            # The lambda body with the substitutions.
            inner_requirements = []
            subbed_body = self.body.substituted(inner_repl_map, inner_reserved_vars,
                                                inner_assumptions, inner_requirements)
            # Translate from inner requirements to outer requirements
            # in a manner that respects the change in scope w.r.t.
            # lambda parameters.
            for requirement in inner_requirements:
                if requirement.freeVars().isdisjoint(new_params):
                    requirements.append(requirement)
                else:
                    # If the requirement involves any of the Lambda parameters,
                    # it must be generalized under these parameters to ensure
                    # there is no scoping violation since the scope of these
                    # parameters is within the new Lambda.
                    requirement_params = requirement.freeVars().intersection(new_params)
                    conditions = requirement.assumptions
                    requirement = requirement.generalize(requirement_params,
                                                         conditions=conditions)
                requirements.append(requirement)
            
        except ScopingViolation as e:
            raise ScopingViolation("Scoping violation while substituting"
                                    "%s.  %s"%(str(self), e.message))
        
            
        try:
            newLambda = Lambda(new_params, subbed_body)
        except TypeError as e:
            raise ImproperSubstitution(e.args[0])
        except ValueError as e:
            raise ImproperSubstitution(e.args[0])            
        return newLambda
    
    def relabeled(self, relabel_map):
        '''
        Return a variant of this Lambda expression with one or more
        of its parameter labels changed.  The resulting expression should
        be "equal" to the original (having the same meaning) but essentially
        has a different "style" (formats differently) and uses different
        labels for substitution purposes.
        
        TODO: we also need to handle parameter splitting transformations.
        '''
        for key, val in relabel_map.iteritems():
            if not isinstance(key, Variable):
                raise TypeError("relabel_map must map Variables to Variables. "
                                "%s key is not a Variable."%key)
            if not isinstance(val, Variable):
                raise TypeError("relabel_map must map Variables to Variables. "
                                "%s value is not a Variable."%val)
        result = self.substituted(relabel_map)
        assert result==self, "Relabeled version should be 'equal' to original"
        return result
    
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
        return self.body.usedVars().union(set(self.parameterVarSet))
        
    def freeVars(self):
        '''
        The free variables the lambda function are the free variables of the 
        body minus the lambda parameter variables.  The lambda 
        function binds those variables.
        '''
        innerFreeVs = set(self.body.freeVars())
        return innerFreeVs - self.parameterVarSet
    
    def freeIndexedVars(self, index):
        '''
        The free indexed variables of the lambda function are the free 
        indexed variables of the body minus any whose 'var' is in the
        set of lambda parameter variables.  The lambda function binds those 
        variables.
        '''
        innerFreeVs = set(self.body.freeIndexedVars(index))
        return {indexed_var for indexed_var in innerFreeVs 
                if indexed_var.var not in self.parameterVarSet}

class LambdaApplicationError(Exception):
    def __init__(self, lambda_map, operands, assumptions, extra_msg):
        self.lambda_map = lambda_map
        self.operands = operands
        self.assumptions = assumptions
        self.extra_msg = extra_msg
    def __str__(self):
        return ("Failure to apply %s to %s assuming %s: %s"
                %(self.lambda_map, self.operands, self.assumptions, self.extra_msg))

class ArgumentExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics
    def __str__(self):
        return ("Cannot extract argument(s); mappedExpr does not match this Lambda "
                "expression: " + self.specifics)

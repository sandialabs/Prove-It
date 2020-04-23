from proveit._core_.expression.expr import (Expression, MakeNotImplemented, 
                                            ImproperSubstitution,
                                            free_vars)
from proveit._core_.expression.label.var import safeDummyVar, safeDummyVars
from proveit._core_.defaults import defaults, USE_DEFAULTS

def getParamVar(parameter):
    '''
    Parameters may be variables, indexed variables, or iterations over indexed
    variables.  If it is either of the latter, the associated, intrinsic
    parameter variable (that is introduced in the new scopse) 
    is the variable of the Indexed expression.
    '''
    from proveit._core_.expression.label.label import TemporaryLabel
    from proveit._core_.expression.label import Variable
    from proveit._core_.expression.composite import ExprRange
    from proveit._core_.expression.operation.indexed_var import IndexedVar 
    if isinstance(parameter, ExprRange) and isinstance(parameter.body, IndexedVar):
        if parameter.body.index != parameter.parameter:
            raise TypeError("Parameter may be an ExprRange over IndexedVar objects "
                            "(e.g., x_1, ..., x_n, but the IndexedVar index must "
                            "match the ExprRange parameter.  %s fails this criterion."
                            %parameter)
        indexed_var = parameter.body
        return indexed_var.var
    elif isinstance(parameter, IndexedVar):
        var = parameter.var
        while isinstance(var, IndexedVar):
            # May be a nested IndexedVar.  We want the innermost var.
            var = var.var 
        return var
    elif isinstance(parameter, Variable) or isinstance(parameter, TemporaryLabel):
        return parameter
    else:
        raise TypeError('Parameter must be a Variables, Indexed variable, or '
                        'range (ExprRange) over Indexed variables.  %s fails '
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
        Each parameter must be a Variable or a range (ExprRange) of 
        indexed variables (IndexedVar).
        When there is a single parameter, there will be a 'parameter'
        attribute. Either way, there will be a 'parameters' attribute
        that bundles the one or more Variables into an ExprTuple.
        The 'body' attribute will be the lambda function body
        Expression.  The body may be singular or a composite.
        
        _generic_expr is used internally for efficiently rebuilding a Lambda.
        '''
        from proveit._core_.expression.composite import (
                compositeExpression, singleOrCompositeExpression, ExprRange)
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
            raise ParameterCollisionError(self.parameters)
        body = singleOrCompositeExpression(body)
        # After the singleOrCompositeExpression, this assertion should
        # not faile.
        assert isinstance(body, Expression) and not isinstance(body, ExprRange)
        self.body = body
                
        if _generic_expr is None:
            # Create a "generic" version (if not already) of the Lambda 
            # expression since the choice of parameter labeling is 
            # irrelevant.
            
            # Temporarily disable automation while making the
            # generic version.
            prev_automation = defaults.automation
            try:
                defaults.automation = False
                genericExpr = self._generic_version()
            finally:
                defaults.automation = prev_automation
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

    def _generic_version(self):
        '''
        Retrieve (and create if necessary) the generic version of this 
        Lambda expression in which its parameters are replaced with
        deterministic 'dummy' variables.
        '''
        if hasattr(self, '_genericExpr'):
            return self._genericExpr

        from proveit._core_.expression.operation.indexed_var import IndexedVar
        from proveit._core_.expression.composite import ExprTuple
        generic_body = self.body._generic_version()
        
        # If there are any Indexed variables, try to replace them
        # with temporary dummy variables: e.b., a_i -> q.
        # If they don't occur any other way, we can replace them
        # in the generic version.
        indexed_var_params = [param for param in self.parameters 
                              if isinstance(param, IndexedVar)]
        repl_map = dict()
        if len(indexed_var_params) > 0:
            indexed_var_replacements = safeDummyVars(len(indexed_var_params),
                                                     generic_body)
            repl_map = {indexed_var:repl for indexed_var, repl 
                        in zip(indexed_var_params, indexed_var_replacements)}
            generic_body = generic_body._substituted(repl_map)
            generic_body_free_vars = generic_body._free_vars()
            for indexed_var_param in indexed_var_params:
                if getParamVar(indexed_var_param) in generic_body_free_vars:
                    # The variable of indexed_var_param occurs in other
                    # forms than just the indexed_var_param itself.
                    # We can't know for sure if this is incorrect
                    # (a_i could have been replaced with a_n in some
                    # occurrence assuming i=n), but we do need to
                    # revert the replacement to be safe.
                    generic_body = generic_body._substituted(
                            {repl_map[indexed_var_param]:indexed_var_param})
                    repl_map.pop(indexed_var_param)
        if len(repl_map) > 0:
            # Made indexed variable replacements.
            parameters = \
                ExprTuple(*[repl_map[param] if param in repl_map else param
                            for param in self.parameters])
            parameter_vars = [getParamVar(param) for param in parameters]
            parameter_var_set = set(parameter_vars)
        else:
            parameters = self.parameters
            parameter_vars = self.parameterVars
            parameter_var_set = self.parameterVarSet
        
        generic_body_vars = generic_body._used_vars()
        disallowed_vars = (generic_body_vars-parameter_var_set)
        generic_param_vars = tuple(safeDummyVars(len(parameter_vars), 
                                                 *disallowed_vars))
        if len(repl_map) > 0 or generic_param_vars != parameter_vars:
            # Create the generic version via relabeling.
            relabel_map = {param:generic_param for param, generic_param 
                           in zip(parameter_vars, generic_param_vars)}
            generic_parameters = parameters._generic_version()
            generic_parameters = generic_parameters._relabeled(relabel_map)
            generic_body = generic_body._relabeled(relabel_map)
            return Lambda(generic_parameters, generic_body)
        else:
            return self
    
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
        return self.extractArguments(mappedExpr)[0]

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
        yield self.parameter_or_parameters
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
        Apply this lambda map onto the given operands (a beta reduction
        in the lambda calculus terminology), returning the
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
        see the ExprRange._substituted documentation.
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
        Instantiation proof).  It also has the flexibility of allowing
        an initial 'repl_map' to start with, which will me amended according
        to paramater:operand mappings.
        '''
        from proveit import (ExprTuple, ExprRange, ProofFailure, 
                             safeDummyVar, Len)
        from proveit.logic import Equals, EvaluationError
        
        # We will be appending to the requirements list if it is given
        # (or a throw-away list if it is not).
        if requirements is None: requirements = []
        assumptions = defaults.checkedAssumptions(assumptions)
        
        # We will be matching operands with parameters in the proper 
        # order and adding corresponding entries to the replacement map.
        repl_map = dict()
        operands_iter = iter(operands)
        try:
            # Loop through each parameter entry and match it with corresponding
            # operand(s).  Singular parameter entries match with singular
            # operand entries.  Iterated parameter entries match with
            # one or more operand entries which match in element-wise length
            # For example, (x_1, ..., x_n, y) has an element-wise lenght of
            # n+1.
            for parameter in parameters:
                if isinstance(parameter, ExprRange):
                    from proveit.number import zero, one
                    # This is a iterated parameter which corresponds with
                    # one or more operand entries in order to match the
                    # element-wise length.
                    param_tuple = ExprTuple(parameter)
                    idx_var = safeDummyVar(*parameters, body)
                    param_indices = ExprRange(idx_var, idx_var, 
                                              parameter.start_index, 
                                              parameter.end_index)
                    param_len = Len(ExprTuple(param_indices))
                    if parameters[-1] == parameter:
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
                            raise LambdaApplicationError(parameters, body, 
                                                         operands, assumptions,
                                                         "Failed to prove operand "
                                                         "length requirement: %s"
                                                         %str(e))
                    else:
                        # Collect enough operands to match the length of the
                        # iterated parameter.
                        param_operands = []
                        while True:
                            param_operands_len = Len(ExprTuple(*param_operands))
                            len_req = Equals(param_operands_len, param_len)
                            if len_req.proven(assumptions):
                                requirements.append(len_req.prove(assumptions))
                                break # we have a match
                            param_operands.append(next(operands_iter))
                    # For the iterated parameter replacement, we map the 
                    # parameter variable to the parameter iteration tuple
                    # (e.g., x : (x_i, ..., x_n)) to indicate the index
                    # range and then map that iteration tuple to the
                    # actual operands to be replaced.
                    repl_map[getParamVar(parameter)] = param_tuple
                    repl_map[param_tuple] = ExprTuple(*param_operands)
                else:
                    # This is a singular parameter which should match
                    # with a singular operator or range(s) with known
                    # length summing up to 1 (may have zero length
                    # ranges).
                    operand = next(operands_iter)
                    if isinstance(operand, ExprRange):
                        # Rangle lengths must be known values and sum 
                        # to 1.
                        try:
                            while True:
                                operand_len_evaluation = \
                                    Len(operand).evaluation(
                                            assumptions=assumptions)
                                requirements.append(operand_len_evaluation)
                                operand_len_val = operand_len_evaluation.rhs
                                if operand_len_val == one:
                                    break # Good to go.
                                elif operand_len_val == zero:
                                    # Keep going until we get a length
                                    # of 1.
                                    operand = next(operands_iter)
                                else:
                                    # No good.
                                    raise LambdaApplicationError(
                                            parameter, body, operands,
                                            assumptions,
                                            "Parameter/argument length "
                                            "mismatch 1 vs %s"
                                            %operand_len_evaluation.rhs)
                        except EvaluationError:                                                        
                            raise LambdaApplicationError(
                                    parameters, body, operands, assumptions,
                                    "Singular parameters must correspond "
                                    "with singular operands or ranges with "
                                    "lengths known to sum to 1: %s vs %s."
                                    %(parameter, operand))
                    repl_map[parameter] = operand
        except StopIteration:
            raise LambdaApplicationError(parameters, body, 
                                         operands, assumptions,
                                         "Parameter/argument length mismatch "
                                         "or unproven length equality for "
                                         "correspondence with %s."
                                         %str(parameter))
        # Make sure all of the operands were consumed.
        try:
            next(operands_iter)
            # All operands were not consumed.
            raise LambdaApplicationError(parameters, body, 
                                         operands, assumptions,
                                         "Too many arguments")
        except StopIteration:
            pass # Good.  All operands were consumed.
        try:
            return body._substituted(repl_map, assumptions=assumptions, 
                                     requirements=requirements)
        except ImproperSubstitution as e:
            raise LambdaApplicationError(parameters, body, 
                                         operands, assumptions,
                                         "Improper substitution: %s "
                                         %str(e))
    
    def _inner_scope_sub(self, repl_map, assumptions, requirements):
        '''
        Helper method for substituted (and used by ExprRange.substituted) which 
        handles the change in scope properly as well as parameter relabeling.
        '''
        
        from proveit import Variable, ExprRange
        
        body_free_vars = self.body._free_vars()
        non_param_free_vars = body_free_vars - self.parameterVarSet
                
        # Within the lambda scope, we can relabel lambda parameters
        # to a different Variable, but any other kind of substitution of
        # a variable that happens to match a Lambda parameter variable
        # must be left behind as an external substitution with no effect on
        # the inner scope of the Lambda.
        inner_repl_map = {key:value for key, value in repl_map.items()
                          if (key in body_free_vars and (
                                  isinstance(value, Variable) or 
                                  key not in self.parameterVarSet))}
        
        # Free variables of the replacements must not collide with
        # the parameter variables.  If there are collisions, relabel
        # the parameter variables to something safe.  First, get the
        # free variables of the body and the replacements.
        restricted_vars = non_param_free_vars.union(
                *[value._free_vars() for key, value in inner_repl_map.items()
                 if key not in self.parameterVarSet])
        for param_var in self.parameterVarSet:
            if inner_repl_map.get(param_var, param_var) in restricted_vars:
                # Avoid this collision by relabeling to a safe dummy 
                # variable.
                inner_repl_map[param_var] = safeDummyVar(*restricted_vars)
            else:
                restricted_vars.add(param_var)
        
        # Generate the new set of parameters which may be relabeled or, 
        # in the case of a parameter range, may be altered due a change
        # in the start/end indices.  For example, we may have
        # x_1, ..., x_n go to 
        #       x_1, ..., x_3 with n:3
        #       x_1 with n:1
        #       or empty with n:0
        new_params = []
        for parameter, param_var in zip(self.parameters, self.parameterVars):
            if isinstance(parameter, ExprRange):
                subbed_param = parameter._substituted_entries(
                        inner_repl_map, assumptions, requirements)
                new_params.extend(subbed_param)
            else:
                subbed_param = parameter._substituted(
                        inner_repl_map, assumptions, requirements)
                new_params.append(subbed_param)
        
        if len({getParamVar(param) for param in new_params}) != len(new_params):
            raise ParameterCollisionError(new_params)

        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = [assumption for assumption in assumptions 
                             if free_vars(assumption).isdisjoint(new_params)]
                                      
        return new_params, inner_repl_map, inner_assumptions
        
    def _substituted(self, repl_map, assumptions=USE_DEFAULTS, 
                     requirements=None):
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
        ExprRange.substituted (which is the sequence of calls involved).
        '''
        
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]

        assumptions = defaults.checkedAssumptions(assumptions)
        
        # Use a helper method to handle some inner scope transformations.
        new_params, inner_repl_map, inner_assumptions \
            = self._inner_scope_sub(repl_map, assumptions, requirements)
        
        # The lambda body with the substitutions.
        inner_requirements = []
        subbed_body = self.body._substituted(
                inner_repl_map, inner_assumptions, inner_requirements)
        # Translate from inner requirements to outer requirements
        # in a manner that respects the change in scope w.r.t.
        # lambda parameters.
        for requirement in inner_requirements:
            if free_vars(requirement).isdisjoint(new_params):
                requirements.append(requirement)
            else:
                # If the requirement involves any of the Lambda 
                # parameters, it must be generalized under these
                # parameters to ensure there is no scoping violation 
                # since the scope of these parameters is within the new
                # Lambda.
                requirement_params = \
                    free_vars(requirement).intersection(new_params)
                conditions = requirement.assumptions
                requirement = requirement.generalize(requirement_params,
                                                     conditions=conditions)
            requirements.append(requirement)
        
        try:
            substituted = Lambda(new_params, subbed_body)
        except TypeError as e:
            raise ImproperSubstitution(e.args[0])
        except ValueError as e:
            raise ImproperSubstitution(e.args[0])
        
        return substituted
    
    """
    def relabeled(self, relabel_map):
        '''
        Return a variant of this Lambda expression with one or more
        of its parameter labels changed.  The resulting expression should
        be "equal" to the original (having the same meaning) but essentially
        has a different "style" (formats differently) and uses different
        labels for substitution purposes.
        
        TODO: we also need to handle parameter splitting transformations.
        '''
        from proveit import Variable
        for key, val in relabel_map.items():
            if not isinstance(key, Variable):
                raise TypeError("relabel_map must map Variables to Variables. "
                                "%s key is not a Variable."%key)
            if not isinstance(val, Variable):
                raise TypeError("relabel_map must map Variables to Variables. "
                                "%s value is not a Variable."%val)
        result = self._substituted(relabel_map)
        assert result==self, "Relabeled version should be 'equal' to original"
        return result
    """
    
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
    
    def _used_vars(self):
        '''
        The used variables of the lambda function are the used variables of the 
        body plus the lambda parameter variables.
        '''
        return self.body._used_vars().union(set(self.parameterVarSet))
        
    def _free_vars(self, exclusions=frozenset()):
        '''
        The free variables the lambda function are the free variables of the 
        body minus the lambda parameter variables.  The lambda 
        function binds those variables.
        '''
        if self in exclusions:         
            return set() # this is excluded
        innerFreeVs = set(self.body._free_vars(exclusions=exclusions))
        return innerFreeVs - self.parameterVarSet
    
    def _free_indexed_vars(self, index):
        '''
        The free indexed variables of the lambda function are the free 
        indexed variables of the body minus any whose 'var' is in the
        set of lambda parameter variables.  The lambda function binds those 
        variables.
        '''
        innerFreeVs = set(self.body._free_indexed_vars(index))
        return {indexed_var for indexed_var in innerFreeVs 
                if indexed_var.var not in self.parameterVarSet}

class ParameterCollisionError(Exception):
    def __init__(self, parameters):
        self.parameters = parameters
    def __str__(self):
        return ("Parameter variables must be unique.  %s does not satisfy "
                "this criterion."%self.parameters)

class LambdaApplicationError(Exception):
    def __init__(self, parameters, body, operands, assumptions, extra_msg):
        self.lambda_map = Lambda(parameters, body)
        self.operands = operands
        self.assumptions = assumptions
        self.extra_msg = extra_msg
    def __str__(self):
        assumption_str = ''
        if len(self.assumptions) > 0:
            assumption_str = ' assuming %s'%str(self.assumptions)
        return ("Failure to apply %s to %s%s: %s"
                %(self.lambda_map, self.operands, assumption_str, self.extra_msg))

class ArgumentExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics
    def __str__(self):
        return ("Cannot extract argument(s); mappedExpr does not match this Lambda "
                "expression: " + self.specifics)

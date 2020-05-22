from proveit._core_.expression.expr import (Expression, MakeNotImplemented, 
                                            ImproperReplacement,
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

def valid_params(expr_tuple):
    '''
    Return True iff all the entries of the given "expr_tuple" form a
    valid tuple of parameters.
    '''
    # See if this is an allowed expansion of a 
    # range of parameters.
    try:
        expanded_vars = {getParamVar(expanded_param)
                         for expanded_param in expr_tuple.entries}
        if len(expanded_vars)!=len(expr_tuple.entries):
            # Parameter variables must be unique to be valid.
            return False
        # All valid and unique parameter entries.
        return True
    except TypeError:
        # One of the entries is not valid.
        return False

class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameter(s) to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the 
    parameters and sin(x^2 + y) is the body.  Each parameter must be a
    Variable.  Note that the body of a Lambda may be a Conditional
    such that the mapping is only defined when one of the conditions is
    satisfied.
    '''
    def __init__(self, parameter_or_parameters, body, *, _generic_expr=None):
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
                compositeExpression, singleOrCompositeExpression)
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
        
        # Parameter variables may not occur multiple times.
        if len(self.parameterVarSet) != len(self.parameters):
            raise ParameterCollisionError(
                    self.parameters, "Parameter variables must be unique")
        
        # Parameter variables may not occur as free variables of
        # any of the parameter indexes.
        free_vars_of_param_indices = self._free_vars_of_parameter_indices()
        if not free_vars_of_param_indices.isdisjoint(self.parameterVarSet):
            raise ParameterCollisionError(
                    self.parameters, ("Parameter variables may not occur as "
                                      "free variables in parameter indices"))         
        
        # Note: a Lambda body may be an ExprRange which is useful
        # for making nested ranges of ranges.
        # However, this is not allowed in the "operation substitution"
        # reduction because it does not respect arity of the function
        # outcome.  Without such a resctriction you end up being able 
        # to prove that
        # |f_1(i_1), ..., f_1(j_1), ......, f_n(i_n), ..., f_n(j_n)| = n
        # WHICH IS WRONG, IN GENERAL!
        body = singleOrCompositeExpression(body, 
                                           wrap_expr_range_in_tuple=False)
        # After the singleOrCompositeExpression, this assertion should
        # not fail.
        assert isinstance(body, Expression)
        self.body = body
        
        """
        # For each ExprRange parameter entry, map the corresponding
        # parameter variable to the set of constant index shifts of
        # are employed (e.g., x_{k+2} has a constant shift of 2).
        # The span is the max-min of the constant shifts.  Denoting this
        # span as s, then the first s elements and last s elements
        # of any replacement must be singuler elements and not ranges.
        param_var_index_shifts = dict()
        for param_var, param in zip(self.parameterVars, self.parameters):
            if isinstance(param, ExprRange):
                index_shifts = {0}
                self.body._var_index_shifts_in_ranges(param_var,
                                                      index_shifts)
                param_var_index_shifts[param_var] = index_shifts
        self.param_var_index_shifts = param_var_index_shifts
        
        # When a Lambda expression introduces a variable in a new scope
        # with a parameter entry that is an IndexedVar or a range
        # of IndexedVars, its occurrences must all match that
        # index or range or shifts as specified via 
        # self.param_var_index_shift_range.
        Lambda._check_all_param_occurrences(self.parameters, body,
                                            self.param_var_index_shifts)
        """
        
        # The '_max_in_scope_bound_vars' attribute is used to make 
        # unique variable assignments for Lambda parameters in the
        # "generic version" which is invarian under 
        # alpha-conversion.  For a Lambda, this attribute is
        # set ahead of time.
        self._max_in_scope_bound_vars = \
            (max(self.parameters._max_in_scope_bound_vars, 
                 self.body._max_in_scope_bound_vars)
             + len(self.parameterVars))
        
        # Parameter variables that are indexed and not fully and
        # explicitly covered under the currently introduced range 
        # cannot be relabeled.
        explicitly_free_var_ranges = \
            Lambda._explicitly_free_var_ranges(
                    self.parameters, self.parameterVars, self.body)
        self.nonrelabelable_param_vars = \
            {var for var, var_form in explicitly_free_var_ranges.items()
            if var in self.parameterVarSet}
        
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
    
    def _free_vars_of_parameter_indices(self):
        '''
        Return the set of free variables of the indices of all
        of the parameters of this Lambda expression.
        '''
        from proveit._core_.expression.composite import ExprRange
        from proveit._core_.expression.operation.indexed_var import IndexedVar 
        free_vars_of_indices = set()
        for parameter in self.parameters:
            if (isinstance(parameter, ExprRange) and 
                    isinstance(parameter.body, IndexedVar)):
                free_vars_of_indices.update(free_vars(parameter.start_index))
                free_vars_of_indices.update(free_vars(parameter.end_index))
            elif isinstance(parameter, IndexedVar):
                free_vars_of_indices.update(free_vars(parameter.index))
        return free_vars_of_indices
    
    def _generic_version(self):
        '''
        Retrieve (and create if necessary) the generic version of this 
        Lambda expression in which its parameters are replaced with
        deterministic 'dummy' variables.
        '''
        from proveit._core_.expression.composite import ExprRange
        
        if hasattr(self, '_genericExpr'):
            return self._genericExpr
        
        # Except for the variables in self.nonrelabelable_param_vars,
        # relabel them to something deterministic independent of the
        # original labels.
        # Note: If there are any direct indexed variable parameters
        # (as opposed to a range of indexed variables) that are 
        # relabelable, replace them with the variable being indexed 
        # in the generic version
        parameterVars = self.parameterVars
        parameters = self.parameters
        bound_parameter_vars = \
            [param_var if isinstance(param, ExprRange) else param
             for param_var, param in zip(parameterVars, parameters)
             if param_var not in self.nonrelabelable_param_vars] 
        
        # Assign unique variables based upon then maximum number
        # of bound variables in any internal scope, subtract the
        # number of new parameters, and add the number of
        # unbound (free) variables.
        # To ensure assignments are deterministic (not rearranged in a 
        # hysteretic manner), we use a starting index that is the 
        # maximum number of in-scope bound variables plus the number
        # of free variables, then we skip over the free variables as 
        # they occur.
        lambda_free_vars = free_vars(self.body) - set(bound_parameter_vars)
        start_index = (self._max_in_scope_bound_vars - len(parameters) + 
                       len(lambda_free_vars))
        generic_param_vars = list(reversed(
                safeDummyVars(len(bound_parameter_vars), *lambda_free_vars,
                              start_index=start_index)))
        
        if generic_param_vars != bound_parameter_vars:
            # Create the generic version via relabeling.
            relabel_map = \
                {param_var:generic_param_var for param_var, generic_param_var
                 in zip(bound_parameter_vars, generic_param_vars)}
            generic_parameters = parameters._generic_version()
            generic_parameters = generic_parameters.replaced(relabel_map)
            generic_body = self.body._generic_version()
            generic_body = generic_body.replaced(relabel_map)
            generic_body = generic_body._generic_version()
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
        lambda_sub_expr = self.body
        mapped_sub_expr = mappedExpr
        if len(self.parameters)==1 and self.body==self.parameter:
            # Simple case of x -> x.  Just return the mappedExpr as the
            # one argument.
            return [mappedExpr]
        param_values = [None]*len(parameters)
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
        return Lambda._string(self.parameters, self.body, **kwargs)
    
    @staticmethod
    def _string(parameters, body, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        outStr = '[' if fence else ''
        parameterListStr = ', '.join([parameter.string(abbrev=True) for parameter 
                                      in parameters])
        if parameters.singular():
            outStr += parameterListStr + ' -> '
        else:
            outStr += '(' + parameterListStr + ') -> '
        outStr += body.string(fence=True)
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
    
    def apply(self, *operands, equiv_alt_expansions=None,
              allow_relabeling=False, assumptions=USE_DEFAULTS, 
              requirements=None):
        '''
        Apply this lambda map onto the given operands (a beta reduction
        in the lambda calculus terminology), returning the
        expression that results from applying the map.  Assumptions
        may be necessary to prove requirements that will be passed back
        if a requirements list is provided.  Requirements may be needed
        to ensure that operands are an appropriate length to match
        a corresponding ExprRange of parameters.  Specifically, the Len 
        of an ExprTuple containing the operands must equal the Len of an
        ExprTuple containing the range of indices covered by a 
        corresponding parameter range (see the example below).  Full 
        automation of the  length proof will only be performed for the 
        last parameter entry; proving the length equivalence may need to
        be performed in advance.
        
        For example, applying the Lambda
        (x, y_1, ..., y_3, z_i, ..., z_j) -> 
            x*y_1 + ... + x*y_3 + z_i + ... + z_j
        to operands (a, b, c, d, e_m, ..., e_n, f)
        will result in a*b + a*c + a*d + e_m + ... _ e_n + f provided 
        that|(b, c, d)| = |(1, ..., 3)| is proven in advance and that
        |(e_m, ..., e_n, f)| = |(i, ..., j)| can be proven via 
        automation.
        
        A dictionary may be provided for equiv_alt_expansions to
        accomplish instantiation of ranges of parameters with more
        versatility.  For example, given the following Lambda
        (x_1, ..., x_{n+1}) -> (x_1 < x_{1+1}) and ... 
                                   and (x_n < x_{n+1})
        we can apply this on the following operands:
            (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
        along with the following entries in equiv_alt_expansions
        (x_1, ..., x_n, x_{n+1}) : 
            (a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1}, b_{n-k})
        (x_1, x_{1+1}, ..., x_{n+1}) :
            (a_1, a_{1+1}, ..., a_{k+1}, b_1, 
             b_{1+1}, ..., b_{(n-k-1)+1})
        to obtain
        (a_1 < a_{1+1}) and ... and (a_k < a_{k+1}) and a_k < b_1
            and (b_1 < b_{1+1}) and ... and (b_{n-k-1} < b_{(n-k-1)+1})
        under the following requirements:
        |(a_1, ..., a_{k+1}, b_1, ..., b_{n-k})| = |(1, ..., n+1)|
        (1, ..., n) = (1, ..., n, n+1)
        (1, ..., n) = (1, 1+1, ..., n+1)
        (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
            = (a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1}, b_{n-k})
        (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
            = (a_1, a_{1+1}, ..., a_{k+1}, b_1, 
               b_{1+1}, ..., b_{(n-k-1)+1})
        |({a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1})| 
            = |(1, ..., n)|
        |(a_{1+1}, ..., a_{k+1}, b_1, b_{1+1}, ..., b_{(n-k-1)+1})|
            = |(1+1, ..., n+1)|        
        
        If allow relabeling is True then inn
        
        There are limitations with respect the Lambda map application
        involving parameter ranges when perfoming operation 
        substitution in order to keep derivation rules (i.e., 
        instantiation) simple.  For details, see the 
        ExprRange.replaced documentation.
        '''
        return Lambda._apply(
                self.parameters, self.body, *operands, 
                equiv_alt_expansions=equiv_alt_expansions,
                allow_relabeling=allow_relabeling,
                assumptions=assumptions, requirements=requirements,
                parameter_vars=self.parameterVars)
    
    @staticmethod 
    def _apply(parameters, body, *operands, equiv_alt_expansions=None,
               allow_relabeling=False,
               assumptions=USE_DEFAULTS, requirements=None,
               parameter_vars=None):
        '''
        Static method version of Lambda.apply which is convenient for 
        doing 'apply' with an 'on-the-fly' effective Lambda that does 
        not need to be initialized (for the sake of efficiency for an 
        Instantiation proof).  It also has the flexibility of allowing
        an initial 'repl_map' to start with, which will me amended 
        according to paramater:operand mappings.
        '''
        from proveit import (ExprTuple, extract_indices)
        from proveit.logic import Equals
        
        try:
            if parameter_vars is None:
                parameter_vars = \
                    [getParamVar(parameter) for parameter in parameters]
        except TypeError as e:
            raise TypeError("Invalid ad-hoc Lambda parameters, %s:\n%s"
                            %(parameters, str(e)))
        
        # We will be appending to the requirements list if it is given
        # (or a throw-away list if it is not).
        if requirements is None: requirements = []
        assumptions = defaults.checkedAssumptions(assumptions)
        
        # We will be matching operands with parameters in the proper 
        # order and adding corresponding entries to the replacement map.
        repl_map = dict()
        extract_param_replacements(
                parameters, parameter_vars, body, operands,
                assumptions, requirements, repl_map)
        
        # Add repl_map entries resulting from equiv_alt_expansions.
        
        # For updating the repl_map:
        repl_map_extensions = dict()
        # Map variables to sets of tuples representing that variable 
        # being consecutively indexed over the same range as in the
        # parameters.  `repl_map` will be updated with this information.
        var_range_forms = dict()
        if equiv_alt_expansions is not None:
            if not isinstance(equiv_alt_expansions, dict):
                raise TypeError("'equiv_alt_expansions' must be a dict")
            for var_tuple, expansion_tuple in equiv_alt_expansions.items():
                if not isinstance(var_tuple, ExprTuple):
                    raise TypeError("'equiv_alt_expansions' keys must be "
                                    "ExprTuple objects; %s is a %s."
                                    %(var_tuple, var_tuple.__class__))
                if not isinstance(expansion_tuple, ExprTuple):
                    raise TypeError("'equiv_alt_expansions' values must be "
                                    "ExprTuple objects; %s is a %s."
                                    %(expansion_tuple, 
                                      expansion_tuple.__class__))
                param_var = None
                for var_tuple_entry in var_tuple:
                    try:
                        if param_var is None:
                            param_var = getParamVar(var_tuple_entry)
                        else:
                            if getParamVar(var_tuple_entry) != param_var:
                                raise ValueError
                    except (TypeError, ValueError):
                        raise ValueError(
                                "'equiv_alt_expansions' values must be "
                                "a tuple containing variables, indexed "
                                "variables, or ranges of indexed variables "
                                "all of the same variable and with no "
                                "internal shifts.  %s does not "
                                "meet this requirement."%var_tuple)
                expansion_set = repl_map.get(param_var, None)
                if expansion_set is None:
                    raise LambdaApplicationError(
                            parameters, body, operands, assumptions,
                            equiv_alt_expansions,
                            "'equiv_alt_expansions' values must represent "
                            "a tuple of consecutive indexed variables that "
                            "corresponds with a range of parameters "
                            "(with no shift in ExprRange indices): "
                            "%s is not found in %s."
                            %(var_tuple, repl_map.keys()))
                assert len(expansion_set)==1
                # We need to ensure that the tuples of indices match.
                orig_params = list(expansion_set)[0]
                indices_eq_req = Equals(extract_indices(var_tuple),
                                        extract_indices(orig_params))
                if indices_eq_req.lhs != indices_eq_req.rhs:
                    requirements.append(indices_eq_req.prove(assumptions))
                # We need to ensure that the tuple expansions are equal.
                orig_expansion = repl_map[orig_params]
                eq_expansion_req = Equals(expansion_tuple, orig_expansion)
                if eq_expansion_req.lhs != eq_expansion_req.rhs:
                    requirements.append(eq_expansion_req.prove(assumptions))
                # Now add new entries to repl_map_extensions for the 
                # new expansion and components corresponding to the
                # components of the var_tuple.
                cur_repl_map_extensions = dict()
                cur_repl_map_extensions[var_tuple] = expansion_tuple
                try:
                    extract_param_replacements(
                            var_tuple, [param_var]*len(var_tuple), 
                            var_tuple, expansion_tuple, assumptions, 
                            requirements, cur_repl_map_extensions)
                except LambdaApplicationError as e:
                    raise LambdaApplicationError(
                            parameters, body, operands, assumptions,
                            equiv_alt_expansions,
                            "Unable to match 'equiv_alt_expansions' "
                            "values entries to a key entry for key & value "
                            "%s & %s.\n%s."
                            %(var_tuple, expansion_tuple, str(e)))
                # Update 'var_tuple_map'
                if param_var not in var_range_forms:
                    var_range_forms[param_var] = set(expansion_set)
                var_range_forms[param_var].add(var_tuple)
                repl_map_extensions.update(cur_repl_map_extensions)
                
        if len(repl_map_extensions) > 0:
            repl_map.update(repl_map_extensions)
            repl_map.update(var_range_forms)
        try:
            return body.replaced(
                    repl_map, allow_relabeling, assumptions=assumptions, 
                    requirements=requirements)
        except ImproperReplacement as e:
            raise LambdaApplicationError(
                    parameters, body, operands, assumptions,
                    equiv_alt_expansions,
                    "Improper replacement: %s "%str(e))
        except TypeError as e:
            raise LambdaApplicationError(
                    parameters, body, operands, assumptions,
                    equiv_alt_expansions,
                    "TypeError: %s "%str(e))
    
    """
    @staticmethod
    def _add_range_to_repl_map(parameter, param_var, param_operands, 
                               index_shifts, repl_map, requirements):
        '''
        For the iterated parameter replacement, we map the 
        parameter variable to a tuple with the parameter iteration 
        ExprTuple and the set of constant 'index_shifts' employed by
        that parameter.
        (e.g., x : ((x_i, ..., x_n), index_shifts))
        Then map that iteration tuple to the
        actual operands to be replaced
        (e.g., (x_i, ..., x_n) : <whatever>).
        If there are index shifts for the parameter, also add
        the shifted versions
        (e.g., (x_{i+1}, ..., x_{(n-1}+1}) : <whatever-shifted>)
        where the range starts & ends of the shifted/non-shifted 
        versions are all in correspondence with each other.  
        For example, given
        param_operands = (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1})
        and index_shifts of {-1, 0, 1}.  Then
        for shift 0 we have
        (x_1, ..., x_{n+1}) : 
                (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1})
        for shift 1 we have
        (x_1, ..., x_n) : 
                (y_1, ..., y_k, y_{k+1}, q, z_1, ..., z_k)
        (x_{1+1}, ..., x_{n+1}) : 
                (y_{1+1}, ..., y_{k+1}, q, z_1, z_{1+1}, ..., z_{k+1})
        for shift -1 we have
        (x_2, ..., x_{n+1}) : 
                (y_2, ..., y_{k+1}, q, z_1, z_2, ..., z_k)
        (x_{2-1}, ..., x_{(n+1)-1}) : 
                (y_{2-1}, ..., y_{(k+1)-1}, y_{k+1}, 
                 q, z_{2-1}, ..., z_{(k+1)-1})
        Note that among the group for each shift, the expression
        ranges have the same pattern.  In this example, for shift 1, 
        the pattern is (1 to k range, singular element, 1 to k range) 
        and for shift -1 the pattern is 
        (2 to k+1 range, singular element, 2 to k+1 range).
            
        As requirements, in this example, we would have
            (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1}) =
            (y_1, ..., y_k, y_{k+1}, q, z_1, ..., z_k, z_{k+1});
            (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1}) =
            (y_1, y_{1+1}, ..., y_{k+1}, q, z_1, z_{1+1}, ..., z_{k+1});
            (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1}) =
            (y_1, y_2, ..., y_{k+1}, q, z_1, z_2, ..., z_k);
            (y_1, ..., y_{k+1}, q, z_1, ..., z_{k+1}) =
            (y_{2-1}, ..., y_{(k+1)-1}, q, y_{k+1},
             z_{2-1}, ..., z_{(k+1)-1}, q, z_{k+1})
        '''
        from proveit import ExprTuple, ExprRange
        from proveit.relation import TransRelUpdater
        from proveit.number import (const_shift_decomposition,
                                    const_shift_composition)
        assert isinstance(parameter, ExprRange)
        start_decomp = const_shift_decomposition(parameter.start_index)
        end_decomp = const_shift_decomposition(parameter.end_index)
        param_var = getParamVar(parameter)
        param_tuple = ExprTuple(parameter)
        repl_map[param_var] = set([param_tuple])
        repl_map[param_tuple] = ExprTuple(*param_operands)
        assert 0 in index_shifts
        nonzero_index_shifts = index_shifts.difference({0})
        # For each index shift, we'll generate replacements from
        # zero to the extreme of that index shift that will match
        # range patterns.
        for extreme_shift in nonzero_index_shifts:
            # Figure out the start/end indices for this 
            # "extreme_shift" that allows the full range of 
            # shiftin out to the extreme.
            start_index = parameter.start_index
            end_index = parameter.start_index
            if extreme_shift < 0:
                start_index = const_shift_composition(
                        start_decomp[0], start_decomp[1]-extreme_shift)
            else:
                end_index = const_shift_composition(
                        end_decomp[0], end_decomp[1]-extreme_shift)
            param_tuple = ExprRange(parameter.parameter, param_var,
                                    start_index, end_index)
            sgn = -1 if extreme_shift < 0 else 1
            for index_shift in range(abs(extreme_shift)+1):
                index_shift = sgn*index_shift
                eq = TransRelUpdater(param_tuple)
                for entry in param_operands:
                    if isinstance(entry, ExprRange):
                        if extreme_shift > 0:
                            n_front_partition = index_shift
                            n_back_partition = extreme_shift - index_shift
                        else:
                            n_front_partition = -extreme_shift + index_shift
                            n_back_partition = -index_shift
                        operand_start_decomp = \
                            const_shift_decomposition(entry.start_index)
                        operand_end_decomp = \
                            const_shift_decomposition(entry.end_index)
                        start_index = entry.start_index
                        end_index = entry.start_index
                        if index_shift < 0:
                            start_index = const_shift_composition(
                                    operand_start_decomp[0], 
                                    operand_start_decomp[1]-index_shift)
                        else:
                            end_index = const_shift_composition(
                                    operand_end_decomp[0], 
                                    operand_end_decomp[1]-index_shift)
                        # partition then shift as appropriate.
                        
                        
                # Add another replacemen.
                requirements.append(eq.relation)
                repl_map[param_var].add(param_tuple)
                shifted_operands = eq.expr.entries
                if index_shift < 0:
                    shifted_operands = shifted_operands[:index_shift]
                elif index_shift > 0:
                    shifted_operands = shifted_operands[index_shift:]
                repl_map[param_tuple] = ExprTuple(*shifted_operands)
                        
    """
        
    def _replaced(self, repl_map, allow_relabeling=False,
                  assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions replaced 
        according to the replacement map (repl_map) dictionary 
        which maps Expressions to Expressions.
        
        If allow_relabeling is True then internal Lambda parameters
        may be replaced when it is a valid replacement of parameter(s) 
        (i.e., Variable's, IndexedVar's, or an ExprRange of 
        IndexedVar's, and unique parameter variables).
        Otherwise, the Lambda parameter variables will be masked
        within its scope.  Partial masked of a range of indexed
        varaibles is not allowed and will cause an error.
        For example, we cannot replace (x_1, ..., x_{n+1}) within 
        (x_1, ..., x_n) -> f(x_1, ..., x_n).        
        
        'assumptions' and 'requirements' are used when an operator is
        replaced with a lambda map that has iterated parameters such that 
        the length of the parameters and operands are required to be equal.
        For more details, see Operation.replaced, Lambda.apply, and
        ExprRange.replaced (which is the sequence of calls involved).
        '''
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be replaced.
            return repl_map[self]
        
        assumptions = defaults.checkedAssumptions(assumptions)
        
        # Use a helper method to handle some inner scope transformations.
        new_params, inner_repl_map, inner_assumptions \
            = self._inner_scope_sub(repl_map, allow_relabeling,
                                    assumptions, requirements)
        
        # The lambda body with the substitutions.
        inner_requirements = []
        subbed_body = self.body.replaced(
                inner_repl_map, allow_relabeling,
                inner_assumptions, inner_requirements)
        
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
            replaced = Lambda(new_params, subbed_body)
        except TypeError as e:
            raise ImproperReplacement(self, repl_map, e.args[0])
        except ValueError as e:
            raise ImproperReplacement(self, repl_map, e.args[0])
        
        return replaced

    def _inner_scope_sub(self, repl_map, allow_relabeling,
                         assumptions, requirements):
        '''
        Helper method for replaced (and used by ExprRange.replaced) 
        which handles the change in scope properly as well as parameter 
        relabeling.
        '''
        
        from proveit import Variable, ExprRange, IndexedVar
        from proveit._core_.expression.composite.expr_range import \
            extract_start_indices, extract_end_indices
        
        # Within the lambda scope, we can instantiate lambda parameters
        # in a manner that retains the validity of the parameters as
        # parameters.  For any disallowed instantiation of Lambda 
        # parameters, we will ignore the corresponding instantiation
        # within this scope and assume it is meant to be done external
        # to this scope; it is masked within the new scope with
        # exception to a partial masking of a range of indexed 
        # variables.  In the latter case, we raise an exception,
        # disallowing such substitutions.
        inner_repl_map = dict()
        for key, value in repl_map.items():
            if not _guaranteed_to_be_independent(key, self.parameterVarSet):
                # If any of the free variables of the key occur as
                # parameter variables, either that replacement is
                # masked within this scope, or there is an allowed
                # relabeling or parameter range expansion.
                
                # First, let's see if there is an associated
                # expansion for this key.
                key_repl = repl_map.get(key, None)
                if isinstance(key_repl, set):
                    # There are one or more expansions for a variable
                    # that occurs as a local Lambda parameter.
                    # It may be fully or partially masked.  We have to
                    # be careful about partial masks, making sure
                    # there is no masking outside of the covered range 
                    # of indices but there is masking otherwise.
                    var = key
                    assert isinstance(var, Variable)
                    param_of_var = None
                    for param, param_var in zip(self.parameters, 
                                                self.parameterVars):
                        if param_var==var:
                            param_of_var = param
                    if param_of_var is None:
                        # The key is not being masked in any way.
                        continue
                    if isinstance(param_of_var, Variable):
                        # The parameter is the Variable itself, so
                        # it masks all occurrences of that Variable.
                        continue # No inner replacement for this.
                    if isinstance(param_of_var, ExprRange):
                        mask_start = extract_start_indices(param_of_var)
                        mask_end = extract_end_indices(param_of_var)
                    else:
                        assert isinstance(param_of_var, IndexedVar)
                        mask_start = mask_end = [param_of_var.index]
                    # We may only use the variable range forms of 
                    # key_repl that carve out the masked indices (e.g.
                    # (x_1, ..., x_n, x_{n+1}) is usable if the masked
                    # indices are (1, ..., n) or (n+1) but not 
                    # otherwise).
                    try:
                        if not _mask_var_range(
                                var, key_repl, mask_start, mask_end, 
                                allow_relabeling, repl_map, inner_repl_map, 
                                assumptions, requirements):
                            # No valid variable range form that carvs
                            # out the masked indices.  All we can do
                            # is indicate that the 'param_of_var' is
                            # unchanged and no other expansion is 
                            # allowed.
                            inner_repl_map[var] = {param_of_var}
                            inner_repl_map[param_of_var] = param_of_var                
                    except ValueError as e:
                        raise ImproperReplacement(
                                self, repl_map, str(e))    
                elif isinstance(key, Variable) and isinstance(value, Variable):
                    # A simple relabeling is allowed to propagate
                    # through as long as the variable is not indexed
                    # over a range that is not covered here.
                    if (allow_relabeling and 
                            key not in self.nonrelabelable_param_vars):
                        inner_repl_map[key] = value
                    # Otherwise, it is a simple, fair masking.
                elif isinstance(key, IndexedVar) and key in self.parameters:
                    if allow_relabeling:
                        if (isinstance(value, IndexedVar) 
                                or isinstance(value, Variable)):
                            # You can relabel an IndexedVar to another
                            # IndexedVar or a Variable.
                            inner_repl_map[key] = value
                    # Otherwise, it is a simple, fair masking.
                # In all remaining cases where the key is not
                # inserted into inner_repl_map, the replacement
                # is deemed to be safely masked within this scope.
            else:
                # No conflict -- propagate the replacement.
                inner_repl_map[key] = value
        
        # Free variables of the replacements must not collide with
        # the parameter variables.  If there are collisions, relabel
        # the parameter variables to something safe.  First, get the
        # free variables of the body and the replacements.
        # (Note: a repl_map 'value' may be a set indicating
        # possible expansions for an indexed variable over a range,
        # e.g., x : {(x_1, .., x_{n+1}), ({x_1, .., x_n}), 
        #            (x_{1+1}, ..., x_{n+1})} 
        # we can ignore those for this purpose as the real replacements 
        # will be what the members of this set map to.
        non_param_body_free_vars = (free_vars(self.body) - 
                                    self.parameterVarSet)
        restricted_vars = non_param_body_free_vars.union(
                *[free_vars(value) for key, value in inner_repl_map.items()
                 if (key not in self.parameterVarSet 
                     and not isinstance(value, set))])
        for param_var in self.parameterVarSet:
            if inner_repl_map.get(param_var, param_var) in restricted_vars:
                # Avoid this collision by relabeling to a safe dummy 
                # variable.
                if param_var in self.nonrelabelable_param_vars:
                    raise DisallowedParameterRelabeling(
                            param_var, self, 
                            " Thus, a collision of variable names induced "
                            "by the following replacement map could not be "
                            "avoided: %s."%inner_repl_map)
                dummy_var = safeDummyVar(*restricted_vars)
                inner_repl_map[param_var] = dummy_var
                restricted_vars.add(dummy_var)
            else:
                restricted_vars.add(param_var)
        
        # Generate the new set of parameters which may be relabeled or, 
        # in the case of a parameter range, may be altered due a change
        # in the start/end indices, or may be expanded.
        # For example, we may have
        # x_1, ..., x_n go to 
        #       x_1, ..., x_3 with n:3
        #       a, b, c with n:3 and (x_1, ..., x_3):(a, b, c)
        #       x_1 with n:1
        #       or empty with n:0
        new_params = []
        for parameter, param_var in zip(self.parameters, self.parameterVars):
            if isinstance(parameter, ExprRange):
                subbed_param = parameter._replaced_entries(
                        inner_repl_map, allow_relabeling, 
                        assumptions, requirements)
                new_params.extend(subbed_param)
            else:
                subbed_param = parameter.replaced(
                        inner_repl_map, allow_relabeling, 
                        assumptions, requirements)
                new_params.append(subbed_param)
        
        if len({getParamVar(param) for param in new_params}) != len(new_params):
            raise ParameterCollisionError(
                    new_params, "Parameter variables must be unique")

        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = [assumption for assumption in assumptions 
                             if free_vars(assumption).isdisjoint(new_params)]
                                      
        return new_params, inner_repl_map, inner_assumptions
    

    def relabeled(self, relabel_map):
        '''
        Return a variant of this Lambda expression with one or more
        of its parameter labels changed.  The resulting expression 
        should be "equal" to the original (having the same meaning) but 
        essentially has a different "style" (formats differently) and 
        uses different labels for substitution purposes.
        '''
        from proveit import Variable, IndexedVar
        for key, val in relabel_map.items():
            if (not isinstance(val, Variable) 
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel %s"%val)
            if (not isinstance(val, Variable) 
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel to %s"%key)
        relabeled = self.replaced(relabel_map, allow_relabeling=True)
        for orig_param_var, new_param_var in zip(self.parameterVars,
                                                 relabeled.parameterVars):
            # Presume that if one of the parameters did not actually
            # get relabeled, that it was because the relabeling was
            # not allowed.
            if (new_param_var != 
                    relabel_map.get(orig_param_var, orig_param_var)):
                raise DisallowedParameterRelabeling(orig_param_var, self)
        assert relabeled==self, (
                "Relabeled version should be 'equal' to original")
        return relabeled
    
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
            relabeledExpr2 = lambda2.body.replaced({lambda2.parameters[0]:lambda1.parameters[0]})
            # x -> f(g(x))
            return Lambda(lambda1.parameters[0], lambda1.body.replaced({lambda1.parameters[0]:relabeledExpr2}))
        else:
            if len(lambda2) != len(lambda1.parameters):
                raise TypeError("Must supply a list of lambda2s with the same length as the number of lambda1 parameters")
            relabeledExpr2s = []
            for lambda2elem in lambda2:
                if len(lambda2elem.parameters) != len(lambda1.parameters):
                    raise TypeError("Each lambda2 must have the same number of parameters as lambda1")
                # gi(x1, x2, ..., xn)
                paramReplMap = {param2:param1 for param1, param2 in zip(lambda1.parameters, lambda2elem.parameters)}
                relabeledExpr2s.append(lambda2elem.body.replaced(paramReplMap))
            # x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
            lambda1ExprSubMap = {param1:relabeledExpr2 for param1, relabeledExpr2 in zip(lambda1.parameters, relabeledExpr2s)}
            return Lambda(lambda1.parameters, lambda1.body.replaced(lambda1ExprSubMap))
    
    @staticmethod
    def globalRepl(masterExpr, subExpr):
        '''
        Returns the Lambda map for replacing the given sub-Expression
        everywhere that it occurs in the master Expression.
        '''
        lambdaParam = masterExpr.safeDummyVar()
        return Lambda(lambdaParam, masterExpr.replaced({subExpr:lambdaParam}))
    
    @staticmethod
    def _explicitly_free_var_ranges(parameters, parameterVars, body,
                                    exclusions=None):
        '''
        Like _free_var_ranges but doesn't account for eliminating
        ranges with internally bound variables.
        '''
        forms_dict = dict()
        for expr in (parameters, body):
            forms_dict.update(expr._free_var_ranges(exclusions=exclusions))
        for param, param_var in zip(parameters, parameterVars):
            if param_var in forms_dict.keys():
                forms_dict[param_var].discard(param)
                # Note: If you have a parameter of x_1 or a parameter of
                # x_1, ..., x_n, then 'x' itself is masked although
                # x_{n+1} would not be masked.  Therfore, remove 'x':
                forms_dict[param_var].discard(param_var)
                if len(forms_dict[param_var])==0:
                    forms_dict.pop(param_var)
        return forms_dict        
        
    
    def _free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free or 
        not explicitly and completely masked.  Examples of "forms":
            x
            x_i
            x_1, ..., x_n
            x_{i, 1}, ..., x_{i, n_i}
            x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}

        If any of the ranges have indices with internally
        bound variables, they will not be reported as free since
        part of it is bound.  For example,
        (k, n) -> [(x_1, ..., x_n) -> 
                   x_1 + ... + x_k + x_{k+1} + ... + x_{n}]
        would not report anything.
        '''
        forms_dict = dict()
        if exclusions is not None and self in exclusions: 
            return forms_dict # this is excluded        
        
        relabelable_param_vars \
        = {param_var for param_var in self.parameterVars
           if param_var not in self.nonrelabelable_param_vars}
        
        # Use the _explicitly_free_var_ranges but skip anything that
        # is has any of the relabelable parameter variables as free
        # (if it changes under relabeling, it cannot be reported as 
        # free).
        for var, forms in Lambda._explicitly_free_var_ranges(
                self.parameters, self.parameterVars, self.body, 
                exclusions=exclusions).items():
            for form in forms:
                if relabelable_param_vars.isdisjoint(free_vars(form)):
                    forms_dict.setdefault(var, set()).add(form)        
        return forms_dict

def _guaranteed_to_be_independent(expr, parameter_vars):
    '''
    Return True if we can guarantee that the given expression
    is independent of the given parameters.  It may not be clear
    in some cases.  For example, if 
    expr : x_1 + ... + x_n
    parameters : x_i, ..., x_j
    In such a case, we must return False since there is no guarantee
    of independence.
    '''
    from proveit._core_.expression.expr import free_vars
    if free_vars(expr).isdisjoint(parameter_vars):
        return True
    return False

def extract_param_replacements(parameters, parameter_vars, body,
                               operands, assumptions, requirements,
                               repl_map):
    '''
    Match the operands with parameters in order by checking
    tuple lengths.  Add a repl_map entry to map each
    parameter entry (or ExprTuple-wrapped entry) to corresponding
    operand(s) (ExprTuple-wrapped as appropriate).
    '''
    from proveit import (ExprTuple, ExprRange, ProofFailure, 
                         safeDummyVar, Len)
    from proveit.logic import Equals, EvaluationError
    # Loop through each parameter entry and match it with corresponding
    # operand(s).  Singular parameter entries match with singular
    # operand entries.  Iterated parameter entries match with
    # one or more operand entries which match in element-wise length
    # For example, (x_1, ..., x_n, y) has an element-wise lenght of
    # n+1.
    operands_iter = iter(operands)
    try:
        for parameter, param_var in zip(parameters, parameter_vars):
            if isinstance(parameter, ExprRange):
                from proveit.number import zero, one
                # This is a iterated parameter which corresponds with
                # one or more operand entries in order to match the
                # element-wise length.
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
                        raise LambdaApplicationError(
                                parameters, body, operands, assumptions, [],
                                "Failed to prove operand length "
                                "requirement: %s"%str(e))
                else:
                    # Collect enough operands to match the length of
                    # the range of parameters.
                    param_operands = []
                    while True:
                        param_operands_tuple = ExprTuple(*param_operands)
                        param_operands_len = Len(param_operands_tuple)
                        len_req = Equals(param_operands_len, param_len)
                        try:
                            # Try to prove len_req using minimal
                            # automation since we do not know if
                            # this is the right match or if we need
                            # to go further with more operands.
                            len_req.lhs.deduceEquality(
                                    len_req, assumptions, 
                                    minimal_automation=True)
                            assert len_req.proven(assumptions)
                        except ProofFailure:
                            pass
                        if len_req.proven(assumptions):
                            requirements.append(len_req.prove(assumptions))
                            break # we have a match
                        param_operands.append(next(operands_iter))
                # For the parameter range replacement, we map the 
                # parameter variable to a set of parameter range
                # tuples (e.g., x : {(x_i, ..., x_n)}) to indicate 
                # the index range and then map that iteration tuple 
                # to the actual operands to be replaced.
                param_tuple = ExprTuple(parameter)
                repl_map[param_var] = {param_tuple}
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
                                        assumptions, [],
                                        "Parameter/argument length "
                                        "mismatch 1 vs %s"
                                        %operand_len_evaluation.rhs)
                    except EvaluationError:                                                        
                        raise LambdaApplicationError(
                                parameters, body, operands, assumptions, [],
                                "Singular parameters must correspond "
                                "with singular operands or ranges with "
                                "lengths known to sum to 1: %s vs %s."
                                %(parameter, operand))
                repl_map[parameter] = operand
    except StopIteration:
        raise LambdaApplicationError(parameters, body, 
                                     operands, assumptions, [],
                                     "Parameter/argument length mismatch "
                                     "or unproven length equality for "
                                     "correspondence with %s."
                                     %str(parameter))
    # Make sure all of the operands were consumed.
    try:
        next(operands_iter)
        # All operands were not consumed.
        raise LambdaApplicationError(parameters, body, 
                                     operands, assumptions, [],
                                     "Too many arguments")
    except StopIteration:
        pass # Good.  All operands were consumed.

def _mask_var_range(
        var, var_range_forms, mask_start, mask_end, allow_relabeling, 
        repl_map, inner_repl_map, assumptions, requirements):
    '''
    Given a variable 'var' (e.g., 'x'), a set of equivalent forms
    of ranges over indices over that variable (e.g., 
    {(x_1, ..., x_{n+1}), (x_1, x_2, ..., x_n, x_{n+1}),
     (x_1, ..., x_n, x_{n+1})}),
    a starting and ending indices for a 'masked' range of indices,
    and a replacement map, update the `inner_repl_map` valid with
    masking the 'masked' range.  Specifically, only the forms of 
    ranges with explicit coverage of the 'masked' range are valid to
    use.  In our previous example, if start_index==1 and end_index==n 
    then only (x_1, x_2, ..., x_n, x_{n+1}) and (x_1, ..., x_n, x_{n+1})
    could be used and (x_1, ..., x_{n+1}) would be ignored.
    To mask the 'masked' range, entries within that range will
    map to themselves rather than the corresponding replacements.
    However, if allow_relabeling is true, and the corresponding
    replacements of the masked entries map to valid parameters, then
    we can perform relabeling.  When relabeling and there are multiple
    forms covering the masked range, we will need to add the 
    requirements that those forms are equal for all instances
    of those parameter variables.  For example, to relabel
    x_1, ..., x_n to y_1, ..., y_i, z_{i+1}, ..., z_n in the scenario
    above where we also have
    (x_1, x_2, ..., x_n, x_{n+1}) : 
        (y_1, y_2, ..., y_i, z_{i+1}, ..., z_n, q)
    we would require that
    \forall_{y_1, ..., y_i, z_{i+1}, ..., z_n} 
        (y_1, ..., y_i, z_{i+1}, ..., z_n) = 
        (y_1, y_2, ..., y_i, z_{i+1}, ..., z_n)
    
    In the multiple index setting, we need to check all of the indices.  
    Consider 
        (x_{m, i_{m}}, ..., x_{m, j_{m}}, ......,
         x_{n, i_{n}}, ..., x_{n, j_{n}}).
    Here, we need to match with all indices:
        (m, i_m) for the start and (n, j_n) for the end.
    
    Return True iff there are one or more valid range forms that
    carve out the masked region.
    '''
    from proveit import (IndexedVar, ExprTuple, ExprRange,
                         singleOrCompositeExpression)
    from proveit._core_.expression.composite.expr_range import \
        extract_start_indices, extract_end_indices
    valid_var_range_forms = set()
    masked_region_repl_map = dict()
    fully_masking_var_range = None
    for var_range_form in var_range_forms:
        masked_entries = []
        has_start = has_end = False
        for entry in var_range_form:
            if isinstance(entry, IndexedVar):
                entry_start_indices = entry_end_indices \
                    = [entry.index]
            else:
                assert isinstance(entry, ExprRange)
                entry_start_indices = extract_start_indices(entry)
                entry_end_indices = extract_end_indices(entry)
            if entry_start_indices == mask_start:
                has_start = True
            if has_start and not has_end:
                masked_entries.append(entry)
            if entry_end_indices == mask_end:
                has_end = True
        if has_start and has_end:
            # Add entries for this var_tuple expansion into 
            # `cur_repl_map` first; these will be divied into
            # `inner_repl_map` (unmasked) and mased_region_repl 
            # (masked).
            expansion = repl_map[var_range_form]
            valid_var_range_forms.add(var_range_form)
            cur_repl_map = dict()
            try:
                extract_param_replacements(
                        var_range_form, [var]*len(var_range_form), 
                        var_range_form, expansion, assumptions, 
                        requirements, cur_repl_map)
            except LambdaApplicationError as e:
                raise ValueError(
                        "Unable to match the tuple of indexed "
                        "variables %s to its expansion %s.  "
                        "Got error %s."
                        %(var_range_form, expansion, str(e)))    
            # Divy `cur_repl_map` entries into `inner_repl_map` 
            # (unmasked) and mased_region_repl (masked).
            inner_repl_map[var_range_form] = expansion
            if len(masked_entries)==1:
                fully_masking_var_range = \
                    singleOrCompositeExpression(masked_entries[0])
            masked_region_repl = []
            for masked_entry in masked_entries:
                if isinstance(masked_entry, ExprRange): 
                    masked_region_repl.extend(
                            cur_repl_map.pop(ExprTuple(masked_entry)))
                else:
                    masked_region_repl.append(cur_repl_map.pop(masked_entry))
            masked_region_repl = ExprTuple(*masked_region_repl)
            masked_region_repl_map[ExprTuple(*masked_entries)] \
                = masked_region_repl
            inner_repl_map.update(cur_repl_map)
    
    if len(valid_var_range_forms)==0:
        # No valid variable range forms which carve out the masked
        # region.
        return False
    # Record the range forms that are valid, carving out the
    # masked region.
    inner_repl_map[var] = valid_var_range_forms      
        
    # If relabeling is allowed and we know the replacement for
    # the full masked region and it is a tuple of valid parameters,
    # then do relabeling for the masked region under the requirement
    # that all of the replacements of the masked region are equal
    # for all instances of the parameter variables.
    # Otherwise, we need to map the masked region entries to themselvs.
    if (allow_relabeling and fully_masking_var_range is not None):
        fully_masking_repl = masked_region_repl_map[fully_masking_var_range]
        if valid_params(fully_masking_repl):
            # Do "fancy" variable range relabeling.
            from proveit.logic import Forall, Equals
            # Add requirements when there are multiple replacements
            # of the masked region to make sure they are all equal.
            for masked_var_range, repl in masked_region_repl_map.items():
                if masked_var_range != fully_masking_var_range:
                    req = Forall(fully_masking_repl.entries,
                                 Equals(repl, fully_masking_repl))
                    requirements.append(req.prove(assumptions))
            # Update the `inner_repl_map` to effect the relabeling.
            inner_repl_map.update(masked_region_repl_map)        
            return True
        
    # No relabeling.  Map the masked region entries to themselves
    # to effect proper masking.
    for masked_var_range in masked_region_repl_map.keys():
        for masked_entry in masked_var_range:
            masked_entry_key = singleOrCompositeExpression(masked_entry)
            inner_repl_map[masked_entry_key] = masked_entry_key
    return True

class ParameterCollisionError(Exception):
    def __init__(self, parameters, main_msg):
        self.parameters = parameters
        self.main_msg = main_msg
    def __str__(self):
        return ("%s.  %s does not satisfy this criterion."
                %(self.main_msg, self.parameters))

class DisallowedParameterRelabeling(Exception):
    def __init__(self, param_var, lambda_expr, extra_msg=''):
        self.param_var = param_var
        self.lambda_expr = lambda_expr
        self.extra_msg = extra_msg
    def __str__(self):
        return ("Cannot relabel %s in %s; relabeling is only allowed when "
                "all occurrences of a range of parameters matches the exact "
                "range appearing as parameters (otherwise, the bound verses "
                "free portions of the range may be ambiguous).%s"
                %(self.param_var, self.lambda_expr, self.extra_msg))

class LambdaApplicationError(Exception):
    def __init__(self, parameters, body, operands, assumptions, 
                 equiv_alt_expansions, extra_msg):
        from proveit._core_.expression.composite.composite import \
            compositeExpression
        self.parameters = compositeExpression(parameters)
        self.body = body
        self.operands = operands
        self.assumptions = assumptions
        self.equiv_alt_expansions=equiv_alt_expansions
        self.extra_msg = extra_msg
    def __str__(self):
        assumption_str = ''
        equiv_alt_expansions_str = ''
        if len(self.assumptions) > 0:
            assumption_str = ' assuming %s'%str(self.assumptions)
        if (self.equiv_alt_expansions is not None and
                len(self.equiv_alt_expansions) > 0):
            equiv_alt_expansions_str = (
                    " using equivalent alternate expansions of %s"
                    %self.equiv_alt_expansions)
        return ("Failure to apply %s to %s%s%s:\n%s"
                %(Lambda._string(self.parameters, self.body), 
                  self.operands, equiv_alt_expansions_str, 
                  assumption_str, self.extra_msg))

class ArgumentExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics
    def __str__(self):
        return ("Cannot extract argument(s); mappedExpr does not match this Lambda "
                "expression: " + self.specifics)

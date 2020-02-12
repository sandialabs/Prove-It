from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
from proveit._core_.expression.composite import Composite, ExprTuple, singleOrCompositeExpression, compositeExpression
from proveit._core_.defaults import defaults, USE_DEFAULTS
import itertools

class Iter(Expression):
    '''
    An Iter Expression represents an iteration of  Expressions to be 
    inserted into a containing composite Expression.
    
    Upon substitution, it automatically expands to if it contains an 
    Indexed expression whose variable is substituted with a tuple or 
    array.  To ensure such an expansion is unambiguous and sensibly 
    defined, Iter expressions must only contain Indexed variables with
    indices that are 'simple' functions of an iteration (the parameter 
    itself or a sum of terms with one term as the parameter).
    For example
    a_1*b_1 + ... + a_n*b_n
    when substituted with 
    a:(x_1, ..., x_j, y_1, ..., y_k)
    b:(z_1, ..., z_k, x_1, ..., x_j)
    under the assumption that j<k will be transformed into
    x_1*z_1 + ... + x_j*z_j +
    y_1*z_{j+1} + ... + y_{k-j}*z_{j+(k-j)} +
    y_{k-j+1}*x_1 + ... + y_{k-j+j}*x_j
    '''

    def __init__(self, parameter_or_parameters, body, start_index_or_indices, end_index_or_indices, styles=None, requirements=tuple(), _lambda_map=None):
        '''
        Create an Iter that represents an iteration of the body for the
        parameter(s) ranging from the start index/indices to the end 
        index/indices.  A Lambda expression will be created as its 
        sub-expression that maps the parameter(s) to the body with
        conditions that restrict the parameter(s) to the appropriate interval.
        
        _lambda_map is used internally for efficiently rebuilding an Iter.
        '''
        from proveit.logic import InSet
        from proveit.number import Interval
        
        if _lambda_map is not None:
            # Use the provided 'lambda_map' instead of creating one.
            lambda_map = _lambda_map
            pos_args = (parameter_or_parameters, body, start_index_or_indices, 
                        end_index_or_indices)
            if pos_args != (None, None, None, None):
                raise ValueError("Positional arguments of the Init constructor "
                                 "should be None if lambda_map is provided.")
            parameters = lambda_map.parameters
            body = lambda_map.body
            conditions = lambda_map.conditions
            if len(conditions) != len(parameters):
                raise ValueError("Inconsistent number of conditions and lambda "
                                 "map parameters")
            start_indices, end_indices = [], []
            for param, condition in zip(parameters, conditions):
                invalid_condition_msg = ("Not the right kind of lambda_map condition "
                                         "for an iteration")
                if not isinstance(condition, InSet) or condition.element != param:
                    raise ValueError(invalid_condition_msg)
                domain = condition.domain
                if not isinstance(domain, Interval):
                    raise ValueError(invalid_condition_msg)
                start_index, end_index = domain.lowerBound, domain.upperBound
                start_indices.append(start_index)
                end_indices.append(end_index)
            self.start_indices = ExprTuple(*start_indices)
            self.end_indices = ExprTuple(*end_indices)
            if len(parameters) == 1:
                self.start_index = self.start_indices[0]
                self.end_index = self.end_indices[0]
                self.start_index_or_indices = self.start_index
                self.end_index_or_indices = self.end_index
            else:
                self.start_index_or_indices = self.start_indices
                self.end_index_or_indices = self.end_indices                
        else:
            parameters = compositeExpression(parameter_or_parameters)

            start_index_or_indices = singleOrCompositeExpression(start_index_or_indices)
            if isinstance(start_index_or_indices, ExprTuple) and len(start_index_or_indices)==1:
                start_index_or_indices = start_index_or_indices[0]
            self.start_index_or_indices = start_index_or_indices
            if isinstance(start_index_or_indices, Composite):
                # a composite of multiple indices
                self.start_indices = self.start_index_or_indices 
            else:
                # a single index
                self.start_index = self.start_index_or_indices
                # wrap a single index in a composite for convenience
                self.start_indices = compositeExpression(self.start_index_or_indices)
    
            end_index_or_indices = singleOrCompositeExpression(end_index_or_indices)
            if isinstance(end_index_or_indices, ExprTuple) and len(end_index_or_indices)==1:
                end_index_or_indices = end_index_or_indices[0]
            self.end_index_or_indices = end_index_or_indices
            if isinstance(self.end_index_or_indices, Composite):
                # a composite of multiple indices
                self.end_indices = self.end_index_or_indices 
            else:
                # a single index
                self.end_index = self.end_index_or_indices
                # wrap a single index in a composite for convenience
                self.end_indices = compositeExpression(self.end_index_or_indices)                        

            conditions = []
            for param, start_index, end_index in zip(parameters, self.start_indices, 
                                                     self.end_indices):
                conditions.append(InSet(param, Interval(start_index, end_index)))
            
            lambda_map = Lambda(parameters, body, conditions=conditions)
        
        self.ndims = len(self.start_indices)
        if self.ndims != len(self.end_indices):
            raise ValueError("Inconsistent number of 'start' and 'end' indices")
        
        if len(parameters) != len(self.start_indices):
            raise ValueError("Inconsistent number of indices and lambda map parameters")
        
        Expression.__init__(self, ['Iter'], [lambda_map], styles=styles, requirements=requirements)
        self.lambda_map = lambda_map
        self._checkIndexedRestriction(body)
    
    """
    def __init__(self, lambda_map, start_index_or_indices, end_index_or_indices, styles=None, requirements=tuple()):
        if not isinstance(lambda_map, Lambda):
            raise TypeError('When creating an Iter Expression, the lambda_map argument must be a Lambda expression')
        
        if isinstance(start_index_or_indices, ExprTuple) and len(start_index_or_indices)==1:
            start_index_or_indices = start_index_or_indices[0]
        self.start_index_or_indices = singleOrCompositeExpression(start_index_or_indices)
        
        self.ndims = len(self.start_indices)
        if self.ndims != len(self.end_indices):
            raise ValueError("Inconsistent number of 'start' and 'end' indices")
        
        if len(lambda_map.parameters) != len(self.start_indices):
            raise ValueError("Inconsistent number of indices and lambda map parameters")
        
        Expression.__init__(self, ['Iter'], [lambda_map, self.start_index_or_indices, self.end_index_or_indices], styles=styles, requirements=requirements)
        self.lambda_map = lambda_map
    """
    
    def _checkIndexedRestriction(self, subExpr):
        '''
        An iteration is restricted to not contain any Indexed variable
        that is a complicated function of the iteration parameter.
        Specifically, for each parameter, the index of an Indexed 
        variable may  be a function solely of that parameter or that 
        parameter added with terms that don't contain the parameter.
        For example, you can have x_1, ..., x_n and you can have
        x_{1+k}, ..., x_{n+k} or x_{k+1}, ..., x_{k+n} but not
        x_{1^2}, ..., x_{n^2} or x_{2*1}, ..., x_{2*n}.
        '''
        from .indexed import Indexed
        from proveit.number import Add
        if isinstance(subExpr, Indexed):
            for index in subExpr.indices:
                for parameter in self.lambda_map.parameters:
                    if index==parameter:
                        # It is fine for the index to simply be the
                        # parameter.  That is a simple case.
                        continue
                    if isinstance(index, Add):
                        terms_to_check = list(index.operands)
                        if parameter in terms_to_check:
                            # Remove first occurrence of the parameter.
                            terms_to_check.remove(parameter)
                        for term in terms_to_check:
                            if parameter in term.freeVars():
                                # Invalid because the parameter occurs
                                # either in multiple terms of the index
                                # or in a non-trivial form (not simply
                                # as itself).
                                raise InvalidIterationError(index,
                                                             parameter)
                        # Valid: the parameter occurs solely as a term 
                        # of the index. 
                        continue # Move on to the next check.
                    if parameter in index.freeVars():
                        # The parameter occurs in the index in a form
                        # that is not valid:
                        raise InvalidIterationError(index, parameter)
        # Recursively check sub expressions of the sub expression.
        for sub_sub_expr in subExpr.subExprIter():
            self._checkIndexedRestriction(sub_sub_expr)
            
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != Iter: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'Iter':
            raise ValueError("Expecting Iter coreInfo to contain exactly one item: 'Iter'")
        lambda_map = subExpressions[0]
        return Iter(None, None, None, None, _lambda_map=lambda_map).withStyles(**styles)
            
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.lambda_map.parameter_or_parameters
        yield self.lambda_map.body
        yield self.start_index_or_indices
        yield self.end_index_or_indices
        
    def first(self):
        '''
        Return the first instance of the iteration (and store for future use).
        '''
        if not hasattr(self, '_first'):
            expr_map = {parameter:index for parameter, index 
                        in zip(self.lambda_map.parameters, self.start_indices)}
            self._first =  self.lambda_map.body.substituted(expr_map)
        return self._first

    def last(self):
        '''
        Return the last instance of the iteration (and store for futurle use).
        '''
        if not hasattr(self, '_last'):
            expr_map = {parameter:index for parameter, index 
                        in zip(self.lambda_map.parameters, self.end_indices)}
            self._last = self.lambda_map.body.substituted(expr_map)
        return self._last
    
        
    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=False, subFence=True, operator=None, **kwargs):
        outStr = ''
        if operator is None:
            formatted_operator = ',' # comma is the default formatted operator
        elif isinstance(operator, str):
            formatted_operator = operator
        else:
            formatted_operator = operator.formatted(formatType)
        formatted_sub_expressions = [subExpr.formatted(formatType, fence=subFence) for subExpr in (self.first(), self.last())]
        formatted_sub_expressions.insert(1, '\ldots' if formatType=='latex' else '...')
        # put the formatted operator between each of formattedSubExpressions
        if fence: 
            outStr += '(' if formatType=='string' else  r'\left('
        outStr += formatted_operator.join(formatted_sub_expressions)
        if fence:            
            outStr += ')' if formatType=='string' else  r'\right)'
        return outStr
    
    def getInstance(self, index_or_indices, assumptions = USE_DEFAULTS, requirements = None):
        '''
        Return the iteration instance with the given indices
        as an Expression, using the given assumptions as needed
        to interpret the indices expression.  Required
        truths, proven under the given assumptions, that 
        were used to make this interpretation will be
        appended to the given 'requirements' (if provided).
        '''
        from proveit.number import LessEq
        
        if self.ndims==1:
            indices = [index_or_indices]
        else:
            indices = index_or_indices

        if requirements is None:
            # requirements won't be passed back in this case 
            requirements = [] 
        
        # first make sure that the indices are in the iteration range
        for index, start, end in zip(indices, self.start_indices, self.end_indices):
            for first, second in ((start, index), (index, end)):
                relation = None
                try:
                    relation = LessEq.sort([first, second], reorder=False, assumptions=assumptions)
                except:
                    raise IterationError("Indices not provably within the iteration range: %s <= %s"%(first, second)) 
                requirements.append(relation)
        
        # map to the desired instance
        return self.lambda_map.mapped(*indices)
    
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, 
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        Attempt to automatically expand the iteration if any Indexed 
        sub-expressions substitute their variable for a composite
        (list or tensor).  Indexed should index variables that represent
        composites, but substituting the composite is a signal that
        an outer iteration should be expanded.  An exception is
        raised if this fails.
        '''
        from .composite import _generateCoordOrderAssumptions
        from proveit import ProofFailure, ExprArray
        from proveit.logic import Equals, InSet
        from proveit.number import Less, LessEq, dist_add, \
            zero, one, dist_subtract, Naturals, Integers
        from .composite import _simplifiedCoord
        from proveit._core_.expression.expr import _NoExpandedIteration
        from proveit._core_.expression.label.var import safeDummyVars
        
        self._checkRelabelMap(relabelMap)
        if relabelMap is None: relabelMap = dict()
        
        assumptions = defaults.checkedAssumptions(assumptions)
        new_requirements = []
        iter_params = self.lambda_map.parameters
        iter_body = self.lambda_map.body
        ndims = self.ndims
        subbed_start = self.start_indices.substituted(exprMap, relabelMap, 
                           reservedVars, assumptions, new_requirements)
        subbed_end = self.end_indices.substituted(exprMap, relabelMap, 
                         reservedVars, assumptions, new_requirements)
        
        #print("iteration substituted", self, subbed_start, subbed_end)
        
        # Need to handle the change in scope within the lambda 
        # expression.  We won't use 'new_params'.  They aren't relavent 
        # after an expansion, this won't be used.
        new_params, inner_expr_map, inner_assumptions, inner_reservations \
            = self.lambda_map._innerScopeSub(exprMap, relabelMap, 
                  reservedVars, assumptions, new_requirements)
        
        # Get sorted substitution parameter start and end
        # values demarcating how the entry array must be split up for 
        # each axis.
        all_entry_starts = [None]*ndims
        all_entry_ends = [None]*ndims
        do_expansion = False
        for axis in range(ndims):
            try:
                empty_eq = Equals(dist_add(subbed_end[axis], one), 
                                  subbed_start[axis])
                try:
                    # Check if this is an empty iteration which
                    # happens when end+1=start.
                    empty_eq.prove(assumptions, automation=False)
                    all_entry_starts[axis] = all_entry_ends[axis] = []
                    do_expansion = True
                    continue
                except ProofFailure:
                    pass
                param_vals = \
                    iter_body._iterSubParamVals(axis, iter_params[axis], 
                                                subbed_start[axis], 
                                                subbed_end[axis],
                                                inner_expr_map, relabelMap,
                                                inner_reservations, 
                                                inner_assumptions,
                                                new_requirements)
                assert param_vals[0] == subbed_start[axis]
                if param_vals[-1] != subbed_end[axis]:
                    # The last of the param_vals should either be
                    # subbed_end[axis] or known to be 
                    # subbed_end[axis]+1.  Let's double-check.
                    eq = Equals(dist_add(subbed_end[axis], one), param_vals[-1])
                    eq.prove(assumptions, automation=False)
                # Populate the entry starts and ends using the
                # param_vals which indicate that start of each contained
                # entry plus the end of this iteration.
                all_entry_starts[axis] = []
                all_entry_ends[axis] = []
                for left, right in zip(param_vals[:-1], param_vals[1:]):
                    all_entry_starts[axis].append(left)
                    try:
                        eq = Equals(dist_add(left, one), right)
                        eq.prove(assumptions, automation=False)
                        new_requirements.append(eq.prove(assumptions,
                                                         automation=False))
                        # Simple single-entry case: the start and end
                        # are the same.
                        entry_end = left
                    except:
                        # Not the simple case; perform the positive 
                        # integrality check.
                        requirement = InSet(dist_subtract(right, left), 
                                            Naturals)
                        # Knowing the simplification may help prove the 
                        # requirement.
                        _simplifiedCoord(requirement, assumptions, [])
                        try:
                            new_requirements.append(requirement.prove(assumptions))
                        except ProofFailure as e:
                            raise IterationError("Failed to prove requirement "
                                                  "%s:\n%s"%(requirement, e))
                        if right==subbed_end[axis]:
                            # This last entry is the inclusive end
                            # rather than past the end, so it is an
                            # exception.
                            entry_end = right
                        else:
                            # Subtract one from the start of the next
                            # entyr to get the end of this entry.
                            entry_end = dist_subtract(right, one)
                            entry_end = _simplifiedCoord(entry_end, assumptions,
                                                        requirements)
                    all_entry_ends[axis].append(entry_end)
                # See if we should add the end value as an extra 
                # singular entry.  If param_vals[-1] is at the inclusive
                # end, then we have a singular final entry.
                if param_vals[-1] == subbed_end[axis]:
                    end_val = subbed_end[axis]
                    all_entry_starts[axis].append(end_val)
                    all_entry_ends[axis].append(end_val)
                else:
                    # Otherwise, the last param_val will be one after
                    # the inclusive end which we will want to use below
                    # when building the last iteration entry.
                    all_entry_starts[axis].append(param_vals[-1])           
                do_expansion = True
            except EmptyIterException:
                # Indexing over a negative or empty range.  The only way this
                # should be allowed is if subbed_end+1=subbed_start.
                Equals(dist_add(subbed_end[axis], one), subbed_start[axis]).prove(assumptions)
                all_entry_starts[axis] = all_entry_ends[axis] = []
                do_expansion = True
            except _NoExpandedIteration:
                pass
        
        if do_expansion:
            # There are Indexed sub-Expressions whose variable is
            # being replaced with a Composite, so let us
            # expand the iteration for all of the relevant
            # iteration ranges.
            # Sort the argument value ranges.
            
            # We must have "substition parameter values" along each
            # axis:
            if None in all_entry_starts or None in all_entry_ends:
                raise IterationError("Must expand all axes or none of the "
                                      "axes, when substituting %s"%str(self))

            # Generate the expanded tuple/array as the substition
            # of 'self'.
            shape =  [len(all_entry_ends[axis]) 
                      for axis in range(ndims)]
            entries = ExprArray.make_empty_entries(shape)
            indices_by_axis = [range(extent) for extent in shape]
            #print('shape', shape, 'indices_by_axis', indices_by_axis, 'sub_param_vals', sub_param_vals)
            
            extended_inner_assumptions = list(inner_assumptions)
            for axis_starts in all_entry_starts:
                # Generate assumptions that order the
                # successive entry start parameter values
                # must be natural numbers. (This is a requirement for
                # iteration instances and is a simple fact of
                # succession for single entries.)
                extended_inner_assumptions.extend(_generateCoordOrderAssumptions(axis_starts))
            
            # Maintain lists of parameter values that come before each given entry.
            #prev_param_vals = [[] for axis in range(ndims)]
            
            # Iterate over each of the new entries, obtaining indices
            # into sub_param_vals for the start parameters of the entry.
            for entry_indices in itertools.product(*indices_by_axis):
                entry_starts = [axis_starts[i] for axis_starts, i in \
                                zip(all_entry_starts, entry_indices)]
                entry_ends = [axis_ends[i] for axis_ends, i in \
                                zip(all_entry_ends, entry_indices)]
                                
                is_singular_entry = True                
                for entry_start, entry_end in zip(entry_starts, entry_ends):
                    # Note that empty ranges will be skipped because
                    # equivalent parameter values should be skipped in
                    # the param_vals above.
                    if entry_start != entry_end:
                        # Not a singular entry along this axis, so
                        # it is not a singular entry.  We must do an
                        # iteration for this entry.
                        is_singular_entry = False
                
                if is_singular_entry:                    
                    # Single element entry.
                                        
                    # Generate the entry by making appropriate
                    # parameter substitutions for the iteration body.
                    entry_inner_expr_map = dict(inner_expr_map)
                    entry_inner_expr_map.update({param:arg for param, arg in 
                                                 zip(iter_params, 
                                                     entry_starts)})
                    for param in iter_params: relabelMap.pop(param, None)
                    entry = iter_body.substituted(entry_inner_expr_map, 
                                relabelMap, inner_reservations, 
                                extended_inner_assumptions, new_requirements)
                else:
                    # Iteration entry.
                    # Shift the iteration parameter so that the 
                    # iteration will have the same start-indices
                    # for this sub-range (like shifting a viewing 
                    # window, moving the origin to the start of the 
                    # sub-range).
                    
                    # Generate "safe" new parameters (the Variables are
                    # not used for anything that might conflict).
                    # Avoid using free variables from these expressions:
                    unsafe_var_exprs = [self]
                    unsafe_var_exprs.extend(exprMap.values())
                    unsafe_var_exprs.extend(relabelMap.values())
                    unsafe_var_exprs.extend(entry_starts)
                    unsafe_var_exprs.extend(entry_ends)
                    new_params = safeDummyVars(ndims, *unsafe_var_exprs)
                                        
                    # Make assumptions that places the parameter(s) in the
                    # appropriate range and at an integral coordinate position.
                    # Note, it is possible that this actually represents an
                    # empty range and that these assumptions are contradictory;
                    # but this still suits our purposes regardless.
                    # Also, we will choose to shift the parameter so it
                    # starts at the start index of the iteration.
                    range_expr_map = dict(inner_expr_map)
                    range_assumptions = []
                    shifted_entry_ends = []
                    for axis, (param, new_param, entry_start, entry_end) \
                            in enumerate(zip(iter_params, new_params, 
                                             entry_starts, entry_ends)):
                        start_idx = self.start_indices[axis]
                        shift = dist_subtract(entry_start, start_idx)
                        shift = _simplifiedCoord(shift, assumptions,
                                                 new_requirements)
                        if shift != zero:
                            shifted_param = dist_add(new_param, shift)
                        else:
                            shifted_param = new_param
                        range_expr_map[param] = shifted_param
                        shifted_end = dist_subtract(entry_end, shift)
                        shifted_end = _simplifiedCoord(shifted_end, 
                                                       assumptions,
                                                       new_requirements)
                        shifted_entry_ends.append(shifted_end)
                        assumption = InSet(new_param, Integers)
                        range_assumptions.append(assumption)
                        assumption = LessEq(entry_start, shifted_param)
                        range_assumptions.append(assumption)
                        # Assume differences with each of the previous
                        # range starts are natural numbers as should be
                        # the case given requirements that have been 
                        # met.
                        next_index = entry_indices[axis]+1
                        prev_starts = all_entry_starts[axis][:next_index]
                        for prev_start in prev_starts:
                            assumption = InSet(dist_subtract(shifted_param, 
                                                             prev_start), 
                                               Naturals)
                            range_assumptions.append(assumption)
                        next_start = all_entry_starts[axis][next_index]
                        assumption = Less(shifted_param, next_start)
                        range_assumptions.append(assumption)


                    # Perform the substitution.
                    # The fact that our "new parameters" are "safe" 
                    # alleviates the need to reserve anything extra.
                    range_lambda_body = iter_body.substituted(range_expr_map, 
                        relabelMap, reservedVars, 
                        extended_inner_assumptions+range_assumptions, new_requirements)
                    # Any requirements that involve the new parameters 
                    # are a direct consequence of the iteration range 
                    # and are not external requirements:
                    new_requirements = \
                        [requirement for requirement in new_requirements 
                         if requirement.freeVars().isdisjoint(new_params)]
                    entry = Iter(new_params, range_lambda_body, self.start_indices, 
                                 shifted_entry_ends)
                # Set this entry in the entries array.
                ExprArray.set_entry(entries, entry_indices, entry)
                                                                                
                '''      
                    # Iteration entry.
                    # Shift the iteration parameter so that the 
                    # iteration will have the same start-indices
                    # for this sub-range (like shifting a viewing 
                    # window, moving the origin to the start of the 
                    # sub-range).

                    # Generate "safe" new parameters (the Variables are
                    # not used for anything that might conflict).
                    # Avoid using free variables from these expressions:
                    unsafe_var_exprs = [self]
                    unsafe_var_exprs.extend(exprMap.values())
                    unsafe_var_exprs.extend(relabelMap.values())
                    unsafe_var_exprs.extend(entry_start_vals)
                    unsafe_var_exprs.extend(entry_end_vals)
                    new_params = safeDummyVars(len(iter_params), 
                                               *unsafe_var_exprs)
                    
                    # Make the appropriate substitution mapping
                    # and add appropriate assumptions for the iteration
                    # parameter(s).
                    range_expr_map = dict(inner_expr_map)
                    range_assumptions = []
                    for start_idx, param, new_param, range_start, range_end \
                            in zip(subbed_start, iter_params, new_params, 
                                   entry_start_vals, entry_end_vals):
                        shifted_param = Add(new_param, subtract(range_start, start_idx))
                        shifted_param = _simplifiedCoord(shifted_param, assumptions,
                                                         requirements)
                        range_expr_map[param] = shifted_param
                        # Include assumptions that the parameters are 
                        # in the proper range.
                        assumption = LessEq(start_idx, new_param)
                        range_assumptions.append(assumption)
                        assumption = InSet(subtract(new_param, start_idx), Naturals)
                        #assumption = LessEq(new_param,
                        #                    subtract(range_end, start_idx))
                        assumption = LessEq(new_param, range_end)
                        range_assumptions.append(assumption)
                    
                    # Perform the substitution.
                    # The fact that our "new parameters" are "safe" 
                    # alleviates the need to reserve anything extra.
                    range_lambda_body = iter_body.substituted(range_expr_map, 
                        relabelMap, reservedVars, 
                        inner_assumptions+range_assumptions, new_requirements)
                    # Any requirements that involve the new parameters 
                    # are a direct consequence of the iteration range 
                    # and are not external requirements:
                    new_requirements = \
                        [requirement for requirement in new_requirements 
                         if requirement.freeVars().isdisjoint(new_params)]
                    range_lambda_map = Lambda(new_params, range_lambda_body)
                    # Obtain the appropriate end indices.
                    end_indices = \
                        [_simplifiedCoord(subtract(range_end, start_idx), 
                                          assumptions, new_requirements) 
                         for start_idx, range_end in zip(subbed_start, 
                                                          entry_end_vals)]
                    entry = Iter(range_lambda_map, subbed_start, end_indices)
                # Set this entry in the entries array.
                ExprArray.set_entry(entries, entry_start_indices, entry)
                '''
            subbed_self = compositeExpression(entries)     
        else:
            # No Indexed sub-Expressions whose variable is 
            # replaced with a Composite, so let us not expand the
            # iteration.  Just do an ordinary substitution.
            new_requirements = [] # Fresh new requirements.
            subbed_map = self.lambda_map.substituted(exprMap, relabelMap, 
                                reservedVars, assumptions, new_requirements)
            subbed_self = Iter(subbed_map.parameters, subbed_map.body, 
                               subbed_start, subbed_end)
        
        for requirement in new_requirements:
            # Make sure requirements don't use reserved variable in a 
            # nested scope.
            requirement._restrictionChecked(reservedVars)      
        if requirements is not None:
            requirements += new_requirements # append new requirements
        
        return subbed_self


def varIter(var, start, end):
    from proveit import safeDummyVar
    from .indexed import Indexed
    param = safeDummyVar(var)
    return Iter(param, Indexed(var, param), start, end)

class IterationError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

class InvalidIterationError(IterationError):
    def __init__(self, index, parameter):
        msg = ("Iterations must only contain Indexed variables with "
               "indices that are 'simple' functions of an iteration " 
               "(the parameter itself or a sum of terms with one term "
               "as the parameter), not %s with %s as a parameter."
               %(index, parameter))
        IterationError.__init__(self, msg) 

class EmptyIterException(Exception):
    def __init__(self):
        pass
 
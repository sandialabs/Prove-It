from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
from proveit._core_.expression.composite import Composite, ExprTuple, singleOrCompositeExpression, compositeExpression
from proveit._core_.defaults import defaults, USE_DEFAULTS
import itertools

class Iter(Expression):
    '''
    An Iter Expression represents an iteration of
    Expressions to be inserted into a containing
    composite Expression.
    
    Upon substitution, it automatically expands to
    a list (tensor) if the difference between the end 
    index (indices) and start index (indices)
    is (are) a known integer(s).
    '''

    def __init__(self, parameter_or_parameters, body, start_index_or_indices, end_index_or_indices, styles=None, requirements=tuple()):
        from proveit.logic import InSet
        from proveit.number import Interval
        
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
        
        self.ndims = len(self.start_indices)
        if self.ndims != len(self.end_indices):
            raise ValueError("Inconsistent number of 'start' and 'end' indices")
        
        if len(parameters) != len(self.start_indices):
            raise ValueError("Inconsistent number of indices and lambda map parameters")
        
        conditions = []
        for param, start_index, end_index in zip(parameters, self.start_indices, self.end_indices):
            conditions.append(InSet(param, Interval(start_index, end_index)))
        
        lambda_map = Lambda(parameters, body, conditions=conditions)
        Expression.__init__(self, ['Iter'], [lambda_map], styles=styles, requirements=requirements)
        self.lambda_map = lambda_map
    
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
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        from proveit.logic import InSet
        from proveit.number import Interval
        if subClass != Iter: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'Iter':
            raise ValueError("Expecting Iter coreInfo to contain exactly one item: 'Iter'")
        lambda_map = subExpressions[0]
        if len(lambda_map.parameters) != len(lambda_map.conditions):
            raise ValueError("Expecting the same number of parameters and conditions")
        start_indices = []
        end_indices = []
        for param, condition in zip(lambda_map.parameters, lambda_map.conditions):
            if not isinstance(condition, InSet) or condition.element != param or not isinstance(condition.domain, Interval):
                raise ValueError("Expecting each 'Iter' condition to define an 'Interval' domain for the corresponding parameter")
            start_indices.append(condition.domain.lowerBound)
            end_indices.append(condition.domain.upperBound)
        return Iter(lambda_map.parameters, lambda_map.body, start_indices, end_indices).withStyles(**styles)
            
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
        Return the first instance of the iteration.
        '''
        return self.lambda_map.body.substituted({parameter:index for parameter, index in zip(self.lambda_map.parameters, self.start_indices)})

    def last(self):
        '''
        Return the last instance of the iteration.
        '''
        return self.lambda_map.body.substituted({parameter:index for parameter, index in zip(self.lambda_map.parameters, self.end_indices)})
        
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
        from proveit.number import Less
        
        if self.ndims==1:
            indices = [index_or_indices]
        else:
            indices = index_or_indices

        if requirements is None: requirements = [] # requirements won't be passed back in this case
        
        # first make sure that the indices are in the iteration range
        for index, start, end in zip(indices, self.start_indices, self.end_indices):
            for first, second in ((start, index), (index, end)):
                relation = None
                try:
                    relation = Less.sort([first, second], reorder=False, assumptions=assumptions)
                except:
                    raise IterationError("Indices not provably within the iteration range: %s <= %s"%(first, second)) 
                requirements.append(relation)
        
        # map to the desired instance
        return self.lambda_map.mapped(*indices)
    
    def _makeNonoverlappingRangeSet(self, rel_iter_ranges, arg_sorting_relations, assumptions, requirements):
        '''
        Helper method for substituted.
        Check for overlapping relative iteration ranges, 
        breaking them up when found and returning the new
        set of ranges with no overlaps.
        '''
        from proveit.number import Add, subtract, one
        from .composite import _simplifiedCoord
        owning_range = dict() # map relative indices to the owning range; overlap occurs when ownership is contested.
        nonoverlapping_ranges = set()
        while len(rel_iter_ranges) > 0:
            rel_iter_range = rel_iter_ranges.pop()
            for p in itertools.product(*[range(start, end) for start, end in zip(*rel_iter_range)]):
                p = tuple(p)
                # Check for contested ownership
                if p in owning_range and owning_range[p] in nonoverlapping_ranges:
                    # Split along the first axis that differs,
                    # adding the split ranges back in.  If there are still 
                    # distinct overlapping ranges after that split, there may be
                    # further splits along different axes.
                    range1, range2 = rel_iter_range, owning_range[p]
                    for axis, (start1, end1, start2, end2) in enumerate(zip(*(range1 + range2))):
                        if start1 != start2 or end1 != end2:
                            # (re)assign range1 to have the earliest start.
                            if start1 > start2:
                                range1, range2 = range2, range1
                                start1, end1, start2, end2 = start2, end2, start1, end1
                            if start1 < start2:
                                # add the first range
                                first_range = (tuple(range1[0]), tuple(range1[1]))
                                abs_end = _simplifiedCoord(subtract(arg_sorting_relations.operands[start2], one), assumptions=assumptions, requirements=requirements)
                                first_range[1][axis] = arg_sorting_relations.index(abs_end)
                                rel_iter_ranges.add(first_range)
                            mid_end = min(end1, end2)
                            if start2 < min(end1, end2):
                                # add the middle ranges (one from each of the originals
                                # where the overlap occurs. 
                                for orig_range in (range1, range2):
                                    mid_range = (tuple(orig_range[0]), tuple(orig_range[1]))
                                    mid_range[1][axis] = end
                                    rel_iter_ranges.add(mid_range)
                            end = max(end1, end2)
                            if mid_end < end:
                                # add the last range
                                last_range = (tuple(range2[0]), tuple(range2[1]))
                                abs_start = _simplifiedCoord(Add(arg_sorting_relations.operands[mid_end], one), assumptions=assumptions, requirements=requirements) 
                                first_range[0][axis] = arg_sorting_relations.index(abs_start)
                                rel_iter_ranges.add(last_range)
                            break
                    # remove/exclude the obsolete originals
                    nonoverlapping_ranges.discard(owning_range[p])
                    rel_iter_range = None
                    break
                else:
                    owning_range[p] = rel_iter_range
            if rel_iter_range is not None:
                nonoverlapping_ranges.add(rel_iter_range)
        return nonoverlapping_ranges
                
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
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
        from proveit.logic import Equals
        from proveit.number import Less, LessEq, subtract, Add, one
        from .composite import _simplifiedCoord
        from proveit._core_.expression.expr import _NoExpandedIteration
        from proveit._core_.expression.label.var import safeDummyVars
        
        self._checkRelabelMap(relabelMap)
        if relabelMap is None: relabelMap = dict()
        
        assumptions = defaults.checkedAssumptions(assumptions)
        arg_sorting_assumptions = list(assumptions)
        
        new_requirements = []
        
        # Collect the iteration ranges from Indexed sub-Expressions
        # whose variable is being replaced with a Composite (list or tensor).
        # If there are not any, we won't expand the iteration at this point.
        # While we are at it, get all of the end points of the
        # ranges along each axis (as well as end points +/-1 that may be
        # needed if there are overlaps): 'special_points'.
        iter_ranges = set()
        iter_params = self.lambda_map.parameters
        special_points = [set() for _ in range(len(iter_params))]
        subbed_start = self.start_indices.substituted(exprMap, relabelMap, reservedVars, assumptions, new_requirements)
        subbed_end = self.end_indices.substituted(exprMap, relabelMap, reservedVars, assumptions, new_requirements)
        try:
            # Need to handle the change in scope within the lambda expression
            new_params, inner_expr_map, inner_assumptions, inner_reservations = self.lambda_map._innerScopeSub(exprMap, relabelMap, reservedVars, assumptions, requirements)
            # We won't use 'new_params'.  They aren't relavent after an expansion.
            # If there is not expansion, we will break out of the try block.
            
            for iter_range in self.lambda_map.body._expandingIterRanges(iter_params, subbed_start, subbed_end, inner_expr_map, relabelMap, inner_reservations, inner_assumptions, new_requirements):
                iter_ranges.add(iter_range)
                for axis, (start, end) in enumerate(zip(*iter_range)):
                    special_points[axis].add(start)
                    special_points[axis].add(end)
                    # Preemptively include start-1 and end+1 in case it is required for splitting up overlapping ranges
                    # (we won't add simplification requirements until we find we actually need them.)
                    # Not necesary in the 1D case.
                    # Add the coordinate simplification to argument sorting assumptions -
                    # after all, this sorting does not go directly into the requirements.
                    start_minus_one = _simplifiedCoord(subtract(start, one), assumptions=assumptions, requirements=arg_sorting_assumptions)
                    end_plus_one = _simplifiedCoord(Add(end, one), assumptions=assumptions, requirements=arg_sorting_assumptions)
                    special_points[axis].update({start_minus_one, end_plus_one})
                    # Add start-1<start and end<end+1 assumptions to ease argument sorting -
                    # after all, this sorting does not go directly into the requirements.
                    arg_sorting_assumptions.append(Less(start_minus_one, start))
                    arg_sorting_assumptions.append(Less(end, end_plus_one))
                    arg_sorting_assumptions.append(Equals(end, subtract(end_plus_one, one)))
                    # Also add start<=end to ease the argument sorting requirement even though it
                    # may not strictly be true if an empty range is possible.  In such a case, we
                    # still want things sorted this way while we don't know if the range is empty or not
                    # and it does not go directly into the requirements.
                    arg_sorting_assumptions.append(LessEq(start, end))
            
            # add the assumptions for applying ordering transitivity rules used to
            # sort special points (these relations may or may not need to be added as actual requirements;
            # in this initial processing, we want everything to go through even if some of these theorems are
            # not "usable" in this context).
            try:
                from proveit.logic.equality._theorems_ import subLeftSideInto, subRightSideInto, equalsReversal
                from proveit.number.ordering._theorems_ import transitivityLessLess, transitivityLessEqLess, transitivityLessLessEq, transitivityLessEqLessEq
                from proveit.number.addition.subtraction._theorems_ import subtractFromAdd, addFromSubtract
                arg_sorting_assumptions.extend([subLeftSideInto.expr, subRightSideInto.expr, equalsReversal.expr])
                arg_sorting_assumptions.extend([transitivityLessLess.expr, transitivityLessEqLess.expr, transitivityLessLessEq.expr, transitivityLessEqLessEq.expr])
                arg_sorting_assumptions.extend([subtractFromAdd.expr, addFromSubtract.expr])
            except:
                pass # skip this if the theorems have not be defined yet 
            
            # There are Indexed sub-Expressions whose variable is
            # being replaced with a Composite, so let us
            # expand the iteration for all of the relevant
            # iteration ranges.
            # Sort the argument value ranges.

            arg_sorting_relations = []
            for axis in range(self.ndims):
                if len(special_points[axis])==0:
                    arg_sorting_relation = None
                else:
                    arg_sorting_relation = Less.sort(special_points[axis], assumptions=arg_sorting_assumptions)
                arg_sorting_relations.append(arg_sorting_relation)
                        
            # Put the iteration ranges in terms of indices of the sorting relation operands
            # (relative indices w.r.t. the sorting relation order).
            rel_iter_ranges = set()
            for iter_range in iter_ranges:
                range_start, range_end = iter_range
                rel_range_start = tuple([arg_sorting_relation.operands.index(arg) for arg, arg_sorting_relation in zip(range_start, arg_sorting_relations)])
                rel_range_end = tuple([arg_sorting_relation.operands.index(arg) for arg, arg_sorting_relation in zip(range_end, arg_sorting_relations)])
                rel_iter_ranges.add((rel_range_start, rel_range_end))
            
            rel_iter_ranges = sorted(self._makeNonoverlappingRangeSet(rel_iter_ranges, arg_sorting_relations, assumptions, new_requirements))
            
            #print arg_sorting_relations
            # Generate the expanded list/tensor to replace the iterations.
            if self.ndims==1: lst = []
            else: tensor = dict()            
            for rel_iter_range in rel_iter_ranges:
                #print rel_iter_range
                # get the starting location of this iteration range
                start_loc = tuple(arg_sorting_relation.operands[idx] for arg_sorting_relation, idx in zip(arg_sorting_relations, rel_iter_range[0]))
                if rel_iter_range[0] == rel_iter_range[1]:
                    # single element entry (starting and ending location the same)
                    entry_inner_expr_map = dict(inner_expr_map)
                    entry_inner_expr_map.update({param:arg for param, arg in zip(self.lambda_map.parameters, start_loc)})
                    for param in self.lambda_map.parameters: relabelMap.pop(param, None)
                    entry = self.lambda_map.body.substituted(entry_inner_expr_map, relabelMap, inner_reservations, inner_assumptions, new_requirements)
                else:
                    # iterate over a sub-range
                    end_loc = tuple(arg_sorting_relation.operands[idx] for arg_sorting_relation, idx in zip(arg_sorting_relations, rel_iter_range[1]))
                    # Shift the iteration parameter so that the iteration will have the same start-indices
                    # for this sub-range (like shifting a viewing window, moving the origin to the start of the sub-range).
                    # Include assumptions that the lambda_map parameters are in the shifted start_loc to end_loc range.
                    range_expr_map = dict(inner_expr_map)
                    range_assumptions = []
                    #print start_loc, end_loc, range_expr_map, range_assumptions, self.lambda_map
                    # generate "safe" new parameters (the Variables are not used for anything that might conflict).
                    new_params = safeDummyVars(len(self.lambda_map.parameters), *([self] + list(range_expr_map.values()) + list(relabelMap.values())))
                    for start_idx, param, new_param, range_start, range_end in zip(self.start_indices, self.lambda_map.parameters, new_params, start_loc, end_loc):
                        range_expr_map[param] = Add(new_param, subtract(range_start, start_idx))
                        range_assumptions.append(LessEq(start_idx, new_param))
                        range_assumptions.append(LessEq(new_param, subtract(range_end, start_idx)))
                        #range_assumptions.append(LessEq(range_start, param))
                        #range_assumptions.append(LessEq(param, range_end))
                    #print range_expr_map, range_assumptions
                    # We don't need to use inner reservations.  The fact that our "new parameters" are "safe" alleviates the need to reserve anything extra.
                    range_lambda_body = self.lambda_map.body.substituted(range_expr_map, relabelMap, reservedVars, inner_assumptions+range_assumptions, new_requirements)
                    # Any requirements that involve the new parameters are a direct consequent of the iteration range and are
                    # not external requirements:
                    #   (PERHAPS THES REQUIREMENTS
                    new_requirements = [requirement for requirement in new_requirements if requirement.freeVars().isdisjoint(new_params)]
                    range_lambda_map = Lambda(new_params, range_lambda_body)
                    # Add the shifted sub-range iteration to the appropriate starting location.
                    end_indices = [_simplifiedCoord(subtract(range_end, start_idx), assumptions, new_requirements) for start_idx, range_end in zip(self.start_indices, end_loc)]
                    entry = Iter(range_lambda_map, self.start_indices, end_indices)
                if self.ndims==1: lst.append(entry)
                else: tensor[start_loc] = entry

            if self.ndims==1:
                subbed_self = compositeExpression(lst)
            else:
                subbed_self = compositeExpression(tensor)

        except _NoExpandedIteration:
            # No Indexed sub-Expressions whose variable is 
            # replaced with a Composite, so let us not expand the
            # iteration.  Just do an ordinary substitution.
            subbed_map = self.lambda_map.substituted(exprMap, relabelMap, reservedVars, assumptions, new_requirements)
            subbed_self = Iter(subbed_map.parameters, subbed_map.body, subbed_start, subbed_end)
        
        for requirement in new_requirements:
            requirement._restrictionChecked(reservedVars) # make sure requirements don't use reserved variable in a nested scope        
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


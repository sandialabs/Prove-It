from proveit._core_.expression import Expression
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
from proveit._core_.expression.label import Literal
from proveit._core_.expression.composite import compositeExpression
from proveit._core_.defaults import Defaults, USE_DEFAULTS
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
    
    # The operator of the And operation
    _operator_ = Literal(stringFormat='iter', context=__file__)
    
    def __init__(self, lambda_map, start_index_or_indices, end_index_or_indices):
        from composite import Composite, singleOrCompositeExpression, compositeExpression
        if not isinstance(lambda_map, Lambda):
            raise TypeError('When creating an Iter Expression, the lambda_map argument must be a Lambda expression')
        
        start_index_or_indices = singleOrCompositeExpression(start_index_or_indices)
        if isinstance(start_index_or_indices, Composite):
            # a composite of multiple indices
            self.start_indices = start_index_or_indices 
        else:
            # a single index
            self.start_index = start_index_or_indices
            # wrap a single index in a composite for convenience
            self.start_indices = compositeExpression(start_index_or_indices)

        end_index_or_indices = singleOrCompositeExpression(end_index_or_indices)
        if isinstance(end_index_or_indices, Composite):
            # a composite of multiple indices
            self.end_indices = end_index_or_indices 
        else:
            # a single index
            self.end_index = end_index_or_indices
            # wrap a single index in a composite for convenience
            self.end_indices = compositeExpression(end_index_or_indices)                        
        
        self.ndims = len(self.start_indices)
        if self.ndims != len(self.end_indices):
            raise ValueError("Inconsistent number of 'start' and 'end' indices")
        
        if len(lambda_map.parameters) != len(self.start_indices):
            raise ValueError("Inconsistent number of indices and lambda map parameters")
        
        Expression.__init__(self, ['Iter'], [lambda_map, start_index_or_indices, end_index_or_indices])
        self.lambda_map = lambda_map
    
    
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
        # fence by default (unless it is within an Embed
        fence =  kwargs['fence'] if 'fence' in kwargs else True 
        innerStr = self.first().string() + ', ..., ' + self.last().string()
        return maybeFenced('string', innerStr, fence=fence)

    def latex(self, **kwargs):
        # fence by default (unless it is within an Embed
        fence =  kwargs['fence'] if 'fence' in kwargs else True
        innerStr = self.first().latex() + ', \ldots, ' + self.last().latex()
        return maybeFenced('latex', innerStr, fence=fence)
    
    def getInstance(self, indices, assumptions = USE_DEFAULTS, requirements = None):
        '''
        Return the iteration instance with the given indices
        as an Expression, using the given assumptions as needed
        to interpret the indices expression.  Required
        truths, proven under the given assumptions, that 
        were used to make this interpretation will be
        appended to the given 'requirements' (if provided).
        '''
        from proveit.number import proven_sort, Less, LessEq
        
        # first make sure that the indices are in the iteration range
        for index, start, end in zip(indices, self.start_indices, self.end_indices):
            for first, second in ((start, index), (index, end)):
                relation = None
                try:
                    relation = proven_sort([first, second], reorder=False, assumptions=assumptions)
                except:
                    raise IterationError("Indices not provably within the iteration range: %s <= %s"%(first, second)) 
                requirements.append(relation)
        
        # map to the desired instance
        return self.lambda_map.mapped(indices)
    
    def _makeNonoverlappingRangeSet(self, rel_iter_ranges):
        '''
        Helper method for substituted.
        Check for overlapping relative iteration ranges, 
        breaking them up when found and returning the new
        set of ranges with no overlaps.
        '''
        owning_range = dict() # map relative indices to the owning range; overlap occurs when ownership is contested.
        nonoverlapping_ranges = set()
        while len(rel_iter_ranges) > 0:
            rel_iter_range = rel_iter_ranges.pop()
            for p in itertools.product(*[xrange(start, end) for start, end in zip(rel_iter_range)]):
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
                                abs_end = _simplifiedCoord(Subtract(arg_sorting_relations.operands[start2], one), assumptions=assumptions, requirements)
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
                                abs_start = _simplifiedCoord(Add(arg_sorting_relations.operands[mid_end], one), assumptions=assumptions, requirements) 
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
                
    def substituted(self, exprMap, relabelMap = None, reservedVars = None, assumptions=USE_DEFAULTS, requirements=None):
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
        from proveit.number import proven_sort, Subtract, Add, one
        from composite import _simplifiedCoord
        
        assumptions = Defaults.checkedAssumptions(assumptions)
        
        # Collect the iteration ranges from Indexed sub-Expressions
        # whose variable is being replaced with a Composite (list or tensor).
        # If there are not any, we won't expand the iteration at this point.
        # While we are at it, get all of the end points of the
        # ranges along each axis (as well as end points +/-1 that may be
        # needed if there are overlaps): 'special_points'.
        iter_ranges = set()
        iter_params = self.lambda_map.parameters
        special_points = [set() for _ in xrange(len(iter_params))]
        for iter_range in self.lambda_map.body.iterRanges(iter_params, self.start_indices, self.end_indices, exprMap, relabelMap, reservedVars, assumptions, requirements):
            iter_ranges.add(iter_range)
            for axis, (start, end) in enumerate(zip(iter_range)):
                special_points[axis].add(start)
                special_points[axis].add(end)
                # Preemptively include start-1 and end+1 in case it is required for splitting up overlapping ranges
                # (we won't add simplification requirements until we find we actually need them.
                special_points[axis].add(_simplifiedCoord(Subtract(start, one), assumptions=assumptions, requirements=None))
                special_points[axis].add(_simplifiedCoord(Add(end, one), assumptions=assumptions, requirements=None))
        
        if len(iter_ranges) == 0:
            # No Indexed sub-Expressions whose variable is 
            # replaced with a Composite, so let us not expand the
            # iteration.  Just do an ordinary substitution.
            subbed_map = self.lambda_map.substituted(self, exprMap, relabelMap, reservedVars, assumptions, requirements)
            subbed_start = self.start_indices.substituted(self, exprMap, relabelMap, reservedVars, assumptions, requirements)
            subbed_end = self.end_indices.substituted(self, exprMap, relabelMap, reservedVars, assumptions, requirements)
            return Iter(subbed_map, subbed_start, subbed_end)
        else:
            # There are Indexed sub-Expressions whose variable is
            # being replaced with a Composite, so let us
            # expand the iteration for all of the relevant
            # iteration ranges.
            
            # Sort the argument value ranges.
            arg_sorting_relations = []
            for axis in xrange(len(iter_params)):
                arg_sorting_relation = proven_sort(special_points[axis], assumptions=assumptions)
                arg_sorting_relations.append(arg_sorting_relation)
            
            # Put the iteration ranges in terms of indices of the sorting relation operands
            # (relative indices w.r.t. the sorting relation order).
            rel_iter_ranges = set()
            for iter_range in iter_ranges:
                range_start, range_end = iter_range
                rel_range_start = tuple([arg_sorting_relation.operands.index(arg) for arg, arg_sorting_relation in zip(range_start, arg_sorting_relations)])
                rel_range_end = tuple([arg_sorting_relation.operands.index(arg) for arg, arg_sorting_relation in zip(range_end, arg_sorting_relations)])
                rel_iter_ranges.add((rel_range_start, rel_range_end))
            
            rel_iter_ranges = self.__makeNonoverlappingRangeSet(rel_iter_ranges)
            
            # Generate the expanded list/tensor to replace the iterations.
            if self.ndims==1: lst = []
            else: tensor = dict()            
            for rel_iter_range in rel_iter_ranges:
                # get the starting location of this iteration range
                start_loc = tuple(arg_sorting_relation.oparands[idx] for arg_sorting_relation, idx in zip(arg_sorting_relations, rel_iter_range[0]))
                if rel_iter_range[0] == rel_iter_range[1]:
                    # single element entry (starting and ending location the same)
                    entry = self.lambda_map.mapped(start_loc)
                else:
                    # iterate over a sub-range
                    end_loc = tuple(arg_sorting_relation.operands[idx] for arg_sorting_relation, idx in zip(arg_sorting_relations, rel_iter_range[1]))
                    # Shift the iteration parameter so that the iteration will have the same start-indices
                    # for this sub-range (like shifting a viewing window, moving the origin to the start of the sub-range).
                    # Include assumptions that the lambda_map parameters are in the shifted start_loc to end_loc range.
                    range_expr_map = dict(exprMap)
                    range_assumptions = list(assumptions)
                    for start_idx, param, range_start, range_end in zip(self.start_indices, self.lambda_map.parameters, start_loc, end_loc):
                        range_expr_map[param] = Add(param, Subtract(range_start, start_idx))
                        range_assumptions += proven_sort((start_idx, param), reorder=False, assumptions=assumptions)
                        range_assumptions += proven_sort((param, Subtract(range_end, start_idx)), reorder=False, assumptions=assumptions)
                    range_lambda_body = self.lambda_map.body.substituted(range_expr_map, relabelMap, reservedVars, range_assumptions, requirements)
                    range_lambda_map = Lambda(self.lambda_map.parameters, range_lambda_body)
                    # Add the shifted sub-range iteration to the appropriate starting location.
                    end_indices = [_simplifiedCoord(Subtract(range_end, start_idx), assumptions, requirements) for start_idx, range_end in zip(self.start_indices, end_loc)]
                    entry = Iter(range_lambda_map, self.start_indices, end_indices)
                if self.ndims==1: lst.append(entry)
                else: tensor[start_loc] = entry
            if self.ndims==1:
                return compositeExpression(lst)
            else:
                return compositeExpression(tensor)
        
        
        
        
        
        """
        try:
            diffs = []
            for start_index, end_index in zip(subbed.start_indices, subbed.end_indices):
                # If we can evaluate the difference between the end_index and start_index
                # as an integer, then we must expand the iteration for index values from
                # the start_index to the end_index.
           s     diff = Subtract(subbed.end_index, subbed.start_index).evaluate(assumptions=assumptions)
                diffs.append(diff)
                
            if not all(isLiteralInt(diff) for diff in diffs):
                # The differences are not literal integers, we cannot expand
                # the iteration, so we just return the subbed Iter as-is.
                return subbed
        except:
            # We cannot evaluate the difference between the end and start indices. 
            # Then we cannot expand the iteration.  Just return the subbed Iter as-is.
            return subbed            
        
        # The difference between end and start indices can be evaluated as literal integers,
        # so we can and should expand the Iter into an ExprList or ExprTensor that iterates
        # over the index values.
        index_lists = [[] for _ in xrange(len(subbed.start_indices))]
        for start_index, end_index, index_list in zip(subbed.start_indices, subbed.end_indices, index_lists):
            # If we can evaluate the difference between the end_index and start_index
            # as an integer, then we must expand the iteration for index values from
            # the start_index to the end_index.
            if diff.asInt() < 0:
                # end_index < start_index
                requirements.append(Less(subbed.end_index, subbed.start_index))
                continue # empty index list
            index = _simplifiedCoord(subbed.start_index, assumptions, requirements)
            end = _simplifiedCoord(subbed.end_index, assumptions, requirements)
            while True: 
                index_list.append(index)
                if index == end:
                    break # made it to the end
                # increment to the next index and simplify the index
                index = _simplifiedCoord(Add(index, one), assumptions, requirements)
        
        if len(index_lists) == 1:
            # A 1D ExprList
            index_list = index_list[0]
            return ExprList([self.lambda_map.body.substituted({self.lambda_map.parameter:index}, assumptions=assumptions, requirements=requirements) for index in index_list])
        else:
            # A multi-dimensional ExprTensor
            tensor = dict()
            for indices in itertools.product(*index_lists):
                tensor[indices] = self.lambda_map.body.substituted({parameter:index for parameter, index in zip(self.lambda_map.parameters, indices)}, assumptions=assumptions, requirements=requirements)
            return ExprTensor(tensor)

        """


class IterationError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg


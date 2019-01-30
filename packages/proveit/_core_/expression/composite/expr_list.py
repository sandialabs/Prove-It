from .composite import Composite, _simplifiedCoord
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.defaults import USE_DEFAULTS

class ExprList(Composite, Expression):
    """
    An ExprList is a composite expr composed of an ordered list of member
    Expressions.
    """
    def __init__(self, *expressions):
        '''
        Initialize an ExprList from an iterable over Expression objects.
        '''
        from proveit._core_ import KnownTruth
        from .composite import singleOrCompositeExpression
        entries = []
        for entry in expressions:
            if isinstance(entry, KnownTruth):
                entry = entry.expr # extract the Expression from the KnownTruth
            try:
                entry = singleOrCompositeExpression(entry)
                assert isinstance(entry, Expression)
            except:
                raise TypeError('ExprList must be created out of Expressions)')
            entries.append(entry)
        self.entries = entries
        self._sortedCoords = []
        Expression.__init__(self, ['ExprList'], self.entries)
        
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != ExprList: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'ExprList':
            raise ValueError("Expecting ExprList coreInfo to contain exactly one item: 'ExprList'")
        return ExprList(*subExpressions).withStyles(**styles)      

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the ExprList.
        '''
        for subExpr in self.subExprIter():
            yield subExpr

    def _expandingIterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        from proveit._core_.expression.expr import _NoExpandedIteration
        # Collect the iteration ranges for all of the entries.
        iter_ranges = set()
        has_expansion = False
        for entry in self.entries:
            try:
                for iter_range in entry._expandingIterRanges(iterParams, startArgs, endArgs, exprMap, relabelMap, reservedVars, assumptions, requirements):
                    iter_ranges.add(iter_range)
                has_expansion = True
            except _NoExpandedIteration:
                pass
        if not has_expansion:
            raise _NoExpandedIteration()
        for iter_range in iter_ranges:
            yield iter_range
                                        
    def __iter__(self):
        '''
        Iterator over the entries of the list.
        Some entries may be iterations (Iter) that 
        represent multiple elements of the list.
        '''
        return iter(self.entries)
    
    def __len__(self):
        '''
        Return the number of entries of the list.
        Some entries may be iterations (Iter) that 
        represent multiple elements of the list.
        '''
        return len(self.entries)

    def __getitem__(self, i):
        '''
        Return the list entry at the ith index.
        This is a relative entry-wise index where
        entries may represent multiple elements
        via iterations (Iter).
        '''
        return self.entries[i]

    def getElem(self, index, base=1, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return the list element at the index, given
        as an Expression, using the given assumptions as needed
        to interpret the location expression.  Required
        truths, proven under the given assumptions, that 
        were used to make this interpretation will be
        appended to the given 'requirements' (if provided).
        '''
        from proveit.number import num, one, lesserSequence, Less, LessEq, Add, Subtract
        from proveit.logic import Equals
        from .iteration import Iter
        from .composite import _simplifiedCoord
        
        if requirements is None:
            requirements = [] # create the requirements list, but it won't be used
        
        sorted_coords = []
        less_operators = [] 
        coord = num(base)
        sorted_coords.append(coord)
        coord_sort_requirements = []
        for entry in self.entries:
            if isinstance(entry, Iter):
                coord = _simplifiedCoord(Add(coord, Subtract(entry.end_index, entry.start_index)), assumptions, coord_sort_requirements)
                less_operators.append(LessEq._operator_) # we don't necessarily know if coord < coord+(entry.end_index-entry.start_index)
            else:
                coord = _simplifiedCoord(Add(coord, one), assumptions, coord_sort_requirements)
                less_operators.append(Less._operator_) # we know coord < coord+1
            sorted_coords.append(coord)
        sorted_coords = lesserSequence(less_operators, sorted_coords)
        try:
            sorted_coords_with_index = sorted_coords.insert(index, assumptions=assumptions)
            upper = sorted_coords_with_index.operands.index(index) # coord above 'index' in the sorted order
            if sorted_coords.operands[upper]==index:
                lower = upper # 'index' is one of the coordinates
            elif upper>0 and sorted_coords_with_index.operators[upper-1]==Equals._operator_:
                lower = upper = upper-1 # 'index' is '=' to the coordinate below it
            elif upper<len(sorted_coords_with_index.operators) and sorted_coords_with_index.operators[upper]==Equals._operator_:
                lower = upper # 'index' is '=' to the coordinate after it
            else:
                lower = upper-1 # 'index' is not known to be the same as any of the existing coordinates
        except:
            raise ExprListError("Could not determine the 'index' range within the ExprList coordinates under the given assumptions")
        requirements += coord_sort_requirements[:lower]
        # The relationship to the lower and upper coordinate bounds are requirements for determining
        # the element being assessed.
        if upper > 0 and sorted_coords.operands[lower] != index:
            requirements.append(LessEq.sort((sorted_coords.operands[lower], index), reorder=False, assumptions=assumptions))
        if lower<upper and upper<len(sorted_coords.operands) and sorted_coords.operands[upper] != index:
            requirements.append(LessEq.sort((index, sorted_coords.operands[upper]), reorder=False, assumptions=assumptions))
        
        entry = self[lower]
        if isinstance(entry, Iter):
            # indexing into an iteration
            entry_origin = sorted_coords[lower]
            iter_start_index = entry.start_index
            iter_loc = Add(iter_start_index, Subtract(index, entry_origin))
            simplified_iter_loc = _simplifiedCoord(iter_loc, assumptions, requirements)
            return entry.getInstance(simplified_iter_loc, assumptions=assumptions, requirements=requirements)
        else:
            # just a single-element entry
            assert lower==upper, "A single-element entry should not have been determined if there was an ambiguous range for the 'index'"
            return entry        
        
    def __add__(self, other):
        '''
        Concatenate ExprList's together via '+' just like
        Python lists.  Actually works with any iterable
        of Expressions as the second argument.
        '''
        return ExprList(*(self.entries + list(other)))
    
    def singular(self):
        '''
        Return True if this has a single element that is not an
        iteration.
        '''
        from .iteration import Iter
        return len(self)==1 and not isinstance(self[0], Iter)
    
    def index(self, entry):
        return self.entries.index(entry)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=True, subFence=False, formattedOperator=None, wrapPositions=tuple()):
        from .iteration import Iter
        outStr = ''
        if len(self) == 0 and fence: 
            # for an empty list, show the parenthesis to show something.            
            return '()'
        if formattedOperator is None:
            formattedOperator = ',' # comma is the default formatted operator
        ellipses = r'\ldots' if formatType=='latex' else ' ... '
        formatted_sub_expressions = []
        for sub_expr in self:
            if isinstance(sub_expr, Iter):
                formatted_sub_expressions += [sub_expr.first().formatted(formatType, fence=subFence), ellipses, sub_expr.last().formatted(formatType, fence=subFence)]
            elif isinstance(sub_expr, ExprList):
                # always fence nested expression lists                
                formatted_sub_expressions.append(sub_expr.formatted(formatType, fence=True))
            else:
                formatted_sub_expressions.append(sub_expr.formatted(formatType, fence=subFence))
        # put the formatted operator between each of formattedSubExpressions
        if fence: 
            outStr += '(' if formatType=='string' else  r'\left('
        for wrap_position in wrapPositions:
            if wrap_position%2==1:
                # wrap after operand (before next operation)
                formatted_sub_expressions[(wrap_position-1)//2] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_sub_expressions[wrap_position//2] = r' \\ ' + formatted_sub_expressions[wrap_position//2]
        outStr += (' '+formattedOperator+' ').join(formatted_sub_expressions)
        if fence:            
            outStr += ')' if formatType=='string' else  r'\right)'
        return outStr
    
    def entryRanges(self, base, start_index, end_index, assumptions, requirements):
        '''
        For each entry of the list that is fully or partially contained in the window defined
        via start_indices and end_indices (as Expressions that can be provably sorted
        against list indices), yield the start and end of the intersection of the
        entry range and the window.
        '''
        from proveit.number import one, num, Add, Subtract, Less
        from proveit.logic import Equals
        from .iteration import Iter
        from proveit import ProofFailure
        
        if requirements is None: requirements = [] # requirements won't be passed back in this case
        
        index = num(base)
        started = False
        prev_end = None

        try:
            start_end_relation = Less.sort([start_index, end_index]).prove(assumptions=assumptions)
            if start_end_relation.operands[0]!=start_index:
                # end comes before start: the range is empty.  This is the vacuous case.
                requirements.append(start_end_relation)
                return
                yield
        except:
            # Unable to prove that the end comes before the start, so assume
            # this will be a finite iteration (if not, the user can decide
            # how long to wait before they realize they are missing something).
            pass
        
        end_index = _simplifiedCoord(end_index, assumptions, requirements) 
                        
        # Iterate over the entries and track the true element index,
        # including ranges of iterations (Iter objects).
        for i, entry in enumerate(self):
            if not started:
                # We have not yet encounted an entry within the desired window,
                # see if this entry is in the desired window.
                if index == start_index:
                    started = True # Now we've started
                else:
                    try:
                        start_relation = Less.sort([start_index, index], reorder=False, assumptions=assumptions)
                        requirements.append(start_relation)
                        if start_relation.operator==Less._operator_ and prev_end is not None:
                            # The start of the window must have occurred before this entry, 
                            # and there was a previous entry:
                            yield (start_index, prev_end) # Do the range for the previous entry.
                        started = True # Now we've started
                    except ProofFailure:
                        pass # We have not started yet.
            
            # Obtain the ending index of the entry (entry_end) and the next_index
            # (entry_end+1). 
            entry_end = index # unless it is an Iter:
            if isinstance(entry, Iter):
                entry_span = Subtract(entry.end_index, entry.start_index)
                entry_end =  _simplifiedCoord(Add(index, entry_span), assumptions, requirements)
            
            arrived_at_end = False
            if index==end_index:
                arrived_at_end = True
            else:
                try:
                    index_eq_end = Equals(end_index, index).prove(assumptions=assumptions, automation=False)
                    requirements.append(index_eq_end)
                    arrived_at_end == True
                except ProofFailure:                    
                    next_index = _simplifiedCoord(Add(entry_end, one), assumptions, requirements) 
                    """
                    # TO KEEP THINGS SIMPLE, LET'S INSIST THAT THE INDEX MUST MATCH THE END EXACTLY TO STOP
                    # (NOT GOING BEYOND WITHOUT MATCHING).
                    # The exception is when the range is empty which we test at the beginning.
                                                       
                    # See if this entry takes us to the end of the window or beyond.
                    try:
                        print next_index, end_index
                        Less.sort([next_index, end_index], reorder=False, assumptions=assumptions)
                    except ProofFailure:
                        arrived_at_end = True # we have presumably encountered the end
                        if entry_end != end_index:
                            # we require a proven relation that we are at the end
                            end_relation = Less.sort([end_index, next_index], reorder=False, assumptions=assumptions)
                            requirements.append(end_relation)
                    """
            
            if arrived_at_end:
                if started:
                    # Yield from the start of the entry to the end of the window:
                    yield (index, end_index) 
                    break
                else:
                    # The full window is within this entry.
                    start_relation = Less.sort([index, start_index], reorder=False, assumptions=assumptions)
                    requirements.append(start_relation)
                    yield (start_index, end_index) # Yield the full window that is within a single entry.
                    break
            elif started:
                # We have encountered the start but not the end.
                yield (index, entry_end) # Yield the full range of the entry.
            
            index = next_index # Move on to the next entry.
            prev_end = entry_end
        
        if not arrived_at_end:
            raise IndexError("ExprList index out of range")
        
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        Flattens nested ExprLists that arise from Embed substitutions.
        '''
        from .iteration import Iter
        self._checkRelabelMap(relabelMap)
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        subbed_exprs = []
        for expr in self:
            subbed_expr = expr.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
            if isinstance(expr, Iter) and isinstance(subbed_expr, ExprList):
                # The iterated expression is being expanded 
                # and should be embedded into the list.
                for iter_expr in subbed_expr:
                    subbed_exprs.append(iter_expr)
            else:
                subbed_exprs.append(subbed_expr)
        return ExprList(*subbed_exprs)

class ExprListError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
from composite import Composite, _simplifiedCoord
from proveit._core_.expression.expr import Expression, MakeNotImplemented

class ExprList(Composite, Expression):
    """
    An ExprList is a composite expr composed of an ordered list of member
    Expressions.
    """
    def __init__(self, expressions):
        '''
        Initialize an ExprList from an iterable over Expression objects.
        '''
        from proveit._core_ import KnownTruth
        entries = []
        for entry in expressions:
            if isinstance(entry, KnownTruth):
                entry = entry.expr # extract the Expression from the KnownTruth
            if not isinstance(entry, Expression):
                raise TypeError('ExprList must be created out of Expressions)')
            entries.append(entry)
        self.entries = entries
        Expression.__init__(self, ['ExprList'], self.entries)
        
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != ExprList: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'ExprList':
            raise ValueError("Expecting ExprList coreInfo to contain exactly one item: 'ExprList'")
        return ExprList(*subExpressions)        

    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the ExprList.
        '''
        for subExpr in self.subExprIter():
            yield subExpr
                    
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

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=True, subFence=True, formattedOperator=None):
        outStr = ''
        if len(self) == 0 and fence: return '()' # for an empty list, show the parenthesis to show something.
        if formattedOperator is None:
            formattedOperator = ',' # comma is the default formatted operator
        formattedSubExpressions = [subExpr.formatted(formatType, fence=subFence) for subExpr in self]
        # put the formatted operator between each of formattedSubExpressions
        if fence: 
            outStr += '(' if formatType=='string' else  r'\left('
        outStr += formattedOperator.join(formattedSubExpressions)
        if fence:            
            outStr += ')' if formatType=='string' else  r'\right)'
        return outStr
    
    def entryRanges(self, start_index, end_index, assumptions, requirements):
        '''
        For each entry of the tensor that is fully or partially contained in the window defined
        via start_indices and end_indices (as Expressions that can be provably sorted
        against tensor coordinates), yield the start and end of the intersection of the
        entry range and the window.
        '''
        from proveit.number import zero, one, Add, Subtract, Less
        from proveit.number import proven_sort
        from iteration import Iter
        from proveit import ProofFailure

        index = zero
        started = False
        prev_end = None

        # Iterate over the entries and track the true element index,
        # including ranges of iterations (Iter objects).
        for i, entry in enumerate(self):
            
            if not started:
                # We have not yet encounted an entry within the desired window,
                # see if this entry is in the desired window.
                try:
                    start_relation = proven_sort([start_index, index], reorder=False, assumptions=assumptions)
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
            next_index = _simplifiedCoord(Add(entry_end, one), assumptions, requirements)
            
            # See if this entry takes us to the end of the window or beyond.
            try:
                end_relation = proven_sort([next_index, end_index], reorder=False, assumptions=assumptions)
                requirements.append(end_relation)
                # We have made it to the end of the window.
                if started:
                    # Yield from the start of the entry to the end of the window:
                    yield (index, end_index) 
                    break
                else:
                    # The full window is within this entry.
                    start_relation = proven_sort([index, start_index], reorder=False, assumptions=assumptions)
                    requirements.append(start_relation)
                    yield (start_index, end_index) # Yield the full window that is within a single entry.
                    break
            except ProofFailure:
                if started:
                    # We have encountered the start but not the end.
                    yield (index, entry_end) # Yield the full range of the entry.
            
            index = next_index # Move on to the next entry.
            prev_end = entry_end
    
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        Flattens nested ExprLists that arise from Embed substitutions.
        '''
        from iter import Iter
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        subbed_exprs = []
        for expr in self:
            subbed_expr = expr.substituted(exprMap, relabelMap, reservedVars)
            if isinstance(expr, Iter) and isinstance(subbed_exprs, ExprList):
                # The iterated expression is being expanded 
                # and should be embedded into the list.
                for iter_expr in subbed_exprs:
                    subbed_exprs.append(iter_expr)
            else:
                subbed_exprs.append(subbed_expr)
        return ExprList(subbed_exprs)
        
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self])
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self])

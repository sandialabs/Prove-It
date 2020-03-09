from .composite import Composite, _simplifiedCoord
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS

class ExprTuple(Composite, Expression):
    """
    An ExprTuple is a composite Exporession composed of an ordered list 
    of member Expressions.
    """
    
    def __init__(self, *expressions):
        '''
        Initialize an ExprTuple from an iterable over Expression 
        objects.  When subsequent iterations in the tuple form a
        self-evident continuation, these iterations will be joined.
        For example, (a_1, ..., a_n, a_{n+1}, ..., a_m) will join to
        form (a_1, ..., a_m).  "Self-evident" falls under two 
        categories: the start of the second iteration is the
        successor to the end of the first iteration (e.g., n and n+1)
        or the end of the first iteration is the predecessor of the
        start of the second iteration (e.g., n-1 and n).  To be a
        valid ExprTuple, all iterations must span a range whose
        extent is a natural number.  In the above example with the
        tuple of "a"-indexed iterations, n must be a natural number
        and m-n must be a natural number for the ExprTuple to be
        valid (note that iterations may have an extent of zero).
        When an ExprTuple is created, there is not a general check
        that it is valid.  However, when deriving new known truths
        from valid existing known truths, validity is guaranteed to
        be maintained (in particular, specializations that transform
        ExprTuples ensure that validity is maintained).  The joining
        of iterations is valid as long as the original iterations
        are valid, so this process is also one that maintains validity
        which is the thing that is important.
        '''
        from proveit._core_ import KnownTruth
        from .composite import singleOrCompositeExpression
        from .iteration import Iter
        prev_entry = None
        entries = []
        for entry in expressions:
            if isinstance(entry, KnownTruth):
                # Extract the Expression from the KnownTruth:
                entry = entry.expr 
            try:
                entry = singleOrCompositeExpression(entry)
                assert isinstance(entry, Expression)
            except:
                raise TypeError("ExprTuple must be created out of "
                                  "Expressions.")
            # See if this entry should be joined with the previous
            # entry.
            if isinstance(prev_entry, Iter) and isinstance(entry, Iter):
                from proveit.number import dist_add, dist_subtract, one
                if prev_entry.lambda_map==entry.lambda_map:
                    prev_end_successor = dist_add(prev_entry.end_index, one)
                    next_start_predecessor = dist_subtract(entry.start_index, 
                                                           one)
                    if entry.start_index == prev_end_successor:
                        # Join the entries of the form
                        # (a_i, ..., a_n, a_{n+1}, ..., a_m).
                        prev_entry.end_index=entry.end_index
                        entry=None
                    elif prev_entry.end_index == next_start_predecessor:
                        # Join the entries of the form
                        # (a_i, ..., a_{n-1}, a_{n}, ..., a_m).
                        prev_entry.end_index=entry.end_index
                        entry=None
            if entry is not None:
                # Safe to append the previous entry since it does
                # not join with the new entry.
                if prev_entry is not None: entries.append(prev_entry)
                prev_entry = entry
        if prev_entry is not None:
            # One last entry to append.
            entries.append(prev_entry)
        self.entries = tuple(entries)
        self._lastEntryCoordInfo = None
        self._lastQueriedEntryIndex = 0
        Expression.__init__(self, ['ExprTuple'], self.entries)
        
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != ExprTuple: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'ExprTuple':
            raise ValueError("Expecting ExprTuple coreInfo to contain "
                               "exactly one item: 'ExprTuple'")
        return ExprTuple(*subExpressions).withStyles(**styles)      

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the ExprTuple.
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

    def getElem(self, coord, base=1, hint_idx=None,
                assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return the tuple element at the coordinate, given as an 
        Expression, using the given assumptions as needed to interpret 
        the location indicated by this expression.  Required truths, 
        proven under the given assumptions, that  were used to make this
        interpretation will be appended to the given 'requirements' 
        (if provided).
        If a hint_idx is provided, use it as a starting entry
        index from which to search for the coordinate.  Otherwise,
        use the previously queried entry as the 'hint'.
        '''
        from .composite import _generateCoordOrderAssumptions, \
            _simplifiedCoord
        from proveit.number import num, Naturals, Less, LessEq, \
            dist_add, Neg, dist_subtract
        from proveit.logic import Equals, InSet
        from proveit.relation import TransitivityException
        from .iteration import Iter
        
        if len(self)==0:
            raise ValueError("An empty ExprTuple has no elements to get")
        
        if requirements is None:
            requirements = [] # create the requirements list, but it won't be used
        
        nentries = len(self.entries)
                
        # First handle the likely case that the coordinate of the
        # element is just the starting coordinate of an entry.
        coord_to_idx = self.entryCoordToIndex(base, assumptions, requirements)
        
        coord = _simplifiedCoord(coord, assumptions, requirements)
        if coord in coord_to_idx:
            # Found the coordinate as the start of an entry.
            start_idx = coord_to_idx[coord]
            entry = self.entries[start_idx]
            if not isinstance(entry, Iter):
                self._lastQueriedEntryIndex = start_idx
                return entry # just a normal entry
            # If this is an iteration entry, we need to be careful.  
            # Ostensibly, we would want to return entry.first() but we 
            # need to be make sure it is not an empty iteration.  
            # Instead, we'll treat it like the "hard" case starting
            # from start_idx.
        elif hint_idx is not None:
            # Use the provided hint as the starting point entry
            # index.
            start_idx = hint_idx
        else:
            # We use the last queried index as the starting point
            # to make typical use-cases more efficient.
            start_idx = self._lastQueriedEntryIndex
            
        try:
            # First we need to find an entry whose starting coordinate
            # is at or beyond our desired 'coord'.  Search starting
            # from the "hint".
            coord_simp_requirements = []
            coords = self.entryCoords(base, assumptions, requirements, 
                                      coord_simp_requirements)
            coord_order_assumptions = \
                list(_generateCoordOrderAssumptions(coords))
            extended_assumptions = assumptions + coord_order_assumptions

            # Record relations between the given 'coord' and each
            # entry coordinate in case we want to reuse it.'
            relations = [None]*(nentries+1)
            
            # Search for the right 'idx' of the entry starting
            # from start_idx and going forward until we have gone
            # too far.
            for idx in range(start_idx, nentries+1):
                # Check if 'coord' is less than coords[idx]
                #print("sort", coord, coords[idx], assumptions)
                relation = LessEq.sort([coord, coords[idx]], 
                                       assumptions=extended_assumptions)
                relations[idx] = relation
                rel_first, rel_op = relation.operands[0], relation.operator
                if rel_first==coord and rel_op==Less._operator_:
                    break
                elif idx==nentries:
                    raise IndexError("Coordinate %s past the range of "
                                       "the ExprTuple, %s"%(str(coord), 
                                                            str(self)))
            
            # Now go back to an entry whose starting coordinate is less 
            # than or equal to the desired 'coord'.
            while idx > 0:
                idx -= 1
                try:
                    # Try to prove coords[idx] <= coord.
                    relation = LessEq.sort([coords[idx], coord], 
                                            assumptions=extended_assumptions,
                                            reorder = False)
                    relations[idx] = relation
                    break
                except TransitivityException:
                    # Since we could not prove that 
                    # coords[idx] <= coord, we must prove
                    # coord < coords[idx] and keep going back.
                    relation = Less(coord, coords[idx]).prove(extended_assumptions)
                    relations[idx] = relation
                    continue
            
            # We have the right index.  Include coordinate 
            # simplifications up to that point as requirements.
            coord_simp_req_map = {eq.rhs:eq for eq in coord_simp_requirements}
            for prev_coord in coords[:idx+1]:
                if prev_coord in coord_simp_req_map:
                    requirements.append(coord_simp_req_map[prev_coord])           
            
            # The 'coord' is within this particular entry.
            # Record the required relations that prove that.
            self._lastQueriedEntryIndex = idx
            requirements.append(relations[idx])
            requirements.append(relations[idx+1])
            
            # And return the appropriate element within the
            # entry.
            entry = self.entries[idx]
            if relations[idx].operator == Equals._operator_:
                # Special case -- coord at the entry origin.
                if isinstance(entry, Iter):
                    return entry.first()
                else:
                    return entry
            
            # The entry must be an iteration.
            if not isinstance(entry, Iter):
                raise ExprTupleError("Invalid coordinate, %s, in "
                                        "ExprTuple, %s."%(str(coord), 
                                                        str(self)))
            
            # Make sure the coordinate is valid and not "in between"
            # coordinates at unit intervals.
            valid_coord = InSet(dist_subtract(coord, coords[idx]), Naturals)
            requirements.append(valid_coord.prove(assumptions))
            
            # Get the appropriate element within the iteration.
            iter_start_index = entry.start_index
            iter_loc = dist_add(iter_start_index, 
                                dist_subtract(coord, coords[idx]))
            simplified_iter_loc = _simplifiedCoord(iter_loc, assumptions, 
                                                    requirements)
            # Does the same as 'entry.getInstance' but without checking
            # requirements; we don't need to worry about these requirements
            # because we already satisfied the requirements that we need.
            return entry.lambda_map.mapped(simplified_iter_loc)
        
        except ProofFailure as e:
            msg = ("Could not determine the element at "
                   "%s of the ExprTuple %s under assumptions %s."
                   %(str(coord), str(self), str(e.assumptions)))
            raise ExprTupleError(msg)

        raise IndexError("Unable to prove that "
                           "%s > %d to be within ExprTuple %s."
                           %(str(coord), base, str(self)))
    
    def __add__(self, other):
        '''
        Concatenate ExprTuple's together via '+' just like
        Python lists.  Actually works with any iterable
        of Expressions as the second argument.
        '''
        return ExprTuple(*(self.entries + tuple(other)))
    
    def singular(self):
        '''
        Return True if this has a single element that is not an
        iteration.
        '''
        from .iteration import Iter
        return len(self)==1 and not isinstance(self[0], Iter)
    
    def index(self, entry, start=0, stop=None):
        if stop is None:
            return self.entries.index(entry, start)
        else:
            return self.entries.index(entry, start, stop)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=True, subFence=False, operatorOrOperators=None, implicitFirstOperator=False, wrapPositions=tuple()):
        from .iteration import Iter
        outStr = ''
        if len(self) == 0 and fence: 
            # for an empty list, show the parenthesis to show something.            
            return '()'
        ellipses = r'\ldots' if formatType=='latex' else ' ... '
        formatted_sub_expressions = []
        for sub_expr in self:
            if isinstance(sub_expr, Iter):
                formatted_sub_expressions += [sub_expr.first().formatted(formatType, fence=subFence), ellipses, sub_expr.last().formatted(formatType, fence=subFence)]
            elif isinstance(sub_expr, ExprTuple):
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
        if operatorOrOperators is None:
            operatorOrOperators = ','
        elif isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operatorOrOperators = operatorOrOperators.formatted(formatType)
        if isinstance(operatorOrOperators, str):
            # single operator
            formatted_operator = operatorOrOperators
            outStr += (' '+formatted_operator+' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operatorOrOperators:
                if isinstance(operator, Iter):
                    formatted_operators += [operator.first().formatted(formatType), '', operator.last().formatted(formatType)]
                else:
                    formatted_operators.append(operator.formatted(formatType))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicitFirstOperator:
                    outStr = formatted_sub_expressions[0] # first operator is implicit
                else:
                    outStr = formatted_operators[0] + formatted_sub_expressions[0] # no space after first operator
                outStr += ' ' # space before next operator
                outStr += ' '.join(formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators)+1:
                # operator between each operand
                outStr = ' '.join(formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in zip(formatted_sub_expressions, formatted_operators))
                outStr += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError("May only perform ExprTuple formatting if the number of operators is equal to the number of operands (precedes each operand) or one less (between each operand); also, operator iterations must be in correpsondence with operand iterations.")
        if fence:            
            outStr += ')' if formatType=='string' else  r'\right)'
        return outStr
    
    def entryCoords(self, base, assumptions=USE_DEFAULTS, 
                     entry_span_requirements=None,
                     coord_simp_requirements=None):
        '''
        Return the simplified expressions for the coordinates of each
        entry of this ExprTuple in the proper order.  For each iteration
        entry (Iter), subsequent coordinates will account for the extent
        of that iteration.  The last coordinate is the length of the
        tuple + the base, including the extent of each iteration.
        These simplified coordinate expressions
        will be remembered and reused when a query is repeated.
        
        Appends to entry_span_requirements the requirements that ensure
        that iterations have a length that is a natural number.
        Appends to coord_simp_requirements the simplification
        equations for each coordinate.
        '''
        from proveit.logic import InSet
        from proveit.number import one, num, Naturals, \
            dist_add, dist_subtract
        from .iteration import Iter
        
        if entry_span_requirements is None: entry_span_requirements = []
        if coord_simp_requirements is None: coord_simp_requirements = []
        
        # Check to see if this was the same query as last time.
        # If so, reuse the last result.
        if self._lastEntryCoordInfo is not None:
            last_base, last_assumptions, last_span_requirements, \
            last_simp_requirements, last_coords, _ \
                = self._lastEntryCoordInfo
            if (last_base, last_assumptions) == (base, assumptions):
                # Reuse the previous result, including the requirements.
                entry_span_requirements.extend(last_span_requirements)
                coord_simp_requirements.extend(last_simp_requirements)
                return last_coords
        
        # Generate the coordinate list.
        coords = []
        new_span_requirements = []
        new_simp_requirements = []
        coord = num(base)
        for k, entry in enumerate(self):
            coords.append(coord)
            if isinstance(entry, Iter):
                entry_delta = _simplifiedCoord(dist_subtract(entry.end_index, 
                                                             entry.start_index),
                                               assumptions, new_span_requirements)
                # Add one, to get to the start of the next entry, and simplify.
                entry_span = _simplifiedCoord(dist_add(entry_delta, one), 
                                              assumptions, new_span_requirements)
                # From one entry to the next should be a natural number (could be
                # an empty entry).
                #print("simplified entry span", entry_span)
                requirement = InSet(entry_span, Naturals)
                try:
                    requirement = requirement.prove(assumptions)
                except ProofFailure:
                    raise Exception("Failed requirement: %s"%requirement)
                new_span_requirements.append(requirement)
                coord = _simplifiedCoord(dist_add(coord, entry_span), 
                                        assumptions, new_simp_requirements)
            else:
                coord = _simplifiedCoord(dist_add(coord, one), 
                                         assumptions, new_simp_requirements)
        # The last included 'coordinate' is one past the last
        # coordinate within the tuple range.  This value minus the base
        # is the length of the tuple, the number of elements it
        # conceptually contains.
        coords.append(coord)

                
        # Remember this result for next time in case the query is
        # repeated.
        coords_to_indices = {coord:i for i, coord in enumerate(coords)}
        coord_info = (base, assumptions, new_span_requirements, \
                      new_simp_requirements, coords, coords_to_indices)
        self._lastEntryCoordInfo = coord_info
        entry_span_requirements.extend(new_span_requirements)
        coord_simp_requirements.extend(new_simp_requirements)
        
        # Return the coordinate list.
        return coords
    
    def entryCoordToIndex(self, base, assumptions, requirements=None):
        '''
        Return a dictionary that maps simplified expressions for the 
        coordinates to respective integer indices of this ExprTuple.
        For each Iter entry, subsequent coordinates will account for 
        the extent of that Iter.  These simplified coordinate 
        expressions will be remembered and reused when a query is repeated.
        '''
        self.entryCoords(base, assumptions, requirements)
        return self._lastEntryCoordInfo[-1]
    
    def length(self, assumptions=USE_DEFAULTS):
        '''
        Return the proven length of this tuple as an Expression.  This
        length includes the extent of all contained iterations. 
        '''
        from proveit.iteration import Len
        return Len(self).simplification(assumptions).rhs
                
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, 
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        Flattens nested ExprTuples that arise from Embed substitutions.
        '''
        from .iteration import Iter
        self._checkRelabelMap(relabelMap)
        if len(exprMap)>0 and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        subbed_exprs = []
        for expr in self:
            subbed_expr = expr.substituted(exprMap, relabelMap, reservedVars, 
                                           assumptions, requirements)
            if isinstance(expr, Iter) and isinstance(subbed_expr, ExprTuple):
                # The iterated expression is being expanded 
                # and should be embedded into the list.
                for iter_expr in subbed_expr:
                    subbed_exprs.append(iter_expr)
            else:
                subbed_exprs.append(subbed_expr)
        return ExprTuple(*subbed_exprs)
        
    def merger(self, assumptions=USE_DEFAULTS):
        '''
        If this is an tuple of expressions that can be directly merged together
        into a single iteration, return this proven equivalence.  For example,
        {j \in Naturals, k-(j+1) \in Naturals} 
        |- (x_1, .., x_j, x_{j+1}, x_{j+2}, ..., x_k) = (x_1, ..., x_k)
        '''
        from proveit._core_.expression.lambda_expr import Lambda
        from proveit._core_.expression.composite.iteration import Iter
        from proveit.relation import TransRelUpdater
        from proveit.iteration._theorems_ import (merge, merge_front, merge_back,
                                                  merge_pair, merge_series)
        from proveit._common_ import f, i, j, k, l, x
        
        # A convenience to allow successive update to the equation via 
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        # Determine the position of the first Iter item and get the lambda map.
        first_iter_pos = len(self)
        lambda_map = None
        for _k, item in enumerate(self):
            if isinstance(item, Iter):
                lambda_map = Lambda(item.lambda_map.parameter, item.lambda_map.body)
                first_iter_pos = _k
                break
        
        if 1 < first_iter_pos:
            if lambda_map is None:
                raise NotImplementedError("Means of extracting a lambda map has not been implemented")
                pass # need the lambda map
            # Collapse singular items at the beginning.
            front_singles = ExprTuple(eq.expr[:first_iter_pos])
            i_sub = lambda_map.extractArgument(front_singles[0])
            j_sub = lambda_map.extractArgument(front_singles[-1])
            if len(front_singles)==2:
                # Merge a pair of singular items.
                front_merger = merge_pair.specialize({f:lambda_map, i:i_sub, j:j_sub}, 
                                                     assumptions=assumptions)
            else:
                # Merge a series of singular items in one shot.
                front_merger = merge_series.specialize({f:lambda_map, x:front_singles,
                                                        i:i_sub, j:j_sub}, 
                                                       assumptions=assumptions)
            eq.update(front_merger.substitution(self.innerExpr()[:first_iter_pos], 
                                                assumptions=assumptions))
            
        if len(eq.expr) == 1:
            # We have accomplished a merger down to one item.
            return eq.relation
        
        if len(eq.expr) == 2:
            # Merge a pair.
            if isinstance(eq.expr[0], Iter):
                if isinstance(eq.expr[1], Iter):
                    # Merge a pair of Iters.
                    item = eq.expr[1]
                    other_lambda_map = Lambda(item.lambda_map.parameter, 
                                              item.lambda_map.body)
                    if other_lambda_map != lambda_map:
                        raise ExprTupleError("Cannot merge together iterations "
                                             "with different lambda maps: %s vs %s"
                                             %(lambda_map, lambda_map_2nd))
                    iSub, jSub = eq.expr[0].start_index, eq.expr[0].end_index
                    kSub, lSub = eq.expr[1].start_index, eq.expr[1].end_index
                    merger = \
                        merge.specialize({f:lambda_map, i:iSub, j:jSub, k:kSub, 
                                          l:lSub}, assumptions=assumptions)
                else:
                    # Merge an Iter and a singular item.
                    iSub, jSub = eq.expr[0].start_index, eq.expr[0].end_index
                    kSub = lambda_map.extractArgument(eq.expr[1])
                    merger = \
                        merge_back.specialize({f:lambda_map, i:iSub, j:jSub,
                                               k:kSub}, assumptions=assumptions)                    
            else:
                # Merge a singular item and Iter.
                iSub = lambda_map.extractArgument(eq.expr[0])
                jSub, kSub = eq.expr[1].start_index, eq.expr[1].end_index
                merger = \
                    merge_front.specialize({f:lambda_map, i:iSub, j:jSub,
                                            k:kSub}, assumptions=assumptions)
            eq.update(merger)
            return eq.relation
        
        while len(eq.expr) > 1:
            front_merger = ExprTuple(eq.expr[:2]).merger(assumptions)
            eq.update(front_merger.substitution(self.innerExpr()[:2], 
                                                assumptions=assumptions))
    
    """
    TODO: change register_equivalence_method to allow and fascilitate these
    method stubs for purposes of generating useful documentation.
    
    def merged(self, assumptions=USE_DEFAULTS):
        '''
        Return the right-hand-side of a 'merger'.
        '''
        raise Exception("Should be implemented via InnerExpr.register_equivalence_method")
    
    def merge(self, assumptions=USE_DEFAULTS):
        '''
        As an InnerExpr method when the inner expression is an ExprTuple,
        return the expression with the inner expression replaced by its
        'merged' version.
        '''
        raise Exception("Implemented via InnerExpr.register_equivalence_method "
                        "only to be applied to an InnerExpr object.")
    """


class ExprTupleError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
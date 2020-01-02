from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.operation.operation import Operation
from proveit._core_.expression.composite.iteration import EmptyIterException
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
from proveit._core_.expression.label import Variable
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS

class Indexed(Expression):
    '''
    An Indexed Expression expresses a Variable,
    representing an ExprTuple or ExprArray, being indexed
    to yield an element.
    
    Upon substitution, it automatically performs the indexing
    if the indexed expression is a composite and the
    difference between the index and base is a known
    integer (or list of integers).
    '''
    
    def __init__(self, var, index_or_indices, base=1, styles=None, requirements=tuple()):
        from .composite import compositeExpression
        if not isinstance(var, Variable):
            raise TypeError("'var' being indexed should be a Variable, got %s"%str(var))
        self.indices = compositeExpression(index_or_indices)
        if len(self.indices) == 1:
            # has a single parameter
            self.index = self.indices[0]
            self.index_or_indices = self.index
        else:
            self.index_or_indices = self.indices
        if not isinstance(base, int):
            raise TypeError("'base' should be an integer")
        Expression.__init__(self, ['Indexed', str(base)], [var, self.index_or_indices], styles=styles, requirements=requirements)
        self.var = var
        self.base = base
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != Indexed: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 2 or coreInfo[0] != 'Indexed':
            raise ValueError("Expecting Indexed coreInfo to contain exactly two items: 'Indexed' and the integer 'base'")
        try:
            base = int(coreInfo[1])
        except:
            raise ValueError("Expecting 'base' to be an integer")
        return Indexed(*subExpressions, base=base).withStyles(**styles)       

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.var
        yield self.index_or_indices
        yield ('base', self.base)       
    
    def string(self, **kwargs):
        return self.var.string() + '_' + self.index_or_indices.string(fence=True)

    def latex(self, **kwargs):
        return self.var.latex() + '_{' + self.index_or_indices.latex(fence=False) + '}'

    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        If the indexed variable has been replaced with a Composite
        (ExprTuple or ExprArray), this should return the
        indexed element.  Only a Variable should be indexed via
        a Indexed expression; once the Variable is replaced with
        a Composite, the indexing should be actualized.
        '''
        from .composite import Composite
        from proveit.number import num, subtract, isLiteralInt
        from .expr_tuple import ExprTuple
        from .expr_array import ExprArray
        
        self._checkRelabelMap(relabelMap)
        
        new_requirements = []
        subbed_var = self.var.substituted(exprMap, relabelMap, reservedVars) # requirements not needed for variable substitution
        subbed_indices = self.indices.substituted(exprMap, relabelMap, reservedVars, assumptions=assumptions, requirements=new_requirements)
        
        result = None
        if isinstance(subbed_var, Composite):
            # The indexed expression is a composite.
            # Now see if the indices can be simplified to integers; if so,
            # we can attempt to extract the specific element.
            # If there is an IndexingError (i.e., we cannot get the element
            # because the Composite has an unexpanding Iter), 
            # default to returning the subbed Indexed.
            indices = subbed_indices
            if isinstance(subbed_var, ExprTuple):
                result = subbed_var.getElem(indices[0], base=self.base, assumptions=assumptions, requirements=new_requirements)
            elif isinstance(subbed_var, ExprArray):
                result = subbed_var.getElem(indices, base=self.base, assumptions=assumptions, requirements=new_requirements)
        
        for requirement in new_requirements:
            requirement._restrictionChecked(reservedVars) # make sure requirements don't use reserved variable in a nested scope        
        if requirements is not None:
            requirements += new_requirements # append new requirements
               
        # If the subbed_var has not been replaced with a Composite,
        # just return the Indexed operation with the substitutions made.
        if result is not None:
            return result
        else:
            return Indexed(subbed_var, subbed_indices, base=self.base)
        
    def _iterSubParamVals(self, axis, iterParam, startArg, endArg, 
                          exprMap, relabelMap=None, reservedVars=None, 
                          assumptions=USE_DEFAULTS, requirements=None):
        '''
        Consider a substitution over a containing iteration (Iter) 
        defined via exprMap, relabelMap, etc, and expand the iteration 
        by substituting the "iteration parameter" over the range from 
        the "starting argument" to the "ending argument" 
        (both inclusive as provided).
        
        When the Indexed variable is substituted with a Composite, any 
        containing Iteration is to be expanded over the iteration range.
        This method returns a list of parameter values that covers 
        occupied portions of the full range in a manner that keeps 
        different inner iterations separate.  In particular, the 
        iteration range is broken up for the different Iter entries that
        are contained in this Composite.  If it is not substituted with 
        a composite, _NoExpandedIteration is raised.
        
        Requirements that are passed back ensure that substituted composites are
        valid (with iterations that have natural number extents), that the 
        start and end indices are within range and at integer positions,
        and also includes equalities for employed simplifications or inversions
        (translating from index coordinates to parameters).
        '''
        from .composite import Composite, IndexingError, _simplifiedCoord, \
                                  _generateCoordOrderAssumptions
        from .expr_tuple import ExprTuple
        from .expr_array import ExprArray
        from proveit.logic import Equals, InSet
        from proveit.number import GreaterEq, LessEq, Add, one, num, \
                                      subtract, Naturals
        from proveit._core_.expression.expr import _NoExpandedIteration
        from .iteration import Iter, InvalidIterationError
        
        if requirements is None: requirements = [] 
        
        subbed_var = self.var.substituted(exprMap, relabelMap, reservedVars, 
                                          assumptions, requirements)
        index = self.indices[axis]
        subbed_index = index.substituted(exprMap, relabelMap, reservedVars, 
                                         assumptions, requirements)
        
        if not isinstance(subbed_var, Composite) or \
                iterParam not in subbed_index.freeVars():
            # No expansion for this parameter here:
            raise _NoExpandedIteration() # no expansionn

        # We cannot substitute in a Composite without doing an 
        # iteration over it.  Only certain iterations are allowed 
        # in this manner however.

        if subbed_index != iterParam:
            if not isinstance(subbed_index, Add):
                raise InvalidIterationError(subbed_index, iterParam)
            shift_terms = [term for term in subbed_index.operands
                            if term != iterParam]
            if len(shift_terms)==1:
                shift = shift_terms[0] # shift by a single term
            else:
                shift = Add(*shift_terms) # shift by multple terms
        
        start_index = subbed_index.substituted({iterParam:startArg})
        end_index = subbed_index.substituted({iterParam:endArg})
        entry_span_requirements = []
        coord_simp_requirements = []
        
        if isinstance(subbed_var, ExprTuple):
            coords = subbed_var.entryCoords(self.base, assumptions, 
                                            entry_span_requirements,
                                            coord_simp_requirements)
        else:
            if not isinstance(subbed_var, ExprArray):
                subbed_var_class_str = str(subbed_var.__class__)
                raise TypeError("Indexed variable should only be "
                                    "substituted with ExprTuple or "
                                    "ExprArray, not %s"%subbed_var_class_str)
            coords = subbed_var.entryCoords(self.base, axis, assumptions, 
                                            entry_span_requirements,
                                            coord_simp_requirements)
        assert coords[0]==num(self.base)
        coord_order_assumptions = list(_generateCoordOrderAssumptions(coords))
        #print("indexed sub coords", self, assumptions, start_index, coords, end_index)
        extended_assumptions = assumptions + coord_order_assumptions
        
        # We will include all of the "entry span" requirements
        # ensuring that the ExprTuple or ExprArray is valid
        # (the length of iterations is a natural number).
        # We will only include coordinate simplification
        # requirements up to the last needed coordinate.
        requirements.extend(entry_span_requirements)
                    
        # Find where the start index and end index belongs
        # relative to the entry coordinates.

        # The start is inclusive and is typically expected to 
        # toward the beginning of the coordinates.
        # Use the "last" insertion point for the start so we are not
        # including multiple equivalent parameter values at the 
        # start.
        start_pos = \
            LessEq.insertion_point(coords, start_index, 
                                    equiv_group_pos = 'last',
                                    assumptions=extended_assumptions)
        
        # The end position splits into two cases.  In the simple case,
        # it lands at a singular entry as the last entry.  Otherwise,
        # we need to add one to the endArg to ensure we get past any
        # iterations that may or may not be empty and find the
        # insertion point.
        end_pos = None
        if end_index in coords:
            # Might be the simple case of a singular entry as the last
            # entry.
            end_pos = coords.index(end_index)
            end_coord = coords[end_pos]
            if isinstance(end_coord, Iter):
                # Not the simple case -- an iteration rather than
                end_pos = None # a singular entry.
        if end_pos is None:
            # Not the simple case.  We need to add one to the endArg
            # to ensure we get past any iterations that may or may not
            # be empty.
            endArg = _simplifiedCoord(Add(endArg, one), assumptions,
                                      requirements)
            end_index = subbed_index.substituted({iterParam:endArg})
            # We would typically expect the end-index to come near the
            # end of the coordinates in which case it is more efficient
            # to search for the insertion point in reverse order, so use
            # Greater instead of Less.  
            # Use the "last" insertion point for the start so we are not
            # including multiple equivalent parameter values at the 
            # end.
            end_pos_from_end = \
                GreaterEq.insertion_point(list(reversed(coords)), end_index, 
                                          equiv_group_pos = 'last',
                                          assumptions=extended_assumptions)
            end_pos = len(coords)-end_pos_from_end
            
        # Check for a range out of bounds of the new composite.
        if start_pos==0:
            msg = ("ExprTuple index out of range: %s not proven "
                    "to be >= %s (the base) when assuming %s"
                    %(str(start_index), str(coords[0]), 
                        str(assumptions)))
            raise IndexError(msg)                
        if end_pos==len(coords)-1:
            msg = ("ExprTuple index out of range: %s not proven "
                    "to be < %s when assuming %s"
                    %(str(end_index), str(coords[-1]), 
                        str(assumptions)))
            raise IndexError(msg)
        
        # Check to see if the range is empty.
        if end_pos < start_pos:
            # Empty range (if valid at all).  Handle this
            # at the Iter.substituted level.
            raise EmptyIterException()
        
        # Include coordinate simplification requirements up to
        # the last used coordinate.
        coord_simp_req_map = {eq.rhs:eq for eq in coord_simp_requirements}
        for coord in coords[:end_pos+1]:
            if coord in coord_simp_req_map:
                requirements.append(coord_simp_req_map[coord])
        
        # End-point requirements may be needed.
        for coord_and_endpoint in [(coords[start_pos-1], start_index), 
                                        (end_index, coords[end_pos])]:
            if coord_and_endpoint[0]==coord_and_endpoint[1]:
                # When the endpoint index is the same as the
                # coordinate, we don't need to add a requirement.
                continue
            try:
                # See if we simply need to prove an equality between
                # the endpoint index and the coordinate.
                eq = Equals(*coord_and_endpoint)
                eq.prove(assumptions, automation=False)
                requirements.append(eq)
            except ProofFailure:
                # Otherwise, we must prove that the difference
                # between the coordinate and endpoint
                # is in the set of natural numbers (integral and
                # in the correct order).
                requirement = InSet(subtract(*reversed(coord_and_endpoint)), 
                                    Naturals)
                requirements.append(requirement.prove(assumptions))
                                    
        # We must put each coordinate in terms of iter parameter 
        # values (arguments) via inverting the subbed_index.
        def coord2param(coord):
            if subbed_index == iterParam:
                # Direct indexing that does not need to be inverted:
                return coord 
            # We must subtract by the 'shift' that the index
            # adds to the parameter in order to invert from
            # the coordinate back to the corresponding parameter:
            param = subtract(coord, shift)
            param = _simplifiedCoord(param, assumptions, requirements)
            return param
        
        coord_params = [coord2param(coord) for coord 
                        in coords[start_pos:end_pos]] 
        
        # If the start and end are the same expression or known to
        # be equal, just return [startArg].
        if startArg==endArg:
            return [startArg]
        try:
            eq = Equals(startArg, endArg)
            requirement = eq.prove(assumptions, automation=False)
            requirements.append(requirement)
            return [startArg]
        except ProofFailure:
            # Return the start, end, and coordinates at the
            # start of entries in between.
            return [startArg] + coord_params + [endArg]
        
        
    """  
    def iterated(self, iterParams, startIndices, endIndices, exprMap, relabelMap = None, reservedVars = None, assumptions=USE_DEFAULTS, requirements=None):
        from proveit.number import proven_sort, zero, one, num, Add, subtract, Greater
        
        subbed_var = self.indexed_expr.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)
        if isinstance(subbed_var, Composite):
            # We cannot substitute in a Composite without doing an iteration over it.
            # Only certain iterations are allowed in this manner however.
            
            if isinstance(subbed_var, ExprTenosr):
                tensor = subbed_var
                if len(iterParams) != len(self.indices):
                    raise IndexingError("Mismatch of ...")
                    
                for axis in xrange(tensor.ndims): # for each axis
                    if iterParams[axis] not in self.indices[axis]:
                        raise IndexingError("Mismatch of ...")
                    index_expr = self.indices[axis]
                    start_index = index_expr.substituted({iterParams[axis]:startIndices[axis]})
                    end_index = index_expr.substituted({iterParams[axis]:endIndices[axis]})
                    
                    sorted_coord_list = tensor.sortedCoordLists[axis]
                    coord_sorting_relation = proven_sort(sorted_coord_list + [start_index, end_index])
                    sorted_coords = list(coord_sorting_relation.operands)
                    
                
            
        else:
            yield self.substituted(exprMap, relabelMap, reservedVars, assumptions, requirements)

        
        
        if self.var in iterParams:
            raise IndexedError("It makes no sense to iterate over an Indexed's Variable.")
        if len(set(iterParams).intersection(self.indices.freeVars())) > 0:
            pass
        
        subbed_indexed_expr = 
        if isinstance(subbed_inde
    """

class IndexedError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

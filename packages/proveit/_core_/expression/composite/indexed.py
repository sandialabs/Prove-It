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
        from .composite import Composite, _simplifiedCoord
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
        
    def _iterSubParamVals(self, axis, iterParam, startArg, endArg, exprMap, 
                          relabelMap=None, reservedVars=None, 
                          assumptions=USE_DEFAULTS, requirements=None):
        '''
        Consider a substitution over a containing iteration (Iter) defined via exprMap, 
        relabelMap, etc, and expand the iteration by substituting the 
        "iteration parameter" over the range from the "starting argument" to the 
        "ending argument" (both inclusive).
        When the Indexed variable is substituted with a Composite, any containing 
        Iteration is to be expanded over the iteration range.  This method returns a list
        of parameter values that covers occupied portions of the full range in a manner 
        that keeps different inner iterations separate.  In particular, the iteration 
        range is broken up for the different Iter entries that are contained in this 
        Composite.  If it is not substituted with a composite, _NoExpandedIteration is
        raised.
        Requirements that are passed back ensure that substituted composites are
        valid (with iterations that have natural number extents), that the 
        start and end indices are within range and at integer positions,
        and also includes equalities for employed simplifications or inversions
        (translating from index coordinates to parameters).
        '''
        from .composite import Composite, IndexingError, _generateCoordOrderAssumptions
        from .expr_tuple import ExprTuple
        from .expr_array import ExprArray
        from proveit.logic import Equals
        from proveit.number import GreaterEq, LessEq, Add, one, InSet, subtract, Naturals
        from proveit._core_.expression.expr import _NoExpandedIteration
        from .iteration import IterationError
        
        if requirements is None: requirements = [] 
        
        subbed_var = self.var.substituted(exprMap, relabelMap, reservedVars, 
                                          assumptions, requirements)
        index = self.indices[axis]
        subbed_index = index.substituted(exprMap, relabelMap, reservedVars, 
                                         assumptions, requirements)
                
        if isinstance(subbed_var, Composite):
            # We cannot substitute in a Composite without doing an 
            # iteration over it.  Only certain iterations are allowed 
            # in this manner however.
            
            if iterParam not in subbed_index.freeVars():
                raise IndexingError("Iteration parameter not contained "
                                     "in the substituted index")
            start_index = subbed_index.substituted({iterParam:startArg})
            end_index = subbed_index.substituted({iterParam:endArg})
            
            if isinstance(subbed_var, ExprTuple):
                coords = subbed_var.entryCoords(self.base, assumptions, 
                                                requirements)
            else:
                if not isinstance(subbed_var, ExprArray):
                    subbed_var_class_str = str(subbed_var.__class__)
                    raise TypeError("Indexed variable should only be "
                                      "substituted with ExprTuple or "
                                      "ExprArray, not %s"%subbed_var_class_str)
                coords = subbed_var.entryCoords(self.base, axis, assumptions, 
                                                requirements)
            assert coords[0]==self.base
            coord_order_assumptions = list(_generateCoordOrderAssumptions(coords))
            #print("indexed sub coords", self, assumptions, start_index, coords, end_index)
            extended_assumptions = assumptions + coord_order_assumptions
            
            # Merge the start index (inclusive) and end index 
            # (exclusive) into the sorted coordinates so we can exclude 
            # anything outside of the appropriate [start, end) range.
            to_sort = [reversed(coords), [end_index]]
            # We would typically expect the end-index to come near the
            # end of the coordinates in which case it is more efficient
            # to merge sort in reverse order so use Greater instead of
            # Less.
            coords_plus_end_reversed = \
                GreaterEq.mergesort(to_sort, assumptions=extended_assumptions,
                                    skip_exact_reps=False,
                                    skip_equiv_reps=False)
            # Use LessEq because the start is inclusive and typically
            # expected to come before the coordinates.
            to_sort = [[start_index], reversed(coords_plus_end_reversed.operands)]
            coord_relations = LessEq.mergesort(to_sort, 
                                               assumptions=extended_assumptions,
                                               skip_exact_reps=False,
                                               skip_equiv_reps=False)
            #print("sorted", coord_relations)
            coord_rel_operands = list(coord_relations.operands) # copy, we may modify it.
            coord_rel_operators = coord_relations.operators
            
            # start_index and end_index are expressions indexing into the conceptual
            # tuple or array.  start_idx and end_idx are corresponding integer
            # indexes into coordinate relations of the entries.
            start_idx = coord_rel_operands.index(start_index)
            end_idx = coord_rel_operands.index(end_index)
            n_rel_operators = len(coord_rel_operators)
                        
            def swap_positions(lst, pos1, pos2): 
                lst[pos1], lst[pos2] = lst[pos2], lst[pos1] 
                return lst
    
            # Include the start and end "end-caps" but exclude
            # contained coordinates that are equal to either of these.
            # Also, if the start and end are the same, ensure that
            # they are placed at the same index (rightmost by this
            # convention).
            while start_idx < n_rel_operators \
                    and coord_rel_operators[start_idx]==Equals._operator_:
                # Swao the start index to the right with something equivalent.
                swap_positions(coord_rel_operands, start_idx, start_idx+1)
                start_idx += 1
            while end_idx < start_idx and \
                    coord_rel_operators[end_idx] == Equals._operator_:
                # Swap the end index to the right with something equivalent.
                swap_positions(coord_rel_operands, end_idx, end_idx+1)
                end_idx += 1
            while start_idx < end_idx and \
                    coord_rel_operators[end_idx-1] == Equals._operator_:
                # Swap the end index to the left with something equivalent.
                swap_positions(coord_rel_operands, end_idx-1, end_idx)
                end_idx -= 1
            
            assert coord_rel_operands[start_idx]==start_index
            assert coord_rel_operands[end_idx]==end_idx

            if end_idx < start_idx:
                # Empty range (if valid at all).  Handle this
                # at the Iter.substituted level.
                raise EmptyIterException()
                        
            # Check for a range out of bounds of the new composite.
            if start_idx==0:
                msg = ("ExprTuple index out of range: %s not proven "
                        "to be >= %s (the base) when assuming %s"
                        %(str(start_index), str(coords[0]), 
                            str(assumptions)))
                raise IndexError(msg)                
            elif end_idx==n_rel_operators:
                msg = ("ExprTuple index out of range: %s not proven "
                        "to be <= %s when assuming %s"
                        %(str(end_index), str(coords[-1]), 
                            str(assumptions)))
                raise IndexError(msg)
            
            # End-point requirements are needed.
            operation_class_dict = Operation.operationClassOfOperator
            #print(coord_relations, start_idx, end_idx-1)
            for idx in [start_idx-1] + [end_idx]:
                req_op = operation_class_dict[coord_rel_operators[idx]]
                operands = coord_rel_operands[idx:idx+2]
                assert len(operands)==2
                if req_op == Equals:
                    requirement = Equals(*operands)
                else:
                    requirement = InSet(subtract(*operands), Naturals)
                requirements.append(requirement.prove(assumptions))
            
            # We must put each coordinate in terms of iter parameter 
            # values (arguments) via inverting the subbed_index.
            def coord2param(coord):
                if coord==start_index: return startArg # Special known inversion.
                if coord==end_index: return endArg # Special known inversion.
                if subbed_index == iterParam:
                    # Direct indexing that does not need to be inverted:
                    return coord 
                # The indexing is not direct; for example, x_{f(p)}.
                # We need to invert f to obtain p from f(p)=coord and 
                # register the inversion as a requirement:
                # f(p) = coord.
                param = Equals.invert(Lambda(iterParam, subbed_index),
                                      coord, assumptions=assumptions)
                inversion = Equals(subbed_index.substituted({iterParam:param}), 
                                   coord)
                requirements.append(inversion.prove(assumptions=assumptions))
                return param
            
            result = [coord2param(coord) for coord 
                     in coord_rel_operands[start_idx:end_idx+1]] 
            return result
        
        raise _NoExpandedIteration() # no expansionn
        
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

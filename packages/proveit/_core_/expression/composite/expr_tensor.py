from composite import Composite
from expr_list import ExprList
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.defaults import defaults, USE_DEFAULTS
from iteration import Iter
import itertools
from ast import literal_eval
                

class ExprTensor(Composite, Expression): 
    '''
    An ExprTensor is a composite Expression representing
    an n-dimensional tensor.  It serves to map n-coordinate 
    "locations" to Expression elements.  The coordinates may 
    be general Expressions that are intended to represent 
    Integer numbers.
    
    The ExprTensor stores entries in terms of "relative
    element locations".  For each axis, all relevent coordinate 
    expressions are sorted into a sorting-relation expression 
    (for example, "a < b <= c = d < e", or some such form).  
    The index of these  operands serve as coordinates for 
    the "relative element locations".  We can translate from 
    one "location" representation to the other using the
    coordinate sorting relations.
    
    There may be Embed Expression elements for embedding
    a tensor within the tensor that may be substituted into
    the outer tensor.  When this happens, new coordinates may
    be added, generating new coordinate sorting relations.
    A specialization step that results in such a substitution
    will be conditioned upon the proof of any new coordinate
    sorting relations (these are extra conditions in addition
    to any explicit conditions of the universal quantifier(s)
    being specialized).
    
    Axioms involving an ExprTensor should properly be stated
    by way of an implication -- the statement involving
    the ExprTensor is the consequent that is only valid
    provided the coordinate sorting relations, in the
    antecedent, is true.  Corresponding theorems can then be
    proven by showing that the coordinate sorting relations
    are true (under the conditions of any universal quantifiers
    or other axioms).
    '''
    
    def __init__(self, tensor, shape=None, styles=dict(), assumptions=USE_DEFAULTS, requirements=tuple()):
        '''
        Create an ExprTensor either with a simple, dense tensor (list of lists ... of lists) or
        with a dictionary mapping coordinates (as tuples of expressions that represent integers) 
        to expr elements or Blocks.
        Providing starting and/or ending location(s) can extend the bounds of the tensor beyond
        the elements that are supplied.
        '''
        from composite import _simplifiedCoord
        from proveit._core_ import KnownTruth
        from proveit.number import Less, Greater, zero, one, num, Add, Subtract
        
        assumptions = defaults.checkedAssumptions(assumptions)
        requirements = []                
        if not isinstance(tensor, dict):
            tensor = {loc:element for loc, element in ExprTensor._tensorDictFromIterables(tensor, assumptions, requirements)}
                
        # Map direct compositions for the end-coordinate of Iter elements
        # to their simplified forms.
        self.endCoordSimplifications = dict()
                
        # generate the set of distinct coordinates for each dimension
        coord_sets = None # simplified versions
        full_tensor = dict()
        ndims = None
        if shape is not None:
            shape = ExprTensor.locAsExprs(shape)
            ndims = len(shape)
        for loc, element in tensor.iteritems():
            if isinstance(element, KnownTruth):
                element = element.expr # extract the Expression from the KnownTruth
            ndims = len(loc)
            if coord_sets is None:
                coord_sets = [set() for _ in range(ndims)]
            elif len(coord_sets) != ndims:
                if shape is not None:
                    raise ValueError("length of 'shape' is inconsistent with number of dimensions for ExprTensor locations")
                else:
                    raise ValueError("inconsistent number of dimensions for locations of the ExprTensor")
            for axis, coord in enumerate(list(loc)):
                if isinstance(coord, int):
                    coord = num(coord) # convert from Python int to an Expression
                    loc[axis] = coord
                coord_sets[axis].add(coord)
                if isinstance(element, Iter):
                    # Add (end-start)+1 of the Iter to get to the end
                    # location of the entry along this axis. 
                    orig_end_coord = Add(coord, Subtract(element.end_indices[axis], element.start_indices[axis]), one)
                    end_coord = _simplifiedCoord(orig_end_coord, assumptions, requirements)
                    self.endCoordSimplifications[orig_end_coord] = end_coord
                    coord_sets[axis].add(end_coord)
            full_tensor[tuple(loc)] = element

        if ndims is None:
            raise ExprTensorError("Empty ExprTensor is not allowed")
        if ndims <= 1:
            raise ExprTensorError("ExprTensor must be 2 or more dimensions (use an ExprList for something 1-dimensional")

        # in each dimension, coord_indices will be a dictionary
        # that maps each tensor location coordinate to its relative entry index.
        coord_rel_indices = []
        self.sortedCoordLists = []
        self.coordDiffRelationLists = []
        for axis in xrange(ndims): # for each axis
            # KnownTruth sorting relation for the simplified coordinates used along this axis
            # (something with a form like a < b <= c = d <= e, that sorts the tensor location coordinates): 
            coord_sorting_relation = Less.sort(coord_sets[axis], assumptions=assumptions)
            sorted_coords = list(coord_sorting_relation.operands)
            
            if shape is None:
                # Since nothing was explicitly specified, the shape is dictacted by extending
                # one beyond the last coordinate entry. 
                sorted_coords.append(Add(sorted_coords[-1], one))
            else:
                sorted_coords.append(shape[axis]) # append the coordinate for the explicitly specified shape
            if sorted_coords[0] != zero:
                sorted_coords.insert(0, zero) # make sure the first of the sorted coordinates is zero.
            
            self.sortedCoordLists.append(ExprList(sorted_coords))
            
            # Add in coordinate expressions that explicitly indicate the difference between coordinates.
            # These may be used in generating the latex form of the ExprTensor.
            diff_relations = []
            for c1, c2 in zip(sorted_coords[:-1], sorted_coords[1:]):
                diff = _simplifiedCoord(Subtract(c2, c1), assumptions, requirements)
                # get the relationship between the difference of successive coordinate and zero.
                diff_relation = Greater.sort([zero, diff], assumptions=assumptions)
                if isinstance(diff_relation, Greater):
                    if c2 == sorted_coords[-1] and shape is not None:
                        raise ExprTensorError("Coordinates extend beyond the specified shape in axis %d: %s after %s"%(axis, str(coord_sorting_relation.operands[-1]), str(shape[axis])))                        
                    assert tuple(diff_relation.operands) == (diff, zero), 'Inconsistent Less.sort results'
                    # diff > 0, let's compare it with one now
                    diff_relation = Greater.sort([one, diff], assumptions=assumptions)
                requirements.append(diff_relation)
                diff_relations.append(diff_relation)
            self.coordDiffRelationLists.append(ExprList(diff_relations))
                
            # map each coordinate expression to its index into the sorting_relation operands
            coord_rel_indices.append({coord:k for k, coord in enumerate(sorted_coords)})
            
        # convert from the full tensor with arbitrary expression coordinates to coordinates that are
        # mapped according to sorted relation enumerations.
        rel_index_tensor = dict()
        for loc, element in full_tensor.iteritems():
            rel_index_loc = (rel_index_map[coord] for coord, rel_index_map in zip(loc, coord_rel_indices))
            rel_index_tensor[rel_index_loc] = element
                
        sorted_keys = sorted(rel_index_tensor.keys())
        Expression.__init__(self, ['ExprTensor', str(ndims), ';'.join(str(key) for key in sorted_keys)], self.sortedCoordLists + self.coordDiffRelationLists + [rel_index_tensor[key] for key in sorted_keys], styles=styles, requirements=requirements)
        self.ndims = ndims
        self.relIndexTensor = rel_index_tensor
        
        # entryOrigins maps relative indices that contain tensor elements to
        # the relative indices of the origin for the corresponding entry.
        # Specifically, single-element entries map indices to themselves, but
        # multi-element Iter entries map each of the encompassed 
        # relative index location to the origin relative index location where
        # that Iter entry is stored.
        self.relEntryOrigins = self._makeEntryOrigins()
        
        # the last coordinates of the sorted coordinates along each eaxis define the shape:        
        self.shape = ExprList([sorted_coords[-1] for sorted_coords in self.sortedCoordLists])
    
    @staticmethod
    def locAsExprs(loc):
        from proveit.number import num
        loc_exprs = []
        for coord in loc:
            if isinstance(coord, int):
                coord = num(coord) # convert int to an Expression
            if not isinstance(coord, Expression):
                raise TypeError("location coordinates must be Expression objects (or 'int's to convert to Expressions)")
            loc_exprs.append(coord)
        return loc_exprs

    @staticmethod
    def _tensorDictFromIterables(tensor, assumptions, requirements):
        '''
        From nested lists of Expressions, create a tensor dictionary, 
        mapping multi-dimensional indices to Expression elements.
        Yields location, element pairs that define a tensor.
        '''
        from proveit._core_ import KnownTruth        
        from composite import _simplifiedCoord
        from proveit.number import zero, one, Add, Subtract
        try:
            coord = zero
            for entry in tensor:
                # simplify the coordinate before moving on
                # (the simplified form will be equated with the original in the
                # sorting relations of the ExprTensor).
                coord = _simplifiedCoord(coord, assumptions, requirements)
                if isinstance(entry, KnownTruth):
                    entry = entry.expr # extract the Expression from the KnownTruth
                if isinstance(entry, Expression):
                    loc = (coord,)
                    if isinstance(entry, Iter) and entry.ndims > 1:
                        loc += (zero,)*(entry.ndims-1) # append zeros for the extra dimensions
                    yield loc, entry # yield the location and element
                    if isinstance(entry, Iter):
                        # skip the coordinate ahead over the Embed expression
                        coord = Add(coord, Subtract(entry.end_indices[0], entry.start_indices[0]), one)
                    else:
                        coord = Add(coord, one) # shift the coordinate ahead by one
                else:
                    for sub_loc, entry in ExprTensor.TensorDictFromIterables(entry):
                        loc = (coord,)+sub_loc
                        yield loc, entry
        except TypeError:
            raise TypeError('An ExprTensor must be a dictionary of indices to elements or a nested iterables of Expressions')
    
    def _makeEntryOrigins(self):
        '''
        entryOrigins maps relative indices that contain tensor elements to
        the relative indices of the origin for the corresponding entry.
        Specifically, single-element entries map indices to themselves, but
        multi-element Iter entries map each of the encompassed 
        relative index location to the origin relative index location where
        that Iter entry is stored.
        
        Raise an ExprTensorError if there are overlapping entries.
        '''
        from iteration import Iter
        from proveit.number import Add, Subtract, one
        
        # Create the entry_origins dictionary and check for invalid
        # overlapping entries while we are at it.
        rel_entry_origins = dict()
        rel_index_tensor = self.relIndexTensor
        for rel_entry_loc, entry in rel_index_tensor.iteritems():
            if isinstance(entry, Iter):
                loc = self.tensorLoc(rel_entry_loc)
                
                # corner location at the end of the Embed block:
                end_corner = []
                for axis, coord in enumerate(loc):
                    end_coord = Add(coord, Subtract(entry.end_indices[axis], entry.start_indices[axis]), one)
                    end_corner.append(self.endCoordSimplifications[end_coord])
                
                # translate the end corner location to the corresponding relative indices
                rel_entry_end_corner = self.relEntryLoc(end_corner)
                
                # iterate over all of the relative indexed locations from the starting corner to 
                # the ending corner of the Iter block, populating the entry_origins dictionary and 
                # making sure none of the locations overlap with something else.
                for p in itertools.product(*[xrange(start, end) for start, end in zip(rel_entry_loc, rel_entry_end_corner)]):
                    p = tuple(p)
                    if p in rel_entry_origins:
                        raise ExprTensorError("Overlapping blocks in the ExprTensor")
                    rel_entry_origins[p] = rel_entry_loc
            else:
                # single-element entry.  check for overlap and add to the entry_origins dictionary
                if rel_entry_loc in rel_entry_origins:
                    raise ExprTensorError("Overlapping blocks in the ExprTensor")
                rel_entry_origins[rel_entry_loc] = rel_entry_loc
                
        # Return the entry_origins dictionary that we generated.
        return rel_entry_origins 
    
    def relEntryLoc(self, loc):
        '''
        Return the relative entry location given the absolute tensor location.
        '''
        return ExprTensor.relEntryLocation(loc, self.coordSortingRelations)

    def tensorLoc(self, rel_entry_loc):
        '''
        Return the absolute tensor location given the relative entry location.
        '''
        return ExprTensor.tensorLocation(rel_entry_loc, self.coordSortingRelations)
    
    @staticmethod
    def relEntryLocation(self, loc, coord_sorting_relations):
        '''
        Return the relative entry location given the absolute tensor location using 
        the given relations for sorting the absolute tensor coordinates.
        '''
        rel_entry_loc = (sorting_relation.operands.index(coord) for coord, sorting_relation in zip(loc, coord_sorting_relations))
        return rel_entry_loc
            
    @staticmethod
    def tensorLocation(self, rel_entry_loc, coord_sorting_relations):
        '''
        Return the absolute tensor location given the relative entry location using 
        the given relations for sorting the absolute tensor coordinates.
        '''
        loc = (sorting_relation.operands[index] for index, sorting_relation in zip(rel_entry_loc, coord_sorting_relations))
        return loc
                        
    def numEntries(self):
        '''
        Return the number of tensor entries.
        '''
        return len(self.relIndexTensor)
        
    def iteritems(self):
        '''
        Yield each relative entry location and corresponding element.
        '''
        return self.relIndexTensor.iteritems()

    def itervalues(self):
        '''
        Yield each tensor element.
        '''
        return self.relIndexTensor.itervalues()
    
    def keys(self):
        '''
        Returns the relative entry location keys
        '''
        return self.relIndexTensor.keys()
    
    def relEndCorner(self, rel_entry_loc):
        '''
        Given a relative location of one of the tensor entries,
        return the relative location for the "end-corner" of
        the entry.  If the entry is an Iter, then this
        relative end corner gives the relative range of the
        iteration inclusively.  Otherwise, the end-corner is
        simply rel_loc; that is, the start and the end are
        the same for single-element entries.
        '''
        # Translate from relative to absolute location, use
        # the endCorner method, then translate this result from
        # absolute to relative.
        return self.relEntryLoc(self.endCorner(self.tensorLoc(rel_entry_loc)))
    
    def endCorner(self, tensor_entry_loc):
        '''
        Given an absolute tensor entry location,
        return the absolute location for the "end-corner" of
        the entry.  If the entry is an Iter, then this
        absolute end corner gives the range of the
        iteration inclusively.  Otherwise, the end-corner is
        simply tensor_entry_loc; that is, the start and the 
        end are the same for single-element entries.
        '''
        from proveit.number import one, Add, Subtract
        from iteration import Iter
        entry = self[self.relEntryLoc(tensor_entry_loc)]
        if isinstance(entry, Iter):
            end_corner = []
            for axis, coord in enumerate(tensor_entry_loc):
                # Add (end-start)+1 of the Iter to get to the end
                # location of the entry along this axis. 
                orig_end_coord = Add(coord, Subtract(entry.end_indices[axis], entry.start_indices[axis]), one)
                end_corner.append(self.endCoordSimplifications[orig_end_coord]) # use the simplified version
            return end_corner # absolute end-corner for the tensor entry
        return tensor_entry_loc # single-element entry

    def __getitem__(self, rel_entry_loc):
        '''
        Return the tensor entry at the given relative
        entry location key.  See getElem(..) for
        getting the element at an absolute location.
        '''
        return self.relIndexTensor[rel_entry_loc]
    
    def getElem(self, tensor_loc, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Return the tensor element at the location, given
        as an Expression, using the given assumptions as needed
        to interpret the location expression.  Required
        truths, proven under the given assumptions, that 
        were used to make this interpretation will be
        appended to the given 'requirements' (if provided).
        '''
        from proveit.number import Less, Add, Subtract
        from iteration import Iter
        from composite import _simplifiedCoord
        if len(tensor_loc) != self.ndims:
            raise ExprTensorError("The 'tensor_loc' has the wrong number of dimensions: %d instead of %d"%(len(tensor_loc), self.ndims))
        
        if requirements is None: requirements = [] # requirements won't be passed back in this case

        lower_indices = []
        upper_indices = []
        for coord, sorted_coords in zip(tensor_loc, self.sortedCoordLists):
            lower, upper = None, None
            try:
                lower, upper = Less.insert(sorted_coords, coord, assumptions=assumptions)
            except:
                raise ExprTensorError("Could not determine the 'tensor_loc' range within the tensor coordinates under the given assumptions")
            # The relationship to the lower and upper coordinate bounds are requirements for determining
            # the element being assessed.
            requirements.append(Less.sort((sorted_coords[lower], coord), reorder=False, assumptions=assumptions))
            requirements.append(Less.sort((coord, sorted_coords[upper]), reorder=False, assumptions=assumptions))
            lower_indices.append(lower)
            upper_indices.append(upper)
        
        if tuple(lower_indices) not in self.entryOrigins or tuple(upper_indices) not in self.entryOrigins:
            raise ExprTensorError("Tensor element could not be found at %s"%str(tensor_loc))
        rel_entry_origin = self.relEntryOrigins[lower_indices]
        if self.relEntryOrigins[upper_indices] != rel_entry_origin:
            raise ExprTensorError("Tensor element is ambiguous for %s under the given assumptions"%str(tensor_loc))
        
        entry = self[rel_entry_origin]
        if isinstance(entry, Iter):
            # indexing into an iteration
            entry_origin = self.tensorLoc(rel_entry_origin)
            iter_start_indices = entry.start_indices
            iter_loc = [Add(iter_start, Subtract(coord, origin)) for iter_start, coord, origin in zip(iter_start_indices, tensor_loc, entry_origin)] 
            simplified_iter_loc = [_simplifiedCoord(coord, assumptions, requirements) for coord in iter_loc]
            return entry.getInstance(simplified_iter_loc, assumptions=assumptions, requirements=requirements)
        else:
            # just a single-element entry
            assert lower_indices==upper_indices, "A single-element entry should not have been determined if there was an ambiguous range for 'tensor_loc'"
            return entry
        
    def yieldLocationDeltas(self, axis):
        '''
        For the given axis, yield the difference between each
        successive coordinate at which an element is explicitly
        located for this tensor (or where an Embed block ends).
        '''
        from proveit.number import zero, Add
        from proveit.logic import Equals
        prev_coord = zero
        for coord in self.sorting_relations[axis]:
            if not Equals(prev_coord, coord).prove(assumptions=[self.sorting_relations[axis]], automation=False):
                assert isinstance(coord, Add) and len(coord.operands)==2 and coord.operands[0]==prev_coord, "The first of a set of equal coordinates in the sorting relations are supposed to indicate the difference from the previous one."
                yield coord.operands[1] # this term is the difference between this coordinate and the simplified form of the previous one
            prev_coord = coord
    


    """
    def yieldRequirements(self):
        '''
        Yield KnownTruth's that are prerequisites for this
        Expression.
        '''
        for sub_req in Expression.yieldRequirements(self):
            yield sub_req
        for sorting_relations in self.sorting_relations:
            yield sorting_relations
    """
            
    def remakeArguments(self):
        '''
        Yield the argument (key, value) pairs that could be used to 
        recreate the ExprTensor.
        '''
        tensor = {loc:element for loc, element in self.iteritems()}
        yield tensor
                                    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != ExprTensor: 
            MakeNotImplemented(subClass) 
        if len(coreInfo) != 3:
            raise ValueError("Expecting ExprTensor coreInfo to contain exactly 3 items: 'ExprTensor', the number of dimensions, and the indexed locations")
        if coreInfo[0] != 'ExprTensor':
            raise ValueError("Expecting ExprTensor coreInfo[0] to be 'ExprTensor'")
        ndims = literal_eval(coreInfo[1])
        indexed_loc_strs = coreInfo[2].split(';')
        # coordinate-sorting relations in each dimension
        sorting_relations = subExpressions[:ndims]
        indexed_tensor = {literal_eval(indexed_loc_str):element for indexed_loc_str, element in zip(indexed_loc_strs, subExpressions[ndims+1:])}
        tensor = {ExprTensor.tensorLocation(indexed_loc, sorting_relations):element for indexed_loc, element in indexed_tensor.iteritems()}
        return ExprTensor(tensor).withStyles(**styles)
                                                                              
    def string(self, fence=False):
        return '{' + ', '.join(loc.string(fence=True) + ':' + element.string(fence=True) for loc, element in self.iteritems()) + '}'
    
    def _config_latex_tool(self, lt):
        Expression._config_latex_tool(self, lt)
        if not 'xy' in lt.packages:
            lt.packages.append('xy')
        if r'\newcommand{\exprtensorelem}' not in lt.preamble:
            lt.preamble += r'\newcommand{\exprtensorelem}[1]{*+<1em,.9em>{\hphantom{#1}} \POS [0,0]="i",[0,0].[0,0]="e",!C *{#1},"e"+UR;"e"+UL **\dir{-};"e"+DL **\dir{-};"e"+DR **\dir{-};"e"+UR **\dir{-}, "i"}' + '\n'
        if r'\newcommand{\exprtensorblock}' not in lt.preamble:
            lt.preamble += r'\newcommand{\exprtensorblock}[3]{\POS [0,0]="i",[0,0].[#1,#2]="e",!C *{#3},"e"+UR;"e"+UL **\dir{-};"e"+DL **\dir{-};"e"+DR **\dir{-};"e"+UR **\dir{-}, "i"}' + '\n'
        if r'\newcommand{\exprtensorghost}' not in lt.preamble:
            lt.preamble += r'\newcommand{\exprtensorghost}[1]{*+<1em,.9em>{\hphantom{#1}}}' + '\n'        
    
    def latex(self, fence=False):
        from proveit._core_.expression.bundle import Block
        if len(self.shape) != 2:
            raise NotImplementedError('Only 2-dimensional ExprTensor formatting has been implemented.')
        _, ncolumns = self.shape
        outStr = r'\xymatrix @*=<0em> @C=1em @R=.7em{' + '\n'
        current_row = -1
        current_col = -1
        # first add arrows at the top for all column alignment indices
        for c in xrange(-1, ncolumns):
            if c in self.alignmentCoordinates[1]:
                outStr += ' \ar @{->} [0,1]'
            outStr += ' & '
        outStr += r'\\'
        isAlignmentRow = 0 in self.alignmentCoordinates[0]
        # next add the populated elements
        for (r, c) in self.keys():
            element = self[(r, c)]
            blockAlignmentStr = ''
            if isAlignmentRow and current_col == -1:
                outStr += ' \ar @{<-} [0,1]'                
            if r > current_row:
                if isAlignmentRow:
                    # add an arrow for the alignment index on the right side
                    while ncolumns > current_col: 
                        outStr += ' & '
                        current_col += 1
                    outStr += ' \ar @{<-} [0,-1]'
                outStr += r' \\' + '\n'
                current_row += 1
                isAlignmentRow = current_row in self.alignmentCoordinates[0]
                current_col = -1
            while c > current_col:
                outStr += ' & '
                current_col += 1
            if isinstance(element, Block):
                block = element
                outStr += r'\exprtensorblock{' + str(block.shape[0] - 1) + '}{' + str(block.shape[1] - 1) + '}'
            elif isinstance(element, _ExpresisonTensorBlockGhost):
                outStr += r'\exprtensorghost'
                block = element.ghosted_block
                block_r, block_c = element.block_coord
                # Add arrow(s) to indicate alignment coordinates "into" a block
                if block_r == 0 and block_c in block.alignmentCoordinates[1]:
                    blockAlignmentStr += r' \ar @{<-} [0,-1]'
                elif block_r == block.shape[0]-1 and block_c in block.alignmentCoordinates[1]:
                    blockAlignmentStr += r' \ar @{<-} [0,1]'
                if block_c == 0 and block_r in block.alignmentCoordinates[0]:
                    blockAlignmentStr = r' \ar @{<-} [-1,0]'
                elif block_c == block.shape[1]-1 and block_c in block.alignmentCoordinates[0]:
                    blockAlignmentStr = r' \ar @{<-} [1,0]'
            else:                
                outStr += r'\exprtensorelem'
            outStr += '{' + element.latex(fence=True) + '}' + blockAlignmentStr
        # finally add arrows at the bottom for all column alignment indices
        for c in xrange(-1, ncolumns):
            if c in self.alignmentCoordinates[1]:
                outStr += ' \ar @{->} [0,-1]'
            outStr += ' & '
        outStr += r'\\'

        outStr += '\n}\n'
        return outStr
    
    def entryRanges(self, base, start_indices, end_indices, assumptions, requirements):
        '''
        For each entry of the tensor that is fully or partially contained in the window defined
        via start_indices and end_indices (as Expressions that can be provably sorted
        against tensor coordinates), yield the start and end of the intersection of the
        entry range and the window.
        '''
        
        from proveit.number import Less, Greater
        if requirements is None: requirements = [] # requirements won't be passed back in this case
                                
        # For each axis, obtain the sorted coordinates of the substituted tensor,
        # insert the start and end indices for the desired range, and determine
        # the starting and ending locations relative to operator positions of the 
        # expanded sorting relations.
        coord_sorting_relations = [] # expanded sorting relations (including start and end indices) along each axis
        rel_start_loc = [] # start location relative to the new sorting locations along each axis
        rel_end_loc = [] # end location relative to the new sorting locations along each axis
        for axis in xrange(self.ndims): # for each axis
            start_index =start_indices[axis]
            end_index = end_indices[axis]
            
            sorted_coords = self.sortedCoordLists[axis]
            # insert the start_index and the end_index into the sorted list of coordinates in their proper places
            coord_sorting_relation = Less.sort(sorted_coords + [start_index, end_index], assumptions=assumptions)
            # get the relative start and end integer coordinates
            rel_start_loc.append(coord_sorting_relation.operands.index(start_index))
            rel_end_loc.append(coord_sorting_relation.operands.index(end_index))
            # remember these sorting relations
            coord_sorting_relations.append(coord_sorting_relation)
        
        # For each entry of the substituted tensor, determine if it is within the start/end
        # "window".  If so, yield the intersected range in terms of parameter values
        # (inverted from the tensor coordinates).  Keep track of the requirements.
        for rel_loc_in_tensor, entry in self.iteritems():
            # convert from the relative location within the tensor to the
            # tensor location in absolute coordinates.
            entry_start = self.tensorLoc(rel_loc_in_tensor)
            entry_end = self.endCorner(rel_loc_in_tensor)
            
            # convert from the absolute tensor location to the relative
            # location w.r.t. the  coord_sorting_relations that include
            # the startArgs and endArgs of the window.
            rel_entry_start = [coord_sorting_relation.index(coord) for coord, coord_sorting_relation in zip(entry_start, coord_sorting_relations)]
            rel_entry_end = [coord_sorting_relation.index(coord) for coord, coord_sorting_relation in zip(entry_end, coord_sorting_relations)]
            
            # get the intersection of the entry range and the considered window,
            rel_intersection_start = [max(a, b) for a, b in zip(rel_start_loc, rel_entry_start)]
            rel_intersection_end = [min(a, b) for a, b in zip(rel_end_loc, rel_entry_end)]
            
            # translate the intersection region to absolute coordinates
            intersection_start = [coord_sorting_relation.operands[i] for i, coord_sorting_relation in zip(rel_intersection_start, coord_sorting_relations)]
            intersection_end = [coord_sorting_relation.operands[i] for i, coord_sorting_relation in zip(rel_intersection_end, coord_sorting_relations)]
                                
            if any(a > b for a, b in zip(rel_intersection_start, rel_intersection_end)):
                # empty intersection, but we need to include requirements that prove this.
                for axis, (a, b) in enumerate(zip(rel_intersection_start, rel_intersection_end)):
                    if a > b:
                        # add the requirements showing the intersection is empty along the first such axis.
                        coord_sorting_relation =  coord_sorting_relations[axis]
                        aCoord, bCoord = coord_sorting_relation.operands[a], coord_sorting_relation.operands[b]
                        empty_intersection_relation = Greater.sort([aCoord, bCoord], assumptions=assumptions)
                        requirements.append(empty_intersection_relation)
            else:
                # There is a non-empty intersection rectangle to yield for a particular entry.
                
                # Let's get the requirements that prove the intersection:
                for axis, (a, b, c, d, e, f) in enumerate(zip(rel_intersection_start, rel_intersection_end, rel_start_loc, rel_entry_start, rel_end_loc, rel_entry_end)):
                    # add the requirements that determine the intersection along this axis.
                    for j, k in ((a, b), (c, d), (e, f)):
                        coord_sorting_relation =  coord_sorting_relations[axis]
                        jCoord, kCoord = coord_sorting_relation.operands[j], coord_sorting_relation.operands[k]
                        empty_intersection_relation = Less.sort([jCoord, kCoord], assumptions=assumptions)
                        requirements.append(empty_intersection_relation)
                yield (intersection_start, intersection_end)        
        
    
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        Flattens nested tensors (or lists of lists) that arise from Embed substitutions.
        '''
        from composite import _simplifiedCoord
        from iteration import Iter
        from proveit.number import Add
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)

        if requirements is None: requirements = [] # requirements won't be passed back in this case

        tensor = dict()
        for loc, element in self.iteritems():
            subbed_loc = loc.substituted(exprMap, relabelMap, reservedVars, assumptions=assumptions, requirements=requirements)
            subbed_elem = element.substituted(exprMap, relabelMap, reservedVars, assumptions=assumptions, requirements=requirements)
            if isinstance(element, Iter) and isinstance(subbed_elem, ExprTensor):
                # An iteration element became an ExprTensor upon substitution,
                # so insert the elements directly into this outer ExprTensor.
                for sub_loc, sub_elem in subbed_elem.iteritems():
                    net_loc = [_simplifiedCoord(Add(main_coord, sub_coord), assumptions, requirements) for main_coord, sub_coord in zip(subbed_loc, sub_loc)]
                    tensor[net_loc] = subbed_elem
            else:
                tensor[subbed_loc] = subbed_elem
        expr_tensor = ExprTensor(tensor, assumptions)
        for requirement in expr_tensor.requirements:
            # check that all ExprTensor requirements satisfy restrictions
            requirement._restrictionChecked(reservedVars) # make sure requirements don't use reserved variable in a nested scope
        
        # pass back the new requirements that are different from the ExprTensor requirements after making substitutions.
        old_requirements = {requirement.substituted(exprMap, relabelMap, reservedVars) for requirement in self.requirements}
        new_requirements = [requirement for requirement in expr_tensor.requirements if requirement not in old_requirements]
            
        requirements += new_requirements
        
        return expr_tensor
                           
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*([expr.usedVars for expr in self.sorting_relations] + [expr.usedVars() for expr in self.values()]))
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*([expr.freeVars for expr in self.sorting_relations] + [expr.freeVars() for expr in self.values()]))

class ExprTensorError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

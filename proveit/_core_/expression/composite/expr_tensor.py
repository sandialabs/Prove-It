'''
compositeExpression.py

The internal logic of Prove-It knows about a few special types of expr classes
that contain multiple Expressions: NamedExpressions, exprlist, and ExpressionTensor.
An NamedExpressions maps string identifiers to Expressions.  An exprlist is a linear
list of Expressions with special substitution rules regarding Bundle elements.
When an exprlist is substituted for a Bundle expr, its elements will be 
absorbed into the parent exprlist.  An ExpressionTensor maps lists of integers
to expr elements or Block Bundles and has special substitution rules regarding Blocks.
When an ExpressionTensor is substituted for a Block expr, its elements (or blocks)
will be absorbed into the parent ExpressionTensor.
'''

from composite import Composite, NestedCompositeExpressionError
from expr_list import ExpressionList
from proveit._core_.expression.expr import Expression, MakeNotImplemented
import itertools
from ast import literal_eval
                

"""
class ExpandableExpression(MultiExpression):
    '''
    The base class for exprlist and ExpressionTensor.
    These may be expanded when a MultiVariable is being substituted.
    '''
    def __init__(self, coreInfo, subExpressions):
        expr.__init__(self, coreInfo, subExpressions)
        freeMultiVars = set().union([subExpression.freeMultiVars() for subExpression in subExpressions])
        if len(freeMultiVars) > 1:
            raise ValueError("Multiple free MultiVariables is unsupported due to ambiguity")
        elif len(freeMultiVars) == 1:
            self.freeMultiVar = freeMultiVars[0]
        self.freeMultiVar = None            
    
    def substitutedElement(self, element, exprMap, operationMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap/operationMap and/or relabeled according to relabelMap.
        If the substituted bundledExpr is of the multiExprType, it will be extracted 
        from the Bundle wrapping and incorporated into the multi-expr which contains it.
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        if self.freeMultiVar is not None and (self.freeMultiVar in exprMap or self.freeMultiVar in operationMap or self.freeMultiVar in relabelMap):
            # performing a multi-variable expansion substitution
            multiVar = self.freeMultiVar
            subExprMap, subOperationMap, subRelabelMap = exprMap, operationMap, relabelMap
            inOperationMap = multiVar in operationMap
            if multiVar in exprMap:
                subExprMap = subMultiVarMap = dict(exprMap)
            elif inOperationMap:
                subOperationMap = subMultiVarMap = dict(operationMap)
            elif multiVar in relabelMap:
                subRelabelMap = subMultiVarMap = dict(relabelMap)
            else:
                assert False, "shouldn't happen"
            multiVarSub = subMultiVarMap[multiVar]
            if inOperationMap:
                bundleOpArgs = subMultiVarMap.arguments
                multiVarSub = subMultiVarMap.expression
            def substituteForElem(subElem):
                if inOperationMap:
                    subMultiVarMap[multiVar] = Lambda(bundleOpArgs, subElem)
                else:
                    subMultiVarMap[multiVar] = subElem
                return self.bundledExpr.substituted(subExprMap, subOperationMap, subRelabelMap, reservedVars)
            if isinstance(multiVarSub, list):
                # exprlist bundle expansion
                return [substituteForElem(subElem) for subElem in multiVarSub]
            elif isinstance(multiVarSub, dict):
                # ExpressionTensor bundle expansion
                return {key:substituteForElem(subElem) for key, subElem in multiVarSub}
        # default when not performing a multi-variable expansion substitution
        return self.element.substituted(exprMap, operationMap, relabelMap, reservedVars)
"""
    
class _ExpresisonTensorBlockGhost:
    '''
    An ExpressionTensorGhost is just a placeholder in an ExpressionTensor that covers
    the region of a Block beyond its origin corner, referencing the Block in question.
    '''
    def __init__(self, ghosted_block, block_coord):
        self.ghosted_block = ghosted_block
        self.block_coord = block_coord
    
class ExpressionTensor(Composite, Expression, dict): 
    '''
    An expr tensor is a composite expr represented as a dictionary mapping coordinates
    (as tuples of integers) to expr elements or Blocks.  Blocks have an extent greater
    than or equal to one in each tensor dimension.  It may be a sparse tensor but must not
    have overlapping blocks.  In addition to this dictionary, each axis of the tensor 
    has a set of alignment coordinates that define how the tensor would be incorporated into 
    another ExpressionTensor when is its substituting a Block element (alignment coordinates 
    of the ExressionTensor must line up in correspondence to those of the Block).
    '''
    def __init__(self, tensor, shape=None, alignmentCoordinates=None):
        '''
        Create an ExpressionTensor either with a simple, dense tensor (list of lists ... of lists) or
        with a dictionary mapping coordinates (as tuples of integers) to expr elements or Blocks.
        Providing a shape can extend the bounds of the tensor beyond the elements that are supplied.
        Providing alignmentCoordinates establishes how this Tensor may be incorporated into another
        tensor when substituting a Block element.
        '''
        from proveit.core.expression.bundle.etcetera import Etcetera
        from proveit.core.expression.bundle.block import Block
        dict.__init__(self)
        if not isinstance(tensor, dict):
            tensor, _ = ExpressionTensor.TensorDictFromIterables(tensor)

        # Establish the shape and check for restriction violations:
        self.shape = shape
        fixed_shape = (shape is not None)
        # Build the ExpressionTensor dictionary, checking for coordinate, shape, or type errors
        for coord, element in tensor.iteritems():
            for i in coord:
                if not isinstance(i, int) or i < 0:
                    raise ExpressionTensorIndexError('ExpressionTensor indices must be an iterable set of non-negative integers')
            if self.shape is None:
                self.shape = [0]*len(coord)
            elif len(coord) != len(self.shape):
                if fixed_shape:
                    raise ExpressionTensorShapeError('ExpressionTensor indices must have the same dimensionality as the specified shape')
                else:
                    raise ExpressionTensorShapeError('ExpressionTensor indices must have consistent dimensionality')
            if fixed_shape:
                if any(coord[axis] >= self.shape[axis] for axis in xrange(len(coord))):
                    raise ExpressionTensorShapeError('ExpressionTensor coordinate out the specified shape bounds')
            else:
                for k, i in enumerate(coord):
                    self.shape[k] = max(self.shape[k], i+1)
            if not isinstance(element, Expression):
                raise TypeError('Each ExpressionTensor element must be an expr')
            if isinstance(element, ExpressionTensor):
                raise NestedCompositeExpressionError('May not nest ExpressionTensors (do you need to use Block? or wrap with an Operation?)')
            if isinstance(element, ExpressionList):
                raise TypeError('May not nest an exprlist in an ExpressionTensors (do you need to wrap with an Operation?)')
            if isinstance(element, Etcetera):
                raise TypeError('An Etcetera may be contained in an exprlist but not an ExpressionTensor')
            self[coord] = element
        self.shape = tuple(self.shape)
        # Check for overlap errors and add appropriate _ExpressionTensorGhost elements
        # that cover the regions of any Blocks.
        for start_coord, element in self.iteritems():
            if isinstance(element, Block):
                block = element
                if len(block.shape) != len(self.shape):
                    raise ExpressionTensorShapeError("Block, with shape " + str(block.shape) + ", does not have the same dimensionality as the Tensor, with shape " + str(self.shape))
                for block_coord in itertools.product([xrange(block_axis_extent) for block_axis_extent in block.shape]):
                    if sum(block_coord) == 0: continue # skip the origin where the Block is placed
                    coord = [start+shift for start, shift in zip(start_coord, block_coord)]
                    if coord in self.keys():
                        raise ExpressionTensorOverlapError("ExpressionTensor Block overlaps another element")
                    self[coord] = _ExpresisonTensorBlockGhost(block, block_coord)
        sortedNonGhostKeys = [key for key in sorted(self.keys()) if not isinstance(self[key], _ExpresisonTensorBlockGhost)]
        Expression.__init__(self, ['ExpressionTensor', str(self.shape), ';'.join(str(key) for key in sortedNonGhostKeys), [self[key] for key in sortedNonGhostKeys]])

    @staticmethod
    def TensorDictFromIterables(tensor, pre_coord=tuple()):
        '''
        From nested lists of Expressions, create a tensor dictionary, 
        mapping multi-dimensional indices to expr elements.
        Returns a (tensor-dictionary, shape) tuple.
        '''
        try:
            sub_tensors = []
            sub_shapes = []
            for i, element in enumerate(tensor):
                if isinstance(element, Expression):
                    sub_shapes.append(tuple())
                else:
                    sub_tensor, sub_shape = ExpressionTensor.TensorDictFromIterables(element, pre_coord+(i,))
                    sub_tensors.append(sub_tensor)
                    sub_shapes.append(sub_shape)
            if len(sub_shapes) == 0:
                raise ExpressionTensorShapeError('An ExpressionTensor may not have zero extent in any dimension')
            if all(sub_shape == sub_shapes[0] for sub_shape in sub_shapes) and len(sub_shapes[0]) > 0:
                # consistent sub-tensor shapes -- take as higher dimensional tensor
                shape = tuple((len(tensor),) + sub_shapes[0])
                tensor_dict = {tuple(pre_coord+(i,)+sub_coord):element for i, sub_tensor in enumerate(sub_tensors) for sub_coord, element in sub_tensor.iteritems()}
                return tensor_dict, shape
            else:
                # 1-D tensor 
                return {(i,):element for i, element in enumerate(tensor)}, (len(tensor),)
        except TypeError:
            raise TypeError('An ExpressionTensor must be a dictionary of indices to elements or a nested iterables of Expressions')

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != ExpressionTensor: 
            MakeNotImplemented(subClass) 
        if len(coreInfo) != 3:
            raise ValueError("Expecting ExpressionTensor coreInfo to contain excactly 3 items: 'ExpressionTensor', the shape, and the keys")
        if coreInfo[0] != 'ExpressionTensor':
            raise ValueError("Expecting ExpressionTensor coreInfo[0] to be 'ExpressionTensor'")
        shape = literal_eval(coreInfo[1])
        keyStrs = coreInfo[2].split(';')
        tensorDict = {literal_eval(keyStr):subExpression for keyStr, subExpression in zip(keyStrs, subExpressions)}
        return ExpressionTensor(tensorDict, shape)
                   
    def string(self, fence=False):
        return '{' + ', '.join(str(key) + ':' + self[key].string(fence=True) for key in sorted(self.keys())) + '}'
    
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
        from proveit.core.expression.bundle import Block
        if len(self.shape) != 2:
            raise NotImplementedError('One 2-dimensional ExpressionTensor formatting has been implemented.')
        _, ncolumns = self.shape
        outStr = r'\xymatrix @*=<0em> @C=1em @R=.7em{' + '\n'
        current_row = -1
        current_col = -1
        # first add arrows at the top for all column alignment indices
        for c in xrange(-1, ncolumns):
            if c in self.alignmentIndices[1]:
                outStr += ' \ar @{->} [0,1]'
            outStr += ' & '
        outStr += r'\\'
        isAlignmentRow = 0 in self.alignmentIndices[0]
        # next add the populated elements
        for (r, c) in sorted(self.keys()):
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
                isAlignmentRow = current_row in self.alignmentIndices[0]
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
                if block_r == 0 and block_c in block.alignmentIndices[1]:
                    blockAlignmentStr += r' \ar @{<-} [0,-1]'
                elif block_r == block.shape[0]-1 and block_c in block.alignmentIndices[1]:
                    blockAlignmentStr += r' \ar @{<-} [0,1]'
                if block_c == 0 and block_r in block.alignmentIndices[0]:
                    blockAlignmentStr = r' \ar @{<-} [-1,0]'
                elif block_c == block.shape[1]-1 and block_c in block.alignmentIndices[0]:
                    blockAlignmentStr = r' \ar @{<-} [1,0]'
            else:                
                outStr += r'\exprtensorelem'
            outStr += '{' + element.latex(fence=True) + '}' + blockAlignmentStr
        # finally add arrows at the bottom for all column alignment indices
        for c in xrange(-1, ncolumns):
            if c in self.alignmentIndices[1]:
                outStr += ' \ar @{->} [0,-1]'
            outStr += ' & '
        outStr += r'\\'

        outStr += '\n}\n'
        return outStr 
    
    def _makeAlignmentMappings(self, outerShape, outerAlignmentCoordinates, innerShape, innerAlignmentCoordinates):
        '''
        Return a space requirement function and coordinate mapping when substituting
        a tensor with the given innerAlignmentCoordinates into a block with the given
        outerAlignmentCoordinates.
        '''
        ndimensions = len(self.shape)
        if len(outerAlignmentCoordinates) != ndimensions:
            raise ValueError('There must be outer alignment indices for each dimension')
        if len(innerAlignmentCoordinates) != ndimensions:
            raise ValueError('There must be inner alignment indices for each dimension')
        if len(outerShape) != ndimensions:
            raise ValueError('Block shape dimensions must match the dimensions of the containing tensor')

        # for each axis, map each inner coordinate to the outer coordinate of the block
        coordinateMaps = [dict() for _ in xrange(ndimensions)]
        # determine the space required for each outer coordinate along each axis
        spaceRequirements = [[[1] for _ in xrange(outerShape[axis])] for axis in xrange(ndimensions)]
        # for each axis
        for axis in ndimensions:
            if len(outerAlignmentCoordinates[axis]) != len(innerAlignmentCoordinates[axis]):
                raise ValueError('inner and outer alignment coordinate count must match')
            i = 0 # the inner coordinate that we are mapping to an outer coordinate
            innerBegin = 0
            outerBegin = outerAlignmentCoordinates[axis][0] - innerAlignmentCoordinates[axis][0]
            extraSpace = 0
            # for each alignment coordinate
            for k in xrange(len(innerAlignmentCoordinates[axis])):
                outerEnd = extraSpace + outerAlignmentCoordinates[axis][k] - 1
                innerEnd = innerAlignmentCoordinates[axis][k] - 1
                innerDelta = (innerEnd - innerBegin)
                outerDelta = (outerEnd - outerBegin)
                if innerDelta > outerDelta :
                    # more space is need to fit the inner substitution into the outer block
                    extraSpace = innerDelta - outerDelta
                    # distribute this extra space evenly but padding earler coordinates with an extra
                    # one as needed if the extra space does not divide evenly
                    minExtraSpacePerCoord = extraSpace / outerDelta
                    for j in xrange(outerBegin, outerEnd+1):
                        spaceRequirements[axis][j - extraSpace] += minExtraSpacePerCoord
                    for j in xrange(outerBegin, innerBegin + extraSpace - minExtraSpacePerCoord*outerDelta):
                        spaceRequirements[axis][j - extraSpace] += 1
                    outerEnd += extraSpace
                    outerDelta += extraSpace
                while i <= innerEnd:
                    # interpolate between alignment indices
                    coordinateMaps[axis][i] = outerBegin + (i - innerBegin) * outerDelta / innerDelta 
                    ++i
                outerBegin = outerEnd + 1
                innerBegin = innerAlignmentCoordinates[axis][k]
            # finish off the coordinate mapping beyond the last alignment coordinates.
            j = outerBegin
            while i < innerShape[axis]:
                coordinateMaps[axis][i] = j
                ++i, ++j
        
        def coordinateMap(innerIndex):
            return [coordinateMaps[axis][innerIndex[axis]] for axis in xrange(ndimensions)]

        return spaceRequirements, coordinateMap
                        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        '''
        from proveit.core.expression.bundle.block import Block
        
        # Check to see if the entire ExpressionTensor is to be substituted
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)

        ndimensions = len(self.shape)
        
        # Perform the element-by-element substitutions and establish
        # the space requirements for each coordinate along each axis
        # due to the expansion of any Block elements, consistent with
        # alignment indices.
        virtualTensor = dict() # maps original indices and block offsets to substituted elements
        spaceRequirements = [{i:1 for i in xrange(self.shape[axis])} for axis in xrange(ndimensions)]
        for coord, element in self.iteritems():
            subbedElement = element.substituted(exprMap, relabelMap, reservedVars)
            if isinstance(element, Block) and isinstance(subbedElement, ExpressionTensor):
                subbedTensor = subbedElement
                if len(self.shape) != len(subbedTensor.shape):
                    raise ExpressionTensorSubstitutionError("Block substitution must have the same dimensionality as the parent ExpressionTensor")
                specificSpaceReqs, coordinateMap = self._makeAlignmentMappings(element.shape, element.alignmentCoordinates, subbedTensor.shape, subbedTensor.alignmentCoordinates)
                for axis in range(len(element.shape)):
                    for i in xrange(element.shape[axis]):
                        spaceRequirements[axis][i] = max(spaceRequirements[axis][i], specificSpaceReqs[axis][i])
                for subbedTensorIdx, subbedTensorElement in subbedTensor.iteritems():
                    virtualTensor[(coord, coordinateMap(subbedTensorIdx))] = subbedTensorElement
            else:
                virtualTensor[(coord,[0]*len(self.shape))] = subbedElement                
        # Map from original indices, in each dimension, to the new indices
        # in order to make room for expanded blocks.
        coordinateMappings = [[0] for axis in xrange(ndimensions)]
        for axis in xrange(ndimensions):
            coordinateMapping = coordinateMappings[axis]
            spaceReq = spaceRequirements[axis]
            for spaceReqIndex in sorted(spaceReq.keys()):
                while len(coordinateMapping) < spaceReqIndex:
                    # space of 1 by default
                    coordinateMapping.append(coordinateMapping[-1]+1) 
                coordinateMapping.append(coordinateMapping[spaceReqIndex] + spaceReq[spaceReqIndex])

        # Create the new tensor based upon the initSubbedTensor,
        # the initial tensor with substitutions, and the coordinate mappings.
        subbedTensor = dict()
        for (virtualIdx, offset), element in virtualTensor.iteritems():
            coord = tuple([coordinateMapping[coordinate] for coordinate, coordinateMapping in zip(virtualIdx, coordinateMappings)])
            subbedTensor[[coord[axis] + offset[axis] for axis in xrange(len(self.shape))]] = element
            
        # Now we are ready to create the new ExpressionTensor
        return ExpressionTensor(subbedTensor)
        
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.values()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.values()])

    def freeMultiVars(self):
        '''
        Returns the union of the free MultiVariables of the sub-Expressions.
        '''
        return set().union(*[expr.freeMultiVars() for expr in self.values()])

class ExpressionTensorIndexError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
    
class ExpressionTensorShapeError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
    
class ExpressionTensorReshapingError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

class ExpressionTensorOverlapError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
    
class ExpressionTensorSubstitutionError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
from bundle import Bundle
from etcetera import Etcetera
from proveit._core_.expression.expr import MakeNotImplemented
from proveit._core_.expression.composite import ExpressionTensor
from ast import literal_eval

class Block(Bundle):
    def __init__(self, expr, shape, alignmentCoordinates=None):
        '''
        Alignment indices
        '''
        if alignmentCoordinates is None:
            # by default, each block-relative coordinate within the Block's shape is an alignment coordinate
            alignmentCoordinates = [list(range(k)) for k in shape]
        if len(shape) != alignmentCoordinates:
            raise ValueError("alignmentCoordinates have the wrong dimensionality for the Block")
        for extent in shape:
            if not isinstance(extent, int):
                raise ValueError("shape must be a list/tuple of integers")
        for indices in alignmentCoordinates:
            for idx in indices:
                if not isinstance(extent, idx):
                    raise ValueError("alignmentCoordinates be a list of integer lists")            
        self.shape = shape
        self.alignmentCoordinates = alignmentCoordinates
        extraCoreInfo = [';'.join(str(extent) for extent in self.shape)]
        for indices in alignmentCoordinates:
            extraCoreInfo += [';'.join(str(idx) for idx in indices)]
        # the alignmentCoordinates are the extra coreInfo
        Bundle.__init__(self, ExpressionTensor, expr, lambda expr : Block(expr), extraCoreInfo)

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != Etcetera: 
            MakeNotImplemented(subClass) 
        if coreInfo[0] != 'Block':
            raise ValueError("Expecting 'Block' to be the first coreInfo element of a Block")        
        if len(coreInfo) < 2:
            raise ValueError("coreInfo of the Block is missing the 'shape' information")
        shape = [literal_eval(extent) for extent in coreInfo[1].split(';')]
        dimensions = len(shape)
        if len(coreInfo) != 2+dimensions:
            raise ValueError("coreInfo of the Block should have 2+dimensions elements to contain 'Block', the shape, and alignment indices for each dimension")
        alignmentCoordinates = []
        for k in xrange(dimensions):
            alignmentCoordinates.append([literal_eval(idx) for idx in coreInfo[2+k].split(';')])
        if len(subExpressions) != 1:
            raise ValueError("Expecting exactly one sub-expression to make a Block")
        return Block(subExpressions[0], shape, alignmentCoordinates)  

    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Etcetera expression.
        '''
        defaultAlignmentCoords = [list(range(k)) for k in self.shape]
        yield self.subExpr(0)
        yield self.shape
        if self.alignmentCoordinates != defaultAlignmentCoords:
            yield self.alignmentCoordinates

    def string(self, **kwargs):
        return '[[' + self.bundledExpr.string(fence=False) + ']]'
    
    def latex(self, **kwargs):
        return '\left[\left[' + self.bundledExpr.latex(fence=False) + '\right]\right]'

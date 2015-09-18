'''
multiExpression.py

The internal logic of Prove-It knows about a few special types of Expression classes
that contain multiple Expressions: NamedExpressions, ExpressionList, and ExpressionTensor.
An NamedExpressions maps string identifiers to Expressions.  An ExpressionList is a linear
list of Expressions with special substitution rules regarding Etcetera list elements.
When an ExpressionList is substituted for an Etcetera Expression, its elements will be 
absorbed into the parent ExpressionList.  An ExpressionTensor maps lists of integers
to Expression elements or Blocks and has special substitution rules regarding Blocks.
When an ExpressionTensor is substituted for a Block Expression, its elements (or blocks)
will be absorbed into the parent ExpressionTensor.
'''

from proveit.expression import Expression, Variable, Operation, Lambda, STRING, LATEX
from _elementtree import SubElement

class MultiExpression(Expression):
    """
    The base class for NamedExpressions, ExpressionList, ExpressionTensor, and Bundle.
    """
    def __init__(self, coreInfo, subExpressions):
        Expression.__init__(self, coreInfo, subExpressions)
        
class NamedExpressions(MultiExpression, dict):
    """
    An NamedExpressions is a composite Expression that maps strings to Expressions.
    """
    def __init__(self, expr_dict):
        dict.__init__(self, expr_dict)
        for key, val in expr_dict.iteritems():
            if not isinstance(key, str): 
                raise TypeError("Keywords of an expression dictionary may only be strings")
            if not isinstance(val, Expression): 
                raise TypeError("Values of an expression dictionary must be Expressions")
        MultiExpression.__init__(self, 'NamedExpressions ' + ','.join(sorted(self.keys())), [self[key] for key in sorted(self.keys())])

    def formatted(self, formatType, fence=False):
        return '{' + ', '.join(key + ':' + self[key].formatted(formatType, fence=True) for key in sorted(self.keys())) + '}'
    
    def substituted(self, exprMap, operationMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap/operationMap and/or relabeled according to relabelMap.
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return NamedExpressions({key:expr.substituted(exprMap, operationMap, relabelMap, reservedVars) for key, expr in self.iteritems()})

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

    def freeUnbundledVars(self):
        """
        Returns the union of the free unbundled Variables of the sub-Expressions.
        """
        return set().union(*[expr.freeUnbundledVars() for expr in self.values()])
    
class ExpressionList(MultiExpression, list):
    """
    An ExpressionList is a composite Expression composed of an ordered list of member
    Expressions.  An ExpressionList is may not be nested.  Use of Etcetera can allow
    substitutions that are absorbed into the containing ExpressionList.  For example
    ExpressionList(x, Etcetera(y)) can become ExpressionList(x, y, z) by doing
    a substition of y to ExpressionList(y, z).
    """
    def __init__(self, *expressions):
        '''
        Initialize an ExpressionList from one or more Expression arguments.
        '''
        list.__init__(self)
        if len(expressions) == 1 and not isinstance(expressions[0], Expression): 
            expressions = expressions[0] # allowed to pass in a single list argument
        for expr in expressions:
            if isinstance(expr, ExpressionList):
                raise NestedMultiExpressionError('May not nest ExpressionLists (do you need to use Etcetera? or ExpressionTensor?)')
            if not isinstance(expr, Expression):
                raise TypeError('ExpressionList must be created out of Expressions)')
            #if isinstance(expr, Block):
            #    raise TypeError('A Block expression may only be used in an ExpressionTensor (you may use an Etcetera Operation in an ExpressionList)')
            self.append(expr)
        self.shape = (len(self),)
        MultiExpression.__init__(self, 'ExpressionList', self)
    
    def formatted(self, formatType, fence=True):
        outStr = ''
        if len(self) == 0: fence = True # for an empty list, show the parenthesis to show something.
        if formatType == STRING or formatType == LATEX:
            if fence: outStr += '('
            outStr += ', '.join([expr.formatted(formatType) for expr in self])
            if fence: outStr += ')'
        return outStr
    
    def substituted(self, exprMap, operationMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap/operationMap and/or relabeled according to relabelMap.
        Flattens nested ExpressionLists that arise from Etcetera substitutions.
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        def subbedGen():
            for expr in self:
                subbed_expr = expr.substituted(exprMap, operationMap, relabelMap, reservedVars)
                if isinstance(expr, Etcetera):
                    # expand the Etcetera substitution              
                    for etc_expr in subbed_expr if isinstance(subbed_expr, ExpressionList) else [subbed_expr]:
                        yield etc_expr
                else: yield subbed_expr # yield an individual ExpressionList element
        return ExpressionList(*list(subbedGen()))
        
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

    def freeUnbundledVars(self):
        '''
        Returns the union of the free unbundled Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeUnbundledVars() for expr in self])

class ExpressionTensor(MultiExpression, dict): 
    '''
    An Expression tensor is a composite Expression represented as a dictionary mapping indices
    (as tuples of integers) to Expression elements or blocks.  It can be a sparse tensor but
    must not have overlapping blocks.
    '''
    def __init__(self, tensor, shape=None):
        '''
        Create an ExpressionTensor either with a simple, dense tensor (list of lists ... of lists) or
        with a dictionary mapping indices (as tuples of integers) to Expression elements or blocks.
        '''
        dict.__init__(self)
        if not isinstance(tensor, dict):
            tensor, _ = ExpressionTensor.TensorDictFromIterables(tensor)

        # Establish the shape and check for restriction violations:
        self.shape = shape
        fixed_shape = (shape is not None)
        print tensor, shape
        for idx, element in tensor.iteritems():
            for i in idx:
                if not isinstance(i, int) or i < 0:
                    raise ExpressionTensorIndexError('ExpressionTensor indices must be an iterable set of non-negative integers')                
            if self.shape is None:
                self.shape = [0]*len(idx)
            elif len(idx) != len(self.shape):
                if fixed_shape:
                    raise ExpressionTensorShapeError('ExpressionTensor indices must have the same dimensionality as the specified shape')
                else:
                    raise ExpressionTensorShapeError('ExpressionTensor indices must have consistent dimensionality')
            if fixed_shape:
                if any(idx[d] >= self.shape[d] for d in xrange(len(idx))):
                    raise ExpressionTensorShapeError('ExpressionTensor index out the specified shape bounds')
            else:
                for k, i in enumerate(idx):
                    self.shape[k] = max(self.shape[k], i+1)
            if not isinstance(element, Expression):
                raise TypeError('Each ExpressionTensor element must be an Expression')                
            if isinstance(element, ExpressionTensor):
                raise NestedMultiExpressionError('May not nest ExpressionTensors (do you need to use Block? or wrap with an Operation?)')
            self[idx] = element
        self.shape = tuple(self.shape)
        
        MultiExpression.__init__(self, 'ExpressionTensor ' + ','.join(str(key) for key in sorted(self.keys())), [self[key] for key in sorted(self.keys())])        

    @staticmethod
    def TensorDictFromIterables(tensor, pre_idx=tuple()):
        '''
        From nested lists of Expressions, create a tensor dictionary, 
        mapping multi-dimensional indices to Expression elements.
        Returns a (tensor-dictionary, shape) tuple.
        '''
        try:
            sub_tensors = []
            sub_shapes = []
            for i, element in enumerate(tensor):
                if isinstance(element, Expression):
                    sub_shapes.append(tuple())
                else:
                    sub_tensor, sub_shape = ExpressionTensor.TensorDictFromIterables(element, pre_idx+(i,))
                    sub_tensors.append(sub_tensor)
                    sub_shapes.append(sub_shape)
            if len(sub_shapes) == 0:
                raise ExpressionTensorShapeError('An ExpressionTensor may not have zero extent in any dimension')
            if all(sub_shape == sub_shapes[0] for sub_shape in sub_shapes) and len(sub_shapes[0]) > 0:
                # consistent sub-tensor shapes -- take as higher dimensional tensor
                shape = tuple((len(tensor),) + sub_shapes[0])
                tensor_dict = {tuple(pre_idx+(i,)+sub_idx):element for i, sub_tensor in enumerate(sub_tensors) for sub_idx, element in sub_tensor.iteritems()}
                return tensor_dict, shape
            else:
                # 1-D tensor 
                return {(i,):element for i, element in enumerate(tensor)}, (len(tensor),)
        except TypeError:
            raise TypeError('An ExpressionTensor must be a dictionary of indices to elements or a nested iterables of Expressions')

        
                

    """           
    def _regularize(self):
        # For each nested tensor in the hierarchy, track its extent 
        # in each dimension according to its shape.
        ndims = len(self.shape)
        print "regularizing: ", self
        extents_by_dim = [[set() for _ in xrange(self.shape[d])] for d in xrange(ndims)]
        for idx, element in self.iteritems():
            if isinstance(element, ExpressionTensor):
                if len(element.shape) != len(self.shape):
                    raise ExpressionTensorShapeError('Dimension of sub-tensor inconsistent with top-level tensor')
                sub_shape = element.shape
            elif isinstance(element, Block):
                sub_shape = ('B', 'B', 'B') # Use 'B' as a special Block extent (flexible)
            else: sub_shape = (1, 1, 1)
            for d in xrange(ndims):
                extents_by_dim[d][idx[d]].add(sub_shape[d])
        '''
        # There may only be one extent besides 'B' (Block) in each extent set
        # for a regularizable tensor.
        for d in xrange(ndims):
            for i in xrange(self.shape[d]):
                if len(extents_by_dim[d][i] - {'B'}) > 1:
                    raise ExpressionTensorShapeError('Ambiguous tensor blocks: nested tensors must have the same extent in a line along an axis')
        '''
        # If there is no unity or 'B' (Block) in any particular extent set, 
        # the corresponding nested tensor may be promoted up in the hierarchy,
        # shifting down indices at the higher level.
        index_remap = [[i for i in xrange(self.shape[d]+1)] for d in xrange(ndims)]
        for d in xrange(ndims):
            new_i = 0
            for i in xrange(self.shape[d]):
                index_remap[d][i] = new_i
                extents = extents_by_dim[d][i]
                if len(extents) == 1 and (1 not in extents) and ('B' not in extents):
                    new_i += next(iter(extents))
                else: new_i += 1
            index_remap[d][self.shape[d]] = new_i
        new_shape = [index_remap[d][-1] for d in xrange(ndims)]
        if self.shape == new_shape:
            return # No change -- in the original shape
        # Make appropriate promotions/regularization up the ranks.
        orig_iteritems = list(self.iteritems()) # wrapping in list will copy the original
        self.clear()
        self.shape = new_shape
        for idx, element in orig_iteritems:
            new_idx = tuple(index_remap[d][idx[d]] for d in xrange(ndims))
            if isinstance(element, ExpressionTensor):
                for sub_idx, sub_element in element.iteritems():
                    top_idx = list(new_idx)
                    sub_idx = list(sub_idx)
                    full_promotion = True
                    for d in xrange(ndims):
                        if index_remap[d][idx[d]+1]-index_remap[d][idx[d]] > 1:
                            top_idx[d] += sub_idx[d]
                            sub_idx[d] = 0
                        else:
                            full_promotion = False
                    top_idx, sub_idx = tuple(top_idx), tuple(sub_idx)
                    if full_promotion:
                        self[top_idx] = sub_element
                    else:
                        if top_idx not in self:
                            self[top_idx] = dict()
                        self[top_idx][sub_idx] = sub_element
            else:
                self[new_idx] = element
        # Transform any new sub-tensors created as dictionaries into ExpressionTensors
        for idx, element in self.iteritems():
            if isinstance(element, dict):
                if len(element) == 1: self[idx] = element[(0, 0)]
                else: self[idx] = ExpressionTensor(element)
    """
                
    def formatted(self, formatType, fence=False):
        if formatType == LATEX and len(self.shape) == 2:
            _, ncolumns = self.shape
            outStr = r'\begin{array}{' + ''.join(['c']*ncolumns) + '}\n'
            current_row = 0
            current_col = 0
            for (r, c) in sorted(self.keys()):
                element = self[(r, c)]
                if r > current_row:
                    outStr += r' \\' + '\n'
                    current_row += 1
                    current_col = 0
                while c > current_col:
                    outStr += ' & '
                    current_col += 1
                outStr += element.formatted(formatType, fence=True)
            outStr += '\n' + r'\end{array}' + '\n'
            return outStr            
        else:
            return '{' + ', '.join(str(key) + ':' + self[key].formatted(formatType, fence=True) for key in sorted(self.keys())) + '}'
        
    def substituted(self, exprMap, operationMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap/operationMap and/or relabeled according to relabelMap.
        '''
        
        # Check to see if the entire ExpressionTensor is to be substituted
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)

        ndimensions = len(self.shape)
        
        # Perform the element-by-element substitutions and establish
        # the space requirements for each index in each dimension
        # due to expansion of Block elements.
        initSubbedTensor = dict()
        spaceRequirements = [dict() for d in xrange(ndimensions)]
        for idx, element in self.iteritems():
            subbedElement = element.substituted(exprMap, operationMap, relabelMap, reservedVars)
            if isinstance(element, Block) and isinstance(subbedElement, ExpressionTensor):
                if len(self.shape) != len(subbedElement.shape):
                    raise Exception("Block substitution must have the same dimensionality as the parent ExpressionTensor")
                subShape = subbedElement.shape
                print "subshape: ", idx, subShape
            else: subShape = [1]*len(self.shape)
            # the shape of the element determines minimum space requirements
            for d in range(len(self.shape)):
                idx_d = idx[d]
                if idx_d in spaceRequirements[d]:
                    spaceRequirements[d][idx_d] = max(spaceRequirements[d][idx_d], subShape[d])
                else:
                    spaceRequirements[d][idx_d] = subShape[d]
            initSubbedTensor[idx] = subbedElement
                
        # Map from original indices, in each dimension, to the new indices
        # in order to make room for expanded blocks.
        indexMappings = [[0] for d in xrange(ndimensions)]
        for d in xrange(ndimensions):
            indexMapping = indexMappings[d]
            spaceReq = spaceRequirements[d]
            for spaceReqIndex in sorted(spaceReq.keys()):
                while len(indexMapping) < spaceReqIndex:
                    # space of 1 by default
                    indexMapping.append(indexMapping[-1]+1) 
                indexMapping.append(indexMapping[spaceReqIndex] + spaceReq[spaceReqIndex])

        # Create the new tensor based upon the initSubbedTensor,
        # the initial tensor with substitutions, and the index mappings.
        subbedTensor = dict()
        for initIdx in initSubbedTensor.keys():
            idx = tuple([indexMapping[index] for index, indexMapping in zip(initIdx, indexMappings)])
            if isinstance(initSubbedTensor[initIdx], ExpressionTensor):
                for subIdx in initSubbedTensor[initIdx].keys():
                    subbedTensor[tuple([index+subIndex for index, subIndex in zip(idx, subIdx)])] = initSubbedTensor[initIdx][subIdx]
            else: subbedTensor[idx] = initSubbedTensor[initIdx]
            
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

    def freeUnbundledVars(self):
        '''
        Returns the union of the free unbundled Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeUnbundledVars() for expr in self.values()])


class Bundle(MultiExpression):
    def __init__(self, multiExprType, bundledExpr, maker):
        assert multiExprType == ExpressionList or multiExprType == ExpressionTensor, "Unrecognized multi-Expression type for Bundle"
        self.multiExprType = multiExprType
        self.bundledExpr = bundledExpr
        if not isinstance(self.bundledExpr, Expression):
            raise TypeError("The 'bundled' expression should be an Expression")
        self.maker = maker
        MultiExpression.__init__(self, 'Bundle ' + str(multiExprType), [self.bundledExpr])

    def substituted(self, exprMap, operationMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap/operationMap and/or relabeled according to relabelMap.
        If the substituted bundledExpr is of the multiExprType, it will be extracted 
        from the Bundle wrapping and incorporated into the multi-Expression which contains it.
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        unbundledInnerVars = self.bundledExpr.freeUnbundledVars()
        bundleVarCandidates = [var for var in unbundledInnerVars if (var in exprMap and isinstance(exprMap[var], self.multiExprType)) or
                               (var in operationMap and isinstance(operationMap[var], Lambda) and isinstance(operationMap[var].expression, self.multiExprType)) or
                                (var in relabelMap and isinstance(relabelMap[var], self.multiExprType))]
        if len(bundleVarCandidates) > 1:
            raise Exception("Multiple Bundle variable expansion is unsupported due to ambiguity")
        if len(bundleVarCandidates) == 1:
            # performing a bundle expansion substitution
            bundleVar = bundleVarCandidates[0]
            subExprMap, subOperationMap, subRelabelMap = exprMap, operationMap, relabelMap
            inOperationMap = bundleVar in operationMap
            if bundleVar in exprMap:
                subExprMap = subBundleVarMap = dict(exprMap)
            elif inOperationMap:
                subOperationMap = subBundleVarMap = dict(operationMap)
            elif bundleVar in relabelMap:
                subRelabelMap = subBundleVarMap = dict(relabelMap)
            else:
                assert False, "shouldn't happen"
            bundleVarSub = subBundleVarMap[bundleVar]
            if inOperationMap:
                bundleOpArgs = bundleVarSub.arguments
                bundleVarSub = bundleVarSub.expression
            def substituteForElem(subElem):
                if inOperationMap:
                    subBundleVarMap[bundleVar] = Lambda(bundleOpArgs, subElem)
                else:
                    subBundleVarMap[bundleVar] = subElem
                return self.bundledExpr.substituted(subExprMap, subOperationMap, subRelabelMap, reservedVars)
            if self.multiExprType == ExpressionList:
                # ExpressionList bundle expansion
                return ExpressionList(substituteForElem(subElem) for subElem in bundleVarSub)
            elif self.multiExprType == ExpressionTensor:
                # ExpressionTensor bundle expansion
                return ExpressionTensor({key:substituteForElem(subElem) for key, subElem in bundleVarSub})
        # default when not performing a bundle expansion substitution
        return self.maker(self.bundledExpr.substituted(exprMap, operationMap, relabelMap, reservedVars))

    def usedVars(self):
        '''
        Returns the union of the used Variables of the bundledExpr.
        '''
        return self.bundledExpr.usedVars()
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the bundledExpr.
        '''
        return self.bundledExpr.freeVars()

    def freeUnbundledVars(self):
        '''
        No unbundled variables within a bundle.
        '''
        return set()
    

def isBundledVar(expr):
    # Is the expression a Bundled Variable (Variable wrapped in Bundle)?
    return isinstance(expr, Bundle) and isinstance(expr.bundledExpr, Variable)

def isBundledVarOrVar(expr):
    # Is the expression either a Variable a Bundled Variable (Variable wrapped in Bundle)?
    return isinstance(expr, Variable) or isBundledVar(expr)

def extractVar(expr):
    # Return expr if it is a Variable, extract the Variable out of a Bundled Variable
    # if it is one, or return None.
    return expr.bundledExpr if isBundledVar(expr) else (expr if isinstance(expr, Variable) else None)

def isBundledOperation(expr):
    # Is the expression a Bundled Ooperation (Operation wrapped in Bundle)?
    return isinstance(expr, Etcetera) and isinstance(expr.bundledExpr, Operation)
        
class Etcetera(Bundle):
    def __init__(self, expr):
        Bundle.__init__(self, ExpressionList, expr, lambda expr : Etcetera(expr))
    
    def formatted(self, formatType, fence=False):
        # override this default as desired
        if formatType == STRING or formatType == LATEX:
            return '..' + self.bundledExpr.formatted(formatType, fence=True) + '..'
    
class Block(Bundle):
    def __init__(self, expr):
        Bundle.__init__(self, ExpressionTensor, expr, lambda expr : Block(expr))

    def formatted(self, formatType, fence=True):
        # override this default as desired
        innerFormatted = self.bundledExpr.formatted(formatType, fence=False)
        if formatType == STRING:
            return '[[' + innerFormatted + ']]'
        elif formatType == LATEX:
            return r'\left[\left[' + innerFormatted + r'\right]\right]'

def multiExpression(expressions):
    '''
    Put the appropriate multi-Expression wrapper around expressions.  
    Dictionaries with string keys will be wrapped in an NamedExpressions.  
    Other dictionaries will be wrapped in an ExpressionTensor.  
    A single Expression or iterable over only Expressions will be wrapped 
    in an ExpressionList.
    '''
    if isinstance(expressions, ExpressionList) or isinstance(expressions, NamedExpressions) or isinstance(expressions, ExpressionTensor):
        return expressions # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        return ExpressionList(expressions) # a single expression that we will wrap in an ExpressionLIst
    elif isinstance(expressions, dict) and len(expressions.keys()) > 0 and isinstance(expressions.keys()[0], str):
        # A dictionary must be an NamedExpressions
        return NamedExpressions(expressions)
    else:
        if all(isinstance(subExpr, Expression) for subExpr in expressions):
            # An iterable over only Expressions must be an ExpressionList
            return ExpressionList(*expressions)
        else:
            # Assume to be a tensor as a list of lists
            return ExpressionTensor(expressions)

def singleOrMultiExpression(exprOrExprs):
    '''
    Put the approriate multi-Expression wrapper around a list (iterable) or dictionary
    of Expressions, or simply return the given Expression if it is one.
    '''
    if isinstance(exprOrExprs, Expression):
        return exprOrExprs
    else: return multiExpression(exprOrExprs)

class NestedMultiExpressionError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

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

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

from proveit.expression import Expression, Variable, Operation, STRING, LATEX
import itertools

class MultiExpression(Expression):
    """
    The base class for NamedExpressions, ExpressionList, ExpressionTensor, and Bundle.
    """
    def __init__(self):
        Expression.__init__(self)
        
class NamedExpressions(MultiExpression, dict):
    """
    An NamedExpressions is a composite Expression that maps strings to Expressions.
    """
    def __init__(self, expr_dict):
        dict.__init__(self, expr_dict)
        Expression.__init__(self)
        for key, val in expr_dict.iteritems():
            if not isinstance(key, str): 
                raise TypeError("Keywords of an expression dictionary may only be strings")
            if not isinstance(val, Expression): 
                raise TypeError("Values of an expression dictionary must be Expressions")

    def __repr__(self):
        return '{' + ', '.join(repr(key) + ':' + repr(expr) for key, expr in self.iteritems()) + '}'
    
    def formatted(self, formatType, fence=False):
        return '{' + ', '.join(repr(key) + ':' + expr.formatted(formatType, fence=True) for key, expr in self.iteritems()) + '}'
    
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        return NamedExpressions({key:expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars) for key, expr in self.iteritems()})

    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.values()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variable sof the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.values()])

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
        Expression.__init__(self)
        if len(expressions) == 1 and not isinstance(expressions[0], Expression): 
            expressions = expressions[0] # allowed to pass in a single list argument
        for expr in expressions:
            if isinstance(expr, ExpressionList):
                raise NestedMultiExpressionError('May not nest ExpressionLists (do you need to use Etcetera? or ExpressionTensor?)')
            if not isinstance(expr, Expression):
                raise TypeError('ExpressionList must be created out of Expressions)')
            if isinstance(expr, Block):
                raise TypeError('A Block expression may only be used in an ExpressionTensor (you may use an Etcetera Operation in an ExpressionList)')
            self.append(expr)
        self.shape = (len(self),)
    
    def __repr__(self):
        return ','.join([repr(expr) for expr in self])
    
    def formatted(self, formatType, fence=True):
        outStr = ''
        if len(self) == 0: fence = True # for an empty list, show the parenthesis to show something.
        if formatType == STRING or formatType == LATEX:
            if fence: outStr += '('
            outStr += ', '.join([expr.formatted(formatType) for expr in self])
            if fence: outStr += ')'
        return outStr
    
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        Flattens nested ExpressionLists that arise from Etcetera substitutions.
        '''
        def subbedGen():
            for expr in self:
                subbed_expr = expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
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
        Returns the union of the free Variable sof the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self])

class ExpressionTensor(MultiExpression, dict): 
    '''
    An Expression tensor is a composite Expression represented as a dictionary mapping indices
    (as tuples of integers) to Expression elements or blocks.  It can be a sparse tensor but
    must not have overlapping blocks.
    '''
    def __init__(self, tensor):
        '''
        Create an ExpressionTensor either with a simple, dense tensor (list of lists ... of lists) or
        with a dictionary mapping indices (as tuples of integers) to Expression elements or blocks.
        '''
        dict.__init__(self)
        Expression.__init__(self)        
        if isinstance(tensor, dict):
            # Supplied a dictionary mapping indices (as tuples of integers) to Exrepssion elements or blocks.
            self.update(tensor)
            used_indices = set()
            self.dim = None
            # for each dictionary item
            for idx, block_or_element in tensor.iteritems():
                # Check for correct types and consistent dimension
                if not isinstance(block_or_element, Expression):
                    raise TypeError('Elements or blocks of the ExpressionTensor must be Expressions')
                if isinstance(block_or_element, ExpressionList):
                    raise NestedMultiExpressionError('May not embed an ExpressionList directly inside of an ExpressionTensor')
                if isinstance(block_or_element, ExpressionTensor):
                    raise NestedMultiExpressionError('May not nest an ExpressionTensor directly inside of another ExpressionTensor (do you require a Block instead?)')
                if not all(isinstance(i, int) for i in idx):
                    raise TypeError('ExpressionTensor dictionary must be use integer sequences as indices')
                if len(used_indices) > 1:
                    if self.dim != len(idx):
                        raise ValueError('Inconsistent dimension for the indices')
                self.dim = len(idx)
                # Check for overlapping Block/element
                if isinstance(block_or_element, Block):
                    block = block_or_element
                    if len(block.extent) != self.dim:
                        raise ValueError('Block extent is not consistent with ExpressionTensor dimension (indicated by indices)')
                    for block_idx in itertools.product([xrange(k) for k in block.extent]):
                        inner_idx = [i + j for i, j in zip(idx, block_idx)]
                        if inner_idx in used_indices:
                            raise ValueError('ExpressionTensor must not have overlapping blocks/elements')
                        used_indices.add(inner_idx)
                else:
                    if idx in used_indices:
                        raise ValueError('ExpressionTensor must not have overlapping blocks/elements')
                    used_indices.add(idx)
            # the shape is the maximum for the used indices in each of the dimensions
            self.shape = [0]*self.dim 
            for idx in used_indices:
                self.shape = [max(i, j) for i, j in zip(self.shape, idx)]
        else:
            from numpy import array
            a = array(tensor)
            for idx in itertools.product([xrange(k) for k in a.shape]):
                self.__setitem__(idx, a[idx])
            self.shape = a.shape
                
    def __repr__(self):
        return '{' + ', '.join(str(key) + ':' + repr(expr) for key, expr in self.iteritems()) + '}'
    
    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return '{' + ', '.join(str(key) + ':' + expr.formatted(formatType, fence=True) for key, expr in self.iteritems()) + '}'
        elif formatType == LATEX:
            outStr = r'\begin{array}[' + ''.join(['c']*self.ncolumns) + ']'
            current_row = 0
            current_col = 0
            for (r, c) in sorted(self.keys()):
                if r > current_row:
                    outStr += r'\\'
                    current_row += 1
                    current_col = 0
                while c > current_col:
                    outStr += ' & '
                    current_col += 1
                outStr += self[(r, c)].formatted(formatType, fence=True)
            outStr += r'\end{array}'
            return outStr
        
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from numpy import cumsum
        subbed_tensor = dict()
        # substitute elements/blocks of the ExpressionTensor and
        # establish shifts coming from resized Blocks in the ExpressionTensor
        shifts = [[0 for k in xrange(l)] for l in self.shape]
        for idx in sorted(self.keys()):
            element_or_block = self.get(idx)
            if isinstance(element_or_block, Block):
                block = element_or_block
                block_sub = block.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
                if isinstance(block_sub, ExpressionTensor):
                    # The Block is replaced with an ExpressionTensor that must be embedded in this ExpressionTensor.
                    # For now, we'll just compute index shifts and store the entire tensor for the Block in its original index.
                    for k, (i, orig_ex, sub_ex) in enumerate(zip(idx, block.extent, block_sub.shape)):
                        shifts[k][i+orig_ex] = (sub_ex - orig_ex)
                subbed_tensor[idx] = block_sub
            else:
                element_sub = element_or_block.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
                subbed_tensor[idx] = element_sub
        # obtain index mapping, for each tensor dimension, from the shifts
        idx_mapping = [cumsum(shifts[l]) for l in self.shape]
        # re-map indices
        subbed_and_shifted_tensor = dict()
        for idx in sorted(subbed_tensor.keys()):
            if isinstance(subbed_tensor[idx], ExpressionTensor):
                # Expand a tensor-replaced Block into the full tensor
                for block_idx in subbed_tensor[idx].keys():
                    subbed_and_shifted_tensor[tuple([idx_mapping[k] + block_idx[k] for k in idx])] = subbed_tensor[idx][block_idx]
            else:
                subbed_and_shifted_tensor[tuple([idx_mapping[k] for k in idx])] = subbed_tensor[idx]
        # Return the ExpressionTensor with its substitutions
        return ExpressionTensor(subbed_and_shifted_tensor)
        
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.values()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variable sof the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.values()])

class Bundle(MultiExpression):
    def __init__(self, multiExprType, bundledExpr, maker):
        Expression.__init__(self)
        assert multiExprType == ExpressionList or multiExprType == ExpressionTensor, "Unrecognized multi-Expression type for Bundle"
        self.multiExprType = multiExprType
        self.bundledExpr = bundledExpr
        self.maker = maker

    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this Expression with the variables substituted according to subMap 
        and/or relabeled according to relabelMap.  If the substituted bundledExpr
        if of the multiExprType, it will be extracted from the Bundle wrapping and 
        incorporated into the multi-Expression which contains it.
        '''
        subbed = self.bundledExpr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
        if isinstance(subbed, self.multiExprType):
            # substituting the entire Bundles expression with an ExpressionList to be merged with an outer multi-Expression
            return subbed 
        else:
            return self.maker(subbed)

    def usedVars(self):
        '''
        Returns the union of the used Variables of the bundledExpr.
        '''
        return self.bundledExpr.usedVars()
        
    def freeVars(self):
        '''
        Returns the union of the free Variable sof the bundledExpr.
        '''
        return self.bundledExpr.freeVars()

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
    
    def __repr__(self):
        return '..' + repr(self.bundledExpr) + '..'
    
    def formatted(self, formatType, fence=False):
        # override this default as desired
        if formatType == STRING or formatType == LATEX:
            return '..' + self.bundledExpr.formatted(formatType, fence=False) + '..'
    
class Block(Bundle):
    def __init__(self, expr, extent, flexible):
        self.extent = tuple(extent)
        self.flexible = flexible
        Bundle.__init__(self, ExpressionTensor, expr, lambda expr : Block(expr, self.extent, self.flexible))

    def __repr__(self):
        if self.flexible:
            return '[..' + repr(self.bundledExpr) + '..]_' + self.extent
        else:
            return '[' + repr(self.bundledExpr) + ']_' + self.extent
    
    def formatted(self, formatType, fence=True):
        # override this default as desired
        innerFormatted = self.bundledExpr.formatted(formatType, fence=False)
        if formatType == STRING:
            if self.flexible:
                return '[..' + innerFormatted + '..]'
            else:
                return '[' + innerFormatted + ']'
        elif formatType == LATEX:
            if self.flexible:
                return '\left[..' + innerFormatted + '..\right]'
            else:
                return '\left[' + innerFormatted + '\right]'

    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        subbed = Bundle.substituted(self, varSubMap, operationSubMap, relabelMap, reservedVars)
        if not self.flexible and isinstance(subbed, ExpressionTensor) and subbed.shape != self.extent:
            raise ExpressionTensorReshapingError("May not change the shape of a Block that is not flexible")
        inner_sub = self.expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars) 
        if isinstance(inner_sub, ExpressionList) or isinstance(inner_sub, ExpressionTensor):
            assert self.flexible or (inner_sub.shape == self.extent), 'The Block extent cannot change unless the Block was created to be flexible'
            return Block(inner_sub, inner_sub.shape, self.flexible)
        else:
            return Block(inner_sub, self.extent, self.flexible)

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
    elif isinstance(expressions, dict):
        if len(expressions) > 0 and isinstance(expressions.keys()[0], str):
            # when there is a string key, it must be an NamedExpressions
            return NamedExpressions(expressions)
        else:
            # if dict is not an NamedExpressions, it must be an ExpressionTensor 
            return ExpressionTensor(expressions)
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

class ExpressionTensorReshapingError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

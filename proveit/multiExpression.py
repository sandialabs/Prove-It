'''
multiExpression.py

The internal logic of Prove-It knows about a few special types of Expression classes
that contain multiple Expressions: ExpressionDict, ExpressionList, and ExpressionTensor.
An ExpressionDict maps string identifiers to Expressions.  An ExpressionList is a linear
list of Expressions with special substitution rules regarding Etcetera list elements.
When an ExpressionList is substituted for an Etcetera Expression, its elements will be 
absorbed into the parent ExpressionList.  An ExpressionTensor maps lists of integers
to Expression elements or Blocks and has special substitution rules regarding Blocks.
When an ExpressionTensor is substituted for a Block Expression, its elements (or blocks)
will be absorbed into the parent ExpressionTensor.
'''

from proveit.expression import Expression, Variable, Operation, STRING, LATEX
import itertools

class ExpressionDict(Expression, dict):
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
        return ExpressionDict({key:expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars) for key, expr in self.iteritems()})

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

class ExpressionList(Expression, list):
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
                raise NestedExpressionListsError()
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

def _expressionOrList(expressions):
    '''
    From one or more expressions, return the flattened ExpressionList or single Expression.
    '''
    expressionList = ExpressionList(*expressions)
    return expressionList.first() if len(expressionList) == 1 else expressionList

class Etcetera(Expression):
    def __init__(self, expr):
        Expression.__init__(self)
        self.etcExpr = expr
    
    def __repr__(self):
        return '..' + repr(self.etcExpr) + '..'
    
    def formatted(self, formatType, fence=False):
        # override this default as desired
        if formatType == STRING or formatType == LATEX:
            return '..' + self.etcExpr.formatted(formatType, fence=False) + '..'
    
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        if relabelMap is not None and self in relabelMap:
            # relabel the Etcetera Variable as a whole: e.g., ..x.. becoming [x, y, z]
            return self.etcExpr.substituted(dict(), None, {self.etcExpr:relabelMap[self]}, reservedVars) # does proper restriction check
        elif relabelMap is not None and self.etcExpr in relabelMap:
            # just relabel the Etcetera Variable, keeping it as an Etcetera Variable            
            # e.g., ..Q.. becoming ..R..
            return Etcetera(self.etcExpr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)) # does proper restriction check
        elif varSubMap is not None and self in varSubMap:
            # substitute the Etcetera Variable as a whole: e.g., ..x.. becoming [x+1, y+5, z-2]
            return self.etcExpr.substituted({self.etcExpr:varSubMap[self]}, None, relabelMap, reservedVars) # does proper restriction check
        elif operationSubMap is not None and isinstance(self.etcExpr, Operation) and Etcetera(self.etcExpr.operator) in operationSubMap:
            # relabel the Etcetera Operation as a whole: e.g., ..Q(x).. becomming [R(x), S(x)]
            return self.etcExpr.substituted(dict(), {self.etcExpr.operator:operationSubMap[Etcetera(self.etcExpr.operator)]}, relabelMap, reservedVars) # does proper restriction check
        # otherwise, just perform the substitution on the innards and keep it wrapped with Etcetera
        return Etcetera(self.etcExpr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars))
        
    def usedVars(self):
        '''
        Returns the union of the used Variables of the etcExpr.
        '''
        return self.etcExpr.usedVars()
        
    def freeVars(self):
        '''
        Returns the union of the free Variable sof the etcExpr.
        '''
        return self.etcExpr.freeVars()

def isEtcVar(expr):
    return isinstance(expr, Etcetera) and isinstance(expr.etcExpr, Variable)

def isEtcVarOrVar(expr):
    return isinstance(expr, Variable) or isEtcVar(expr)

def extractVar(expr):
    # Return expr if it is a Variable, extract the Variable out of an Etcetera Variable
    # if it is one, or return None.
    return expr.etcExpr if isEtcVar(expr) else (expr if isinstance(expr, Variable) else None)

def isEtcOperation(expr):
    return isinstance(expr, Etcetera) and isinstance(expr.etcExpr, Operation)

class ExpressionTensor(Expression, dict): 
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
        return '{' + ', '.join(str(key) + ':' + expr.formatted(formatType, fence=True) for key, expr in self.iteritems()) + '}'

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
                for k, (i, orig_ex, sub_ex) in enumerate(zip(idx, block.extent, block_sub.extent)):
                    shifts[k][i+orig_ex] = (sub_ex - orig_ex)
            else:
                element_sub = element_or_block.substituted(varSubMap, operationSubMap, relabelMap, reservedVars)
                subbed_tensor[idx] = element_sub
        # obtain index mapping, for each tensor dimension, from the shifts
        idx_mapping = [cumsum(shifts[l]) for l in self.shape]
        # re-map indices
        subbed_and_shifted_tensor = dict()
        for idx in sorted(subbed_tensor.keys()):
            subbed_and_shifted_tensor[tuple([idx_mapping[k] for k in idx])] = subbed_tensor[idx]
        return ExpressionTensor(subbed_tensor)
        
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

class Block(Expression):
    def __init__(self, expr, extent, flexible):
        self.expr = expr
        self.extent = extent
        self.flexible = flexible
        
    def substituted(self, varSubMap, operationSubMap = None, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        inner_sub = self.expr.substituted(varSubMap, operationSubMap, relabelMap, reservedVars) 
        if isinstance(inner_sub, ExpressionList) or isinstance(inner_sub, ExpressionTensor):
            assert self.flexible or (inner_sub.shape == self.extent), 'The Block extent cannot change unless the Block was created to be flexible'
            return Block(inner_sub, inner_sub.shape, self.flexible)
        else:
            return Block(inner_sub, self.extent, self.flexible)

    def usedVars(self):
        '''
        Returns the used Variables of this Block Expression.
        '''
        return self.expr.usedVars()
        
    def freeVars(self):
        '''
        Returns the free Variables of this Block Expression.
        '''
        return self.expr.freeVars()

def multiExpression(expressions):
    '''
    Put the appropriate multi-Expression wrapper around expressions.  
    Dictionaries with string keys will be wrapped in an ExpressionDict.  
    Other dictionaries will be wrapped in an ExpressionTensor.  
    A single Expression or iterable over only Expressions will be wrapped 
    in an ExpressionList.
    '''
    if isinstance(expressions, ExpressionList) or isinstance(expressions, ExpressionDict) or isinstance(expressions, ExpressionTensor):
        return expressions # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        return ExpressionList(expressions) # a single expression that we will wrap in an ExpressionLIst
    elif isinstance(expressions, dict):
        if len(expressions) > 0 and isinstance(expressions.keys()[0], str):
            # when there is a string key, it must be an ExpressionDict
            return ExpressionDict(expressions)
        else:
            # if dict is not an ExpressionDict, it must be an ExpressionTensor 
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

class NestedExpressionListsError(Exception):
    def __init__(self):
        pass
    def __str__(self):
        return "May not nest ExpressionLists (do you need to use Etcetera? or ExpressionTensor?)"

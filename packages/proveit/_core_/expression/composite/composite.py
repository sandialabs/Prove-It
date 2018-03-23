'''
compositeExpression.py

The core of Prove-It knows about a few special types of expr classes
that contain multiple Expressions: NamedExprs, ExprList, and ExprTensor.
NamedExprs map identifier strings to Expressions.  An ExprList is a linear
list of Expressions,  An ExprTensor is a multi-dimensional extension of
an ExprList, which introduces extra complications.  It works by
mapping indices (one for each dimension) to elements.  Indices
of an ExprTensor may be general expressions.  The order of distinct indices
in each dimension must be known via axioms, theorems, or assumptions.

The ExprList and ExprTensor composites may contain Embed 
expressions that represent blocks of elements to be embedded 
into their containers.  
'''


from proveit._core_.expression.expr import Expression

class Composite:
    """
    The base class for NamedExprs, ExprList, and ExprTensor.
    """
    pass


def compositeExpression(expressions):
    '''
    Put the appropriate CompositeExpression wrapper around expressions.  
    Dictionaries with string keys will be wrapped in an NamedExpressions.  
    Other dictionaries will be wrapped in an ExpressionTensor.  
    A single expr or iterable over only Expressions will be wrapped 
    in an exprlist.
    '''
    from expr_list import ExprList
    from named_exprs import NamedExprs
    from expr_tensor import ExprTensor
    from proveit._core_.known_truth import KnownTruth
    
    if isinstance(expressions, KnownTruth):
        expressions = expressions.expr
    
    if isinstance(expressions, ExprList) or isinstance(expressions, NamedExprs) or isinstance(expressions, ExprTensor):
        return expressions # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        return ExprList([expressions]) # a single expression that we will wrap in an ExpressionLIst
    else:
        if all(isinstance(subExpr, Expression) or isinstance(subExpr, KnownTruth) for subExpr in expressions):
            # An iterable over only Expressions must be an exprlist
            return ExprList(expressions)
        else:
            try:
                # try to see if we can use expressions to generate a NamedExpressions object
                return NamedExprs(expressions)
            except:        
                # Assume to be a tensor as a list of lists
                return ExprTensor(expressions)

def singleOrCompositeExpression(exprOrExprs):
    '''
    Put the approriate CompositeExpression wrapper around a list (iterable) or dictionary
    of Expressions, or simply return the given Expression if it is one.
    '''
    from proveit._core_.known_truth import KnownTruth
    if isinstance(exprOrExprs, KnownTruth):
        exprOrExprs = exprOrExprs.expr
    if isinstance(exprOrExprs, Expression):
        return exprOrExprs
    else: return compositeExpression(exprOrExprs)


def _simplifiedCoord(coord, assumptions, requirements):
    '''
    Simplify the given coordinate under the given assumptions and append
    the equality of the simplified and original indices as a requirement
    if they are not the same.
    '''
    from proveit.number import simplified
    from proveit.logic import Equals
    simplified_coord = simplified(coord, assumptions=assumptions)
    if simplified_coord != coord and requirements is not None:
        requirements.append(Equals(coord, simplified_coord))
    return simplified_coord

class IndexingError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

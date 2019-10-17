'''
compositeExpression.py

The core of Prove-It knows about a few special types of expr classes
that contain multiple Expressions: NamedExprs, ExprTuple, and ExprArray.
NamedExprs map identifier strings to Expressions.  An ExprTuple is a linear
list of Expressions,  An ExprArray is a multi-dimensional extension of
an ExprTuple, which introduces extra complications.  It works by
mapping indices (one for each dimension) to elements.  Indices
of an ExprArray may be general expressions.  The order of distinct indices
in each dimension must be known via axioms, theorems, or assumptions.

The ExprTuple and ExprArray composites may contain Embed 
expressions that represent blocks of elements to be embedded 
into their containers.  
'''


from proveit._core_.expression.expr import Expression

class Composite:
    """
    The base class for NamedExprs, ExprTuple, and ExprArray.
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
    from .expr_list import ExprTuple
    from .named_exprs import NamedExprs
    from .expr_tensor import ExprArray
    from proveit._core_.known_truth import KnownTruth
    
    if isinstance(expressions, KnownTruth):
        expressions = expressions.expr
    
    if isinstance(expressions, ExprTuple) or isinstance(expressions, NamedExprs) or isinstance(expressions, ExprArray):
        return expressions # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        return ExprTuple(expressions) # a single expression that we will wrap in an ExpressionLIst
    else:
        if isinstance(expressions, dict):
            return ExprArray(expressions)
        try:
            # see if we can build an expression list
            return ExprTuple(*[singleOrCompositeExpression(subExpr) for subExpr in expressions])
        except:
            # try to see if we can use expressions to generate a NamedExpressions object
            return NamedExprs(expressions)

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
    from proveit.logic import Equals
    #from proveit.number import Add
    try:
        simplified_coord = coord.simplification(assumptions=assumptions).rhs
    except:
        simplified_coord = coord # unable to simplify.  that's okay.
    if simplified_coord != coord and requirements is not None:
        requirements.append(Equals(coord, simplified_coord))
    return simplified_coord

class IndexingError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

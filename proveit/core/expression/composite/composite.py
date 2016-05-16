from proveit.core.expression.expr import Expression

class Composite:
    """
    The base class for NamedExpressions, exprlist, and ExpressionTensor.
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
    from expr_list import ExpressionList
    from named_exprs import NamedExpressions
    from expr_tensor import ExpressionTensor
    
    if isinstance(expressions, ExpressionList) or isinstance(expressions, NamedExpressions) or isinstance(expressions, ExpressionTensor):
        return expressions # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        return ExpressionList(expressions) # a single expression that we will wrap in an ExpressionLIst
    elif isinstance(expressions, dict) and len(expressions.keys()) > 0 and isinstance(expressions.keys()[0], str):
        # A dictionary must be an NamedExpressions
        return NamedExpressions(expressions)
    else:
        if all(isinstance(subExpr, Expression) for subExpr in expressions):
            # An iterable over only Expressions must be an exprlist
            return ExpressionList(*expressions)
        else:
            # Assume to be a tensor as a list of lists
            return ExpressionTensor(expressions)

def singleOrCompositeExpression(exprOrExprs):
    '''
    Put the approriate CompositeExpression wrapper around a list (iterable) or dictionary
    of Expressions, or simply return the given Expression if it is one.
    '''
    if isinstance(exprOrExprs, Expression):
        return exprOrExprs
    else: return compositeExpression(exprOrExprs)

class NestedCompositeExpressionError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
    
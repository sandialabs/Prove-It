'''
composite_expression.py

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


def singular_expression(expression):
    from .expr_range import ExprRange
    from proveit._core_.judgment import Judgment
    if isinstance(expression, Judgment):
        expression = expression.expr
    if isinstance(expression, ExprRange):
        raise TypeError("A singular expression may not be an ExprRange "
                        ": %s" % expression)
    if isinstance(expression, Composite):
        raise TypeError("A singular expression may not be a Composite "
                        "(ExprTuple or NamedExprs): %s" % expression)
    assert isinstance(expression, Expression)
    return expression


def composite_expression(expressions):
    '''
    Put the appropriate CompositeExpression wrapper around expressions.
    Dictionaries with string keys will be wrapped in an NamedExpressions.
    Other dictionaries will be wrapped in an ExpressionTensor.
    A single expr or iterable over only Expressions will be wrapped
    in an exprlist.
    '''
    from .expr_tuple import ExprTuple
    from .named_exprs import NamedExprs
    from proveit._core_.judgment import Judgment
    from proveit._core_.theory import UnsetCommonExpressionPlaceholder

    if isinstance(expressions, UnsetCommonExpressionPlaceholder):
        expressions.raise_attempted_use_error()
    if isinstance(expressions, Judgment):
        expressions = expressions.expr
    if isinstance(
            expressions,
            ExprTuple) or isinstance(
            expressions,
            NamedExprs):
        return expressions  # already in a multi-expression wrapper
    elif isinstance(expressions, Expression):
        # A single expression that we will wrap in an ExprTuple:
        return ExprTuple(expressions)
    else:
        if len(expressions) == 0:
            return ExprTuple()
        try:
            # try to see if we can use expressions to generate a
            # NamedExpressions object
            return NamedExprs(expressions)
        except (TypeError, ValueError):
            # See if we can build an ExprTuple.
            return ExprTuple(*expressions)


def single_or_composite_expression(expr_or_exprs,
                                   wrap_expr_range_in_tuple=True,
                                   do_singular_reduction=False):
    '''
    Put the approriate CompositeExpression wrapper around a list
    (iterable) or dictionary of Expressions, or simply return the given
    Expression if it is one.  If wrap_expr_range_in_tuple, wrap
    an ExprRange in an ExprTuple. If do_singular_reduction is True and
    the result is an ExprTuple with one item that is neither an
    ExprRange nor a nested ExprTuple, return the single item.
    '''
    from proveit._core_.judgment import Judgment
    from proveit._core_.theory import UnsetCommonExpressionPlaceholder
    from .expr_tuple import ExprTuple
    from .expr_range import ExprRange
    if isinstance(expr_or_exprs, UnsetCommonExpressionPlaceholder):
        expr_or_exprs.raise_attempted_use_error()
    if isinstance(expr_or_exprs, Judgment):
        expr_or_exprs = expr_or_exprs.expr
    if wrap_expr_range_in_tuple and isinstance(expr_or_exprs, ExprRange):
        # An ExprRange must be wrapped in an ExprTuple in the
        # situations when either a single or composite are allowed.
        return ExprTuple(expr_or_exprs)
    if not isinstance(expr_or_exprs, Expression):
        expr_or_exprs = composite_expression(expr_or_exprs)
    if (do_singular_reduction and isinstance(expr_or_exprs, ExprTuple)
            and len(expr_or_exprs) == 1):
        if (not isinstance(expr_or_exprs[0], ExprTuple) and
                not isinstance(expr_or_exprs[0], ExprRange)):
            # Reduce it to a singular expression.
            return expr_or_exprs[0]
    return expr_or_exprs


def _generateCoordOrderAssumptions(coords):
    from proveit.numbers import LessEq, GreaterEq
    for prev_coord, next_coord in zip(coords[:-1], coords[1:]):
        yield LessEq(prev_coord, next_coord)
        yield GreaterEq(next_coord, prev_coord)


class IndexingError(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

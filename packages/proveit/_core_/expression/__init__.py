from .expr import (Expression, traverse_inner_expressions, used_vars,
                   possibly_free_var_ranges, free_vars, attempt_to_simplify,
                   expression_depth, MakeNotImplemented,
                   ImproperReplacement)
from .style_options import StyleOptions
from .inner_expr import InnerExpr, shallowest_inner_expr
from .fencing import maybe_fenced_string, maybe_fenced_latex, maybe_fenced
from .operation import (
    Operation, IndexedVar, Function,
    OperationOverInstances, bundle, unbundle, OperationError)
from .conditional import Conditional, ConditionalSet
from .lambda_expr import (
    Lambda, ParameterCollisionError, DisallowedParameterRelabeling,
    LambdaApplicationError, ArgumentExtractionError)
from .composite import (
    Composite, composite_expression, single_or_composite_expression,
    ExprTuple, extract_var_tuple_indices, ExprTupleError,
    ExprArray, NamedExprs, ExprRange,
    var_range, RangeInstanceError)
from .label import (Label, Literal, Variable, DuplicateLiteralError,
                    safe_dummy_var, safe_dummy_vars, safe_default_or_dummy_var)

InnerExpr.register_equivalence_method(
    ExprRange, 'partition', 'partitioned', 'split')
InnerExpr.register_equivalence_method(ExprTuple, 'merger', 'merged', 'merge')

InnerExpr.register_equivalence_method(
    Lambda,  'substitution', 'substituted', 'substitute')

InnerExpr.register_equivalence_method(
    OperationOverInstances, 
    'instance_substitution', 'instance_substituted', 
    'instance_substitute')
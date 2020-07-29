from .expr import (Expression, traverse_inner_expressions, used_vars, 
                   possibly_free_var_ranges, free_vars, attempt_to_simplify,
                   expressionDepth, MakeNotImplemented, 
                   ImproperReplacement)
from .style_options import StyleOptions
from .inner_expr import InnerExpr
from .fencing import maybeFencedString, maybeFencedLatex, maybeFenced
from .operation import (
        Operation, IndexedVar, indexed_var, Function, OperationSequence, 
        OperationOverInstances, bundle, unbundle, OperationError)
from .conditional import Conditional
from .lambda_expr import (
        Lambda, ParameterCollisionError, DisallowedParameterRelabeling,
        LambdaApplicationError, ArgumentExtractionError)
from .composite import (
        Composite, compositeExpression, singleOrCompositeExpression, 
        ExprTuple, extract_var_tuple_indices, ExprTupleError, 
        ExprArray, NamedExprs, ExprRange,
        varRange, RangeInstanceError)
from .label import (Label, Literal, Variable, DuplicateLiteralError, 
                    safeDummyVar, safeDummyVars, safeDefaultOrDummyVar)

InnerExpr.register_equivalence_method(ExprRange, 'partition', 'partitioned', 'split')
InnerExpr.register_equivalence_method(ExprTuple, 'merger', 'merged', 'merge')

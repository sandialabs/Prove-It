from .expr import (Expression, used_vars, free_vars, free_indexed_vars,
                   expressionDepth,
                   MakeNotImplemented, ImproperSubstitution, ScopingViolation)
from .style_options import StyleOptions
from .inner_expr import InnerExpr
from .fencing import maybeFencedString, maybeFencedLatex, maybeFenced
from .operation import (Operation, IndexedVar, Function, OperationSequence, 
                        OperationOverInstances, OperationError)
from .conditional import Conditional
from .lambda_expr import (Lambda, ParameterCollisionError,
                          LambdaApplicationError, ArgumentExtractionError)
from .composite import (
        Composite, compositeExpression, singleOrCompositeExpression, 
        ExprTuple, ExprTupleError, ExprArray, NamedExprs, ExprRange,
        varRange, RangeInstanceError)
from .label import (Label, Literal, Variable, DuplicateLiteralError, 
                    safeDummyVar, safeDefaultOrDummyVar)

InnerExpr.register_equivalence_method(ExprRange, 'partition', 'partitioned', 'split')
InnerExpr.register_equivalence_method(ExprTuple, 'merger', 'merged', 'merge')

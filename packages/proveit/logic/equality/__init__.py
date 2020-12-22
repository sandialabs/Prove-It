from .equals import (
    Equals,
    reduce_operands,
    default_simplification,
    evaluate_truth,
    SimplificationError,
    EvaluationError)
#from equals import auto_substitute, auto_substitution, auto_statement_substitution, generate_sub_expressions, extract_sub_expr
from .not_equals import NotEquals


# KEEP THE FOLLOWING AT THE BOTTOM OF THIS __init__.py.
#  (Additions may be made above)
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

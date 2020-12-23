from .equals import (
    Equals,
    reduce_operands,
    default_simplification,
    evaluate_truth,
    SimplificationError,
    EvaluationError)
#from equals import auto_substitute, auto_substitution, auto_statement_substitution, generate_sub_expressions, extract_sub_expr
from .not_equals import NotEquals


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

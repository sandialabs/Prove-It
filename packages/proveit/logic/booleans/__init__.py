from .quantification import Forall, Exists, NotExists, UniqueExists
from .booleans import in_bool, BooleanSet, TrueLiteral, FalseLiteral
from .conjunction import And, compose
from .disjunction import Or
from .negation import Not
from .implication import Implies, Iff, conclude_via_implication


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

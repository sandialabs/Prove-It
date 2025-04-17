# Boolean arithmetic, equality, and set theory.

from .booleans import Boolean, TRUE, FALSE
from .booleans import (And, Or, Not, Implies, Iff, XOr,
                       compose, conclude_via_implication)
from .booleans import in_bool, BooleanSet, TrueLiteral, FalseLiteral
from .booleans import Forall, Exists, NotExists, UniqueExists
from .equality import (
    Equals,
    NotEquals,
    evaluate_truth,
    evaluate_falsehood,
    evaluation_or_simplification,
    deduce_equal_or_not,
    SimplificationError,
    EvaluationError)
from .irreducible_value import IrreducibleValue, is_irreducible_value
from .sets import EmptySet, Set, SetEquiv, SetNotEquiv
from .sets import InSet, NotInSet, SetMembership, SetNonmembership
# StrictSubset and SubsetProper are aliases for ProperSubset.
# StrictSuperset and SupersetProper are aliases for ProperSuperset.
from .sets import (
    SubsetEq, NotSubsetEq, ProperSubset, StrictSubset, SubsetProper,
    NotProperSubset, superset_eq, not_superset_eq, proper_superset,
    not_proper_superset)
from .sets import (Union, UnionAll, Intersect, IntersectAll, Difference,
                   SetOfAll, CartProd, CartExp,
                   PowerSet, Disjoint, Distinct, Card)
from .sets import (Functions, Injections, Surjections, Bijections,
                   Image, InvImage)
from .classes import InClass, NotInClass, ClassMembership, ClassNonmembership

#from mapping.mapping_ops import Domain, CoDomain

import proveit

if proveit.defaults.running_theory_notebook is None:
    # Import some fundamental theorems without quantifiers when not 
    # running an common/axioms/theorems theory notebook.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first
    # time, but fine after that.
    from .booleans.negation import not_f, not_t
    from .booleans.negation import not_false
    from .booleans.implication import true_implies_true, false_implies_true, false_implies_false
    from .booleans import true_axiom, bools_def, false_not_true
    from .booleans import true_eq_true, false_eq_false, true_not_false, true_is_bool, false_is_bool


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

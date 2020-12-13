# Boolean arithmetic, equality, and set theory.

from .booleans import Boolean, TRUE, FALSE
from .booleans import And, Or, Not, Implies, Iff, compose, concludeViaImplication
from .booleans import inBool, BooleanSet, TrueLiteral, FalseLiteral
from .booleans import Forall, Exists, NotExists
from .sets import EmptySet, Set, SetEquiv, SetNotEquiv
from .sets import InSet, NotInSet, Membership, Nonmembership
# StrictSubset and SubsetProper are aliases for ProperSubset.
# StrictSuperset and SupersetProper are aliases for ProperSuperset.
from .sets import (
        SubsetEq, NotSubsetEq, ProperSubset, StrictSubset, SubsetProper,
        NotProperSubset, SupersetEq, NotSupersetEq, ProperSuperset, 
        StrictSuperset, SupersetProper, NotProperSuperset)
from .sets import (Union, UnionAll, Intersect, IntersectAll, Difference, 
                   SetOfAll, PowerSet, Disjoint, Distinct, Card)
from .equality import (Equals, NotEquals, reduceOperands, defaultSimplification,
                       evaluateTruth, SimplificationError, EvaluationError)
from .irreducible_value import IrreducibleValue, isIrreducibleValue

#from mapping.mappingOps import Domain, CoDomain

import proveit

if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from .booleans.negation._axioms_ import notF, notT
    from .booleans.negation._theorems_ import notFalse
    from .booleans.implication._theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
    from .booleans._axioms_ import trueAxiom, boolsDef, falseNotTrue
    from .booleans._theorems_ import trueEqTrue, falseEqFalse, trueNotFalse, trueInBool, falseInBool

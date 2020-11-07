# Boolean arithmetic, equality, and set theory.

from .boolean import Booleans, TRUE, FALSE
from .boolean import And, Or, Not, Implies, Iff, compose, concludeViaImplication
from .boolean import inBool, BooleanSet, TrueLiteral, FalseLiteral
from .boolean import Forall, Exists, NotExists
from .set_theory import EmptySet, Set, SetEquiv, SetNotEquiv
from .set_theory import InSet, NotInSet, Membership, Nonmembership
# StrictSubset and SubsetProper are aliases for ProperSubset.
# StrictSuperset and SupersetProper are aliases for ProperSuperset.
from .set_theory import (
        SubsetEq, NotSubsetEq, ProperSubset, StrictSubset, SubsetProper,
        NotProperSubset, SupersetEq, NotSupersetEq, ProperSuperset, 
        StrictSuperset, SupersetProper, NotProperSuperset)
from .set_theory import (Union, UnionAll, Intersect, IntersectAll, Difference, 
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
    from .boolean.negation._axioms_ import notF, notT
    from .boolean.negation._theorems_ import notFalse
    from .boolean.implication._theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
    from .boolean._axioms_ import trueAxiom, boolsDef, falseNotTrue
    from .boolean._theorems_ import trueEqTrue, falseEqFalse, trueNotFalse, trueInBool, falseInBool

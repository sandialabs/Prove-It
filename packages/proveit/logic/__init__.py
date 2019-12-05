# Boolean arithmetic, equality, and set theory.

from .boolean import Booleans, TRUE, FALSE
from .boolean import And, Or, Not, Implies, Iff, compose, concludeViaImplication
from .boolean import inBool
from .boolean import Forall, Exists, NotExists
from .set_theory import EmptySet, InSet, Membership, NotInSet, Nonmembership
from .set_theory import NotProperSubset, NotSubset, NotSubsetEq, NotSuperset, NotSupersetEq
from .set_theory import NotProperSuperset
from .set_theory import ProperSubset, ProperSuperset
from .set_theory import Set, Subset, SubsetEq, SubsetProper
from .set_theory import StrictSuperset, Superset, SupersetEq, SupersetProper
from .set_theory import Card, Difference, Disjoint, Distinct, Intersect
from .set_theory import SetEquiv, SetNotEquiv
from .set_theory import Union, SetOfAll
from .equality import Equals, NotEquals
from .equality import reduceOperands, defaultSimplification, evaluateTruth, SimplificationError
from .irreducible_value import IrreducibleValue, isIrreducibleValue

#from mapping.mappingOps import Domain, CoDomain

import proveit

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from .boolean.negation._theorems_ import notFalse, notF, notT, notTimpliesF
#     from .boolean.implication._theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
#     from .boolean._axioms_ import trueAxiom, boolsDef, falseNotTrue
#     from .boolean._theorems_ import trueEqTrue, falseEqFalse, trueNotFalse, trueInBool, falseInBool

if proveit.defaults.automation:
		try:
		    # Import some fundamental theorems without quantifiers that are
		    # imported when automation is used.
		    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
		    from .boolean.negation._theorems_ import notFalse, notF, notT, notTimpliesF
		    from .boolean.implication._theorems_ import trueImpliesTrue, falseImpliesTrue, falseImpliesFalse
		    from .boolean._axioms_ import trueAxiom, boolsDef, falseNotTrue
		    from .boolean._theorems_ import trueEqTrue, falseEqFalse, trueNotFalse, trueInBool, falseInBool
		except:
		    pass

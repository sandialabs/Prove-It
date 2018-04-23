# Boolean arithmetic, equality, and set theory.

from boolean import And, Or, Not, Implies, Iff, compose, concludeViaImplication
try:
    from boolean import Booleans, TRUE, FALSE
except ImportError:
    pass # if the boolean common expressions have not been generated yet
from boolean import inBool
from boolean import Forall, Exists, NotExists
try:
    from set_theory import EmptySet
except ImportError:
    pass # if the set_theory common expressions have not been generated yet
from set_theory import InSet, NotInSet, Set, SubsetEq, SupersetEq, Subset, Superset, NotSubsetEq, NotSupersetEq
from set_theory import Union, Intersect, Difference, SetOfAll, Disjoint, Distinct, Card
from equality import Equals, NotEquals
from equality import reduceOperands, defaultEvaluate, evaluateTruth, EvaluationError
from irreducible_value import IrreducibleValue, isIrreducibleValue

#from mapping.mappingOps import Domain, CoDomain

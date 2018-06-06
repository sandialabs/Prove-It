# Boolean arithmetic, equality, and set theory.

from boolean import And, Or, Not, Implies, Iff, compose, concludeViaImplication
from boolean import Booleans, TRUE, FALSE
from boolean import inBool
from boolean import Forall, Exists, NotExists
from set_theory import EmptySet
from set_theory import InSet, NotInSet, Set, SubsetEq, SupersetEq, Subset, Superset, NotSubsetEq, NotSupersetEq
from set_theory import Union, Intersect, Difference, SetOfAll, Disjoint, Distinct, Card
from equality import Equals, NotEquals
from equality import reduceOperands, defaultEvaluate, evaluateTruth, EvaluationError
from irreducible_value import IrreducibleValue, isIrreducibleValue

#from mapping.mappingOps import Domain, CoDomain

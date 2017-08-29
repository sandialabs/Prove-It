# Boolean arithmetic, equality, and set theory.

from boolean import And, Or, Not, Implies, Iff, compose, concludeViaImplication
from boolean import Booleans, TRUE, FALSE
from boolean import inBool
from boolean import Forall, Exists, NotExists
from set_theory import EmptySet, InSet, NotInSet, Set, SubsetEq, SupersetEq, Subset, Superset, NotSubsetEq, NotSupersetEq
from set_theory import Union, Intersect, Difference, SetOfAll, Disjoint, Distinct, Card
from equality import Equals, NotEquals, IrreducibleValue
from equality import reduceOperands, concludeViaReduction, defaultEvaluate, evaluateTruth, EvaluationError
#from equality import autoSubstitute, autoSubstitution, autoStatementSubstitution, generateSubExpressions, extractSubExpr

#from mapping.mappingOps import Domain, CoDomain

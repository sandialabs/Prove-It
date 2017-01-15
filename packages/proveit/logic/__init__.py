# Boolean arithmetic, equality, and set theory.

from boolean import And, Or, Not, Implies, Iff, compose
from boolean import TRUE, FALSE, Booleans, inBool, deduceInBool
from boolean import Forall, Exists, NotExists
from set_theory import InSet, NotInSet, Singleton, Union, Intersect, Difference, SubsetEq, SupersetEq, SetOfAll
from set_theory.common import NOTHING
from equality import Equals, NotEquals, IrreducibleValue
from equality import reduceOperands, proveViaReduction, defaultEvaluate, evaluateTruth, EvaluationError
from transitivity_search import transitivitySearch
#from equality import autoSubstitute, autoSubstitution, autoStatementSubstitution, generateSubExpressions, extractSubExpr

#from mapping.mappingOps import Domain, CoDomain

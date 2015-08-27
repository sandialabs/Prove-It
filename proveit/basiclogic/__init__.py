from genericOps import BinaryOperation, AssociativeOperation, OperationOverInstances
from boolean.quantifiers import Forall, Exists, NotExists
from boolean.boolSet import TRUE, FALSE, BOOLEANS, inBool, deduceInBool
from boolean.boolOps import And, Or, Not, Implies, Iff, deriveStmtEqTrue, compose
from set.setOps import In, NotIn, Singleton, Complement, Union, Intersection, SubsetEq, SupersetEq, SetOfAll, EVERYTHING, NOTHING
from equality.eqOps import Equals, NotEquals, autoSubstitute, autoSubstitution, autoStatementSubstitution
from equality.equation import Equation
from mapping.mappingOps import Domain, CoDomain
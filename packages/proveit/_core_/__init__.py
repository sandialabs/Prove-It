# Core Prove-It constructs required used to construct/verify proofs.

from expression import Expression, Operation, Function, OperationSequence, OperationOverInstances
from expression import Lambda, LambdaError, ParameterExtractionError, Label, Variable, Literal, DuplicateLiteralError
from expression import safeDummyVar, safeDefaultOrDummyVar, expressionDepth
from expression import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation
from expression import Composite, compositeExpression, singleOrCompositeExpression
from expression import ExprList, ExprTensor, NamedExprs, Indexed, Iter, varIter
from expression import maybeFencedString, maybeFencedLatex, maybeFenced
from known_truth import KnownTruth, asExpression, asExpressions
from defaults import defaults, USE_DEFAULTS, InvalidAssumptions
from context import Context, ContextException
from proof import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from proof import ProofFailure, ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure

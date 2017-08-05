# Core Prove-It constructs required used to construct/verify proofs.

from expression import Expression, Operation, Lambda, Label, Variable, MultiVariable, Literal, DuplicateLiteralError
from expression import Etcetera, Block, safeDummyVar, safeDefaultOrDummyVar, tryDerivation, expressionDepth
from expression import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation
from expression import ExpressionList, ExpressionTensor, NamedExpressions, Composite, compositeExpression, singleOrCompositeExpression, NestedCompositeExpressionError
from known_truth import KnownTruth, asExpression, asExpressions
from defaults import defaults, USE_DEFAULTS, InvalidAssumptions
from context import Context, ContextException
from proof import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from proof import ProofFailure, ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure

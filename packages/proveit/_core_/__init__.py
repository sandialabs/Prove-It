# Core Prove-It constructs required used to construct/verify proofs.

from .expression import Expression, InnerExpr
from .expression import Operation, OperationError, Function, OperationSequence, OperationOverInstances
from .expression import Lambda, LambdaError, ParameterExtractionError, Label, Variable, Literal, DuplicateLiteralError
from .expression import safeDummyVar, safeDefaultOrDummyVar, expressionDepth
from .expression import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation
from .expression import Composite, compositeExpression, singleOrCompositeExpression
from .expression import ExprTuple, ExprTupleError, ExprTensor, NamedExprs, Indexed, IndexedError, Iter, varIter
from .expression import StyleOptions, maybeFencedString, maybeFencedLatex, maybeFenced
from .known_truth import KnownTruth, asExpression, asExpressions
from .defaults import defaults, USE_DEFAULTS, InvalidAssumptions
from .context import Context, ContextException
from .proof import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from .proof import ProofFailure, ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure
#import _context_storage
from ._context_storage import relurl, ContextStorage, StoredSpecialStmt, StoredAxiom, StoredTheorem
#from . import magics#KMR addition 1/7/19

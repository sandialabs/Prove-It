from _core_ import defaults, USE_DEFAULTS, InvalidAssumptions, Context, ContextException
from _core_ import Expression, Operation, Function, OperationSequence, OperationOverInstances
from _core_ import Lambda, LambdaError, ParameterExtractionError, Label, Variable, Literal, DuplicateLiteralError
from _core_ import safeDummyVar, safeDefaultOrDummyVar, expressionDepth
from _core_ import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation, ProofFailure
from _core_ import Composite, compositeExpression, singleOrCompositeExpression
from _core_ import ExprList, ExprTensor, NamedExprs, Indexed, Iter
from _core_ import KnownTruth, asExpression, asExpressions
from _core_ import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from _core_ import ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure
from _core_ import maybeFencedString, maybeFencedLatex, maybeFenced
from relation import TransitiveRelation, TransitiveSequence

# Implies, Forall, and InSet are core concepts that are defined outside of the core.
#from proveit.logic import Implies, Forall, InSet

# These methods are called within the core as convenience methods (not really core concepts)
#from proveit.logic import reduceOperands, defaultEvaluate, evaluateTruth, concludeViaImplication
# `Not` is used for the disprove convenience method (but not really a core concept)
#from proveit.logic import Not
# `Set` is used within the core for displaying assumptions sets and specialization mappings (but not really a core concept)
#from proveit.logic import Set

# register Prove-It specific IPython magic:
# %begin_axioms, %end_axioms, %begin_theorems, %end_theorems, %begin_proof, and %display_assignment
import _core_.magics

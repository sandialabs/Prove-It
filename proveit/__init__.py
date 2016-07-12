from _core_ import defaults, USE_DEFAULTS, storage, Expression, Operation, Lambda, Label, Variable, MultiVariable, Literal, Etcetera, Block, safeDummyVar
from _core_ import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation, ProofFailure
from _core_ import ExpressionList, ExpressionTensor, NamedExpressions, compositeExpression, singleOrCompositeExpression, NestedCompositeExpressionError
from _core_ import beginAxioms, endAxioms, beginTheorems, endTheorems, KnownTruth
from _core_ import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from _core_ import ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure
from _generic_ import BinaryOperation, AssociativeOperation, OperationOverInstances, InstanceSubstitutionException
from _generic_ import maybeFencedString, maybeFencedLatex, maybeFenced

# Implies, Forall, and InSet are core concepts that are defined outside of the core.
from proveit.logic import Implies, Forall, InSet


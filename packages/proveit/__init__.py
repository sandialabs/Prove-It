import sys
if sys.version_info[0] < 3:
    raise Exception("Must use Python 3")

from ._core_ import (
        defaults, USE_DEFAULTS, InvalidAssumptions, Context, 
        ContextException,
        Expression, InnerExpr, expressionDepth,
        Operation, OperationError, Function, OperationSequence, 
        OperationOverInstances, IndexedVar,
        Conditional, 
        Lambda, LambdaApplicationError, ArgumentExtractionError, 
        Label, Variable, Literal, DuplicateLiteralError,
        safeDummyVar, safeDefaultOrDummyVar, 
        MakeNotImplemented, ImproperSubstitution, 
        ScopingViolation, ProofFailure,
        Composite, compositeExpression, singleOrCompositeExpression,
        ExprTuple, ExprTupleError, ExprArray, NamedExprs, Iter, varIter,
        KnownTruth, asExpression, asExpressions,
        Proof, Assumption, Axiom, Theorem, ModusPonens, 
        HypotheticalReasoning, Specialization, Generalization,
        ModusPonensFailure, RelabelingFailure, SpecializationFailure, 
        GeneralizationFailure,
        StyleOptions, maybeFencedString, maybeFencedLatex, maybeFenced)
from .relation import (TransitiveRelation, TransitiveSequence, TransitivityException, 
                       TransRelUpdater)

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
#from . import _core_.magics
from . import magics

def reset():
    '''
    Clear all references to Prove-It information.
    This should make a clean slate w.r.t. Prove-It.
    '''
    Expression._clear_()
    Literal._clear_()
    Operation._clear_()
    KnownTruth._clear_()
    Proof._clear_()
    Context._clear_()
    defaults.reset()
    if hasattr(magics, 'proveItMagic'):
        magics.proveItMagic.reset()
    from proveit._core_._unique_data import clear_unique_data
    clear_unique_data()

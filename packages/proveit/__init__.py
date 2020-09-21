import sys
if sys.version_info[0] < 3:
    raise Exception("Must use Python 3")

from ._core_ import (
        defaults, USE_DEFAULTS, InvalidAssumptions, Context, 
        ContextException,
        Expression, traverse_inner_expressions, used_vars, 
        possibly_free_var_ranges, free_vars, attempt_to_simplify,
        InnerExpr, expressionDepth,
        Operation, IndexedVar, indexed_var, Function, OperationSequence, 
        OperationOverInstances, bundle, unbundle, OperationError,
        Conditional, ConditionalSet,
        Lambda, ParameterCollisionError, DisallowedParameterRelabeling,
        LambdaApplicationError, ArgumentExtractionError, 
        Label, Variable, Literal, DuplicateLiteralError,
        safeDummyVar, safeDummyVars, safeDefaultOrDummyVar, 
        MakeNotImplemented, ImproperReplacement, 
        ProofFailure,
        Composite, compositeExpression, singleOrCompositeExpression,
        ExprTuple, ExprTupleError, extract_var_tuple_indices, 
        ExprArray, NamedExprs, ExprRange, 
        varRange, RangeInstanceError,
        KnownTruth, asExpression, asExpressions,
        Proof, Assumption, Axiom, Theorem, ModusPonens, 
        Deduction, Instantiation, Generalization,
        ModusPonensFailure, InstantiationFailure, GeneralizationFailure,
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

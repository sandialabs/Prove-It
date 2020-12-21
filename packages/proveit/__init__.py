import sys
if sys.version_info[0] < 3:
    raise Exception("Must use Python 3")

from ._core_ import (
        defaults, USE_DEFAULTS, InvalidAssumptions, Theory, 
        TheoryException,
        Expression, traverse_inner_expressions, used_vars, 
        possibly_free_var_ranges, free_vars, attempt_to_simplify,
        InnerExpr, expression_depth,
        Operation, IndexedVar, Function, OperationSequence, 
        OperationOverInstances, bundle, unbundle, OperationError,
        Conditional, ConditionalSet,
        Lambda, ParameterCollisionError, DisallowedParameterRelabeling,
        LambdaApplicationError, ArgumentExtractionError, 
        Label, Variable, Literal, DuplicateLiteralError,
        safe_dummy_var, safe_dummy_vars, safe_default_or_dummy_var, 
        MakeNotImplemented, ImproperReplacement, 
        ProofFailure,
        Composite, composite_expression, single_or_composite_expression,
        ExprTuple, ExprTupleError, extract_var_tuple_indices, 
        ExprArray, NamedExprs, ExprRange, 
        var_range, RangeInstanceError,
        Judgment, as_expression, as_expressions,
        Proof, Assumption, Axiom, Theorem, ModusPonens, 
        Deduction, Instantiation, Generalization,
        ModusPonensFailure, InstantiationFailure, GeneralizationFailure,
        StyleOptions, maybe_fenced_string, maybe_fenced_latex, maybe_fenced)
from .relation import (TransitiveRelation, TransitiveSequence, TransitivityException, 
                       TransRelUpdater)

# Implies, Forall, and InSet are core concepts that are defined outside of the core.
#from proveit.logic import Implies, Forall, InSet

# These methods are called within the core as convenience methods (not really core concepts)
#from proveit.logic import reduce_operands, default_evaluate, evaluate_truth, conclude_via_implication
# `Not` is used for the disprove convenience method (but not really a core concept)
#from proveit.logic import Not
# `Set` is used within the core for displaying assumptions sets and instantiation mappings (but not really a core concept)
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
    Judgment._clear_()
    Proof._clear_()
    Theory._clear_()
    defaults.reset()
    if hasattr(magics, 'prove_it_magic'):
        magics.prove_it_magic.reset()
    from proveit._core_._unique_data import clear_unique_data
    clear_unique_data()

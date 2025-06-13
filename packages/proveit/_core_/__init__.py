# Core Prove-It constructs required used to construct/verify proofs.

from .expression import (
    Expression, traverse_inner_expressions, used_vars, used_literals,
    free_var_ranges, free_vars,
    expression_depth, MakeNotImplemented,
    ImproperReplacement,
    InnerExpr, InnerExprGenerator, generate_inner_expressions,
    Label, Literal, Variable, DuplicateLiteralError,
    safe_dummy_var, safe_dummy_vars, safe_default_or_dummy_var,
    Operation, IndexedVar, Function,
    OperationOverInstances, bundle, unbundle, OperationError,
    Conditional, Lambda,
    ParameterCollisionError, ParameterMaskingError,
    ParameterRelabelingError, LambdaApplicationError, 
    ArgumentExtractionError,
    Composite, composite_expression,
    single_or_composite_expression,
    ExprTuple, ExprTupleError, extract_var_tuple_indices,
    ExprArray, var_array, horiz_var_array, VertExprArray, vert_var_array,
    NamedExprs, ExprRange, var_range, RangeInstanceError,
    simplified_index, simplified_indices,
    StyleOptions, maybe_fenced_string,
    maybe_fenced_latex, maybe_fenced)
from .judgment import Judgment, as_expression, as_expressions
from .defaults import (defaults, USE_DEFAULTS, InvalidAssumptions,
                       SimplificationDirectives)
from .theory import Theory, TheoryException
from .proof import (Proof, Assumption, Axiom, Theorem,
                    BasicDefinition, DefiningProperty, DefinitionExistence, 
                    ModusPonens, Deduction, Instantiation, Generalization)
from .proof import (UnusableProof, ProofFailure, ModusPonensFailure,
                    InstantiationFailure, GeneralizationFailure,
                    UnsatisfiedPrerequisites)
#import _theory_storage
from ._theory_storage import (relurl, TheoryStorage, StoredSpecialStmt,
                              StoredAxiom, StoredTheorem)
# from . import magics#KMR addition 1/7/19

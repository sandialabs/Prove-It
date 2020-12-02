# Core Prove-It constructs required used to construct/verify proofs.

from .expression import (
        Expression, traverse_inner_expressions, used_vars, 
        possibly_free_var_ranges, free_vars, attempt_to_simplify,
        expressionDepth, MakeNotImplemented, 
        ImproperReplacement, 
        InnerExpr,
        Label, Literal, Variable, DuplicateLiteralError,
        safeDummyVar, safeDummyVars, safeDefaultOrDummyVar,
        Operation, IndexedVar, Function, OperationSequence, 
        OperationOverInstances, bundle, unbundle, OperationError, 
        Conditional, ConditionalSet,
        Lambda, ParameterCollisionError, DisallowedParameterRelabeling,
        LambdaApplicationError, ArgumentExtractionError, 
        Composite, compositeExpression, 
        singleOrCompositeExpression, 
        ExprTuple, ExprTupleError, extract_var_tuple_indices,
        ExprArray, NamedExprs, ExprRange, 
        varRange, RangeInstanceError,
        StyleOptions, maybeFencedString, 
        maybeFencedLatex, maybeFenced)
from .judgment import Judgment, asExpression, asExpressions
from .defaults import defaults, USE_DEFAULTS, InvalidAssumptions
from .theory import Theory, TheoryException
from .proof import (Proof, Assumption, Axiom, Theorem, ModusPonens, 
                    Deduction, Instantiation, Generalization)
from .proof import (ProofFailure, ModusPonensFailure, 
                    InstantiationFailure, GeneralizationFailure)
#import _theory_storage
from ._theory_storage import (relurl, TheoryStorage, StoredSpecialStmt, 
                               StoredAxiom, StoredTheorem)
#from . import magics#KMR addition 1/7/19

# Core Prove-It constructs required used to construct/verify proofs.

from .expression import (
        Expression, used_vars, free_var_ranges, free_vars,
        expressionDepth, MakeNotImplemented, 
        ImproperReplacement, 
        InnerExpr,
        Label, Literal, Variable, DuplicateLiteralError,
        safeDummyVar, safeDummyVars, safeDefaultOrDummyVar,
        Operation, IndexedVar, indexed_var, Function, OperationSequence, 
        OperationOverInstances, OperationError, 
        Conditional, 
        Lambda, ParameterCollisionError, InvalidParamVarOccurrence,
        LambdaApplicationError, ArgumentExtractionError, 
        Composite, compositeExpression, 
        singleOrCompositeExpression, 
        ExprTuple, ExprTupleError, extract_indices,
        ExprArray, NamedExprs, ExprRange, 
        varRange, RangeInstanceError,
        StyleOptions, maybeFencedString, 
        maybeFencedLatex, maybeFenced)
from .known_truth import KnownTruth, asExpression, asExpressions
from .defaults import defaults, USE_DEFAULTS, InvalidAssumptions
from .context import Context, ContextException
from .proof import (Proof, Assumption, Axiom, Theorem, ModusPonens, 
                    HypotheticalReasoning, Instantiation, Generalization)
from .proof import (ProofFailure, ModusPonensFailure, 
                    InstantiationFailure, GeneralizationFailure)
#import _context_storage
from ._context_storage import (relurl, ContextStorage, StoredSpecialStmt, 
                               StoredAxiom, StoredTheorem)
#from . import magics#KMR addition 1/7/19

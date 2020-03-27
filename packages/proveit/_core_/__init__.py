# Core Prove-It constructs required used to construct/verify proofs.

from .expression import (
        Expression, InnerExpr, expressionDepth,
        MakeNotImplemented, ImproperSubstitution, 
        ScopingViolation, 
        Label, Literal, Variable, DuplicateLiteralError,
        safeDummyVar, safeDefaultOrDummyVar,
        Operation, IndexedVar, Function, OperationSequence, 
        OperationOverInstances, OperationError, 
        Conditional, 
        Lambda, ParameterCollisionError, LambdaApplicationError, 
        ArgumentExtractionError, 
        Composite, compositeExpression, 
        singleOrCompositeExpression, ExprTuple, ExprTupleError, 
        ExprArray, NamedExprs, Iter, 
        varIter, IterationInstanceError,
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

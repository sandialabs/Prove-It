from proveit import USE_DEFAULTS, Operation, Literal, ExpressionList, compositeExpression
from proveit import BinaryOperation, AssociativeOperation
from proveit.logic.boolean.booleans import TRUE, FALSE, deduceInBool
from quantifiers.existential import Exists, NotExists
from proveit.common import A, B, C, x, y, f, a, b, c, S, xEtc, zEtc

pkg = __package__



def _evaluateBooleanBinaryOperation(operation, baseEvalFn):
    from proveit.logic.equality.theorems import unaryEvaluation, binaryEvaluation
    _x = operation.operands[0]
    _y = operation.operands[1]
    operator = operation.operator
    if (_x == TRUE or _x == FALSE) and (_y == TRUE or _y == FALSE):
        evaluation = baseEvalFn(_x, _y)
    elif (_x == TRUE or _x == FALSE):
        _b = _y.evaluate().rhs
        _c = baseEvalFn(_x, _b).rhs
        dummyVar = _x.safeDummyVar() # var that isn't in _x
        fOp = operation(f, dummyVar)
        fOpSub =  operation.make(operator, ExpressionList(_x, dummyVar))
        evaluation = unaryEvaluation.specialize({fOp:fOpSub, x:_y, a:_b, c:_c}).deriveConclusion().deriveConclusion()
    elif (_y == TRUE or _y == FALSE):
        _a = _x.evaluate().rhs
        _c = baseEvalFn(_a, _y).rhs
        dummyVar = _y.safeDummyVar() # var that isn't in _y
        fOp = operation(f, dummyVar)
        fOpSub = operation.make(operator, ExpressionList(dummyVar, _y))
        evaluation = unaryEvaluation.specialize({fOp:fOpSub, x:_x, a:_a, c:_c}).deriveConclusion().deriveConclusion()
    else:
        xEval = _x.evaluate()
        yEval = _y.evaluate()
        compose(xEval, yEval)
        _a, _b = xEval.rhs, yEval.rhs 
        _c = baseEvalFn(_a, _b).rhs
        fOp = operation(f, (a, b))
        fOpSub = operation.make(operator, ExpressionList(a, b))
        # f(_x, _y) = _c
        evaluation = binaryEvaluation.specialize({fOp:fOpSub, x:_x, y:_y, a:_a, b:_b, c:_c}).deriveConclusion().deriveConclusion()
    return evaluation    

"""
def _evaluate(expr, evalFn):
    '''
    Lookup or perform (via evalFn) and store an evaluation of the given boolean expression.
    '''
    if expr in self.evalLookup:
        return self.eval[self.evalLookup[expr]]
    else:
        evaluation = evalFn()
        if evaluation != None:
            self.evalLookup[expr] = len(self.eval)
            self.eval.append(evaluation)
            if evaluation.qed().statement.getRegisteredVar() == None:
                booleans.register('eval', len(booleans.eval)-1)            
        return evaluation
"""

def _evaluate(expr, evalFn):
    '''
    Simple version for now.  The future plan is to store/unnamed unnamed theorems -- anything
    proven that has no free variables or assumptions.
    '''
    return evalFn()


from proveit import Operation

def isIrreducibleValue(expr):
    return (hasattr(expr, 'isIrreducibleValue') and expr.isIrreducibleValue())

class Evaluatable(Operation):
    # Maps Evaluatables to equations with the Evaluatable on the lhs and
    # an irreducable value on the rhs.
    # Populated in evaluate and also, for axioms/theorems, automatically
    # populated in Equals.deriveSideEffects (proveit.logic.equality.equals).
    evaluations = dict()
    
    def __init__(self, operator, operands):
        Operation.__init__(self, operator, operands)
        
    def evaluate(self):
        from proveit.lambda_map import globalRepl
        from proveit.logic import Equals
        self.loadBaseEvaluations()
        # See if the Evaluatable already has a proven evaluation
        if self in Evaluatable.evaluations:
            return Evaluatable.evaluations[self] # found existing evaluation
        # Any of the operands that are not irreducible values must be replaced with their evaluation
        expr = self
        for operand in self.operands:
            if not isIrreducibleValue(operand):
                # the operand is not an irreducible value so it must be evaluated
                operandEval = operand.evaluate()
                if not isIrreducibleValue(operandEval.rhs):
                    raise EvaluationError('Evaluations expected to be irreducible values')
                expr = operandEval.substitution(globalRepl(expr, operand)).rhs
        for operand in expr.operands:
            if not isIrreducibleValue(operand.isIrreducibleValue()):
                raise EvaluationError('All operands should not be irreducible values')
        evaluation = Equals(self, expr._baseEvaluate().rhs).prove()
        # store it in the evaluations dictionary for next time
        Evaluatable.evaluations[self] = evaluation
        return evaluation
    
    def loadBaseEvaluations(self):
        '''
        Import the base evaluations so they will automatically
        populate the evaluations dictionary for evaluating base-level expressions.
        This is specific to each kind of Evaluatable and must be overridden.
        '''
        raise NotImplementedError('_baseEvaluate must be implemented to evaluate the Evaluatable when all operands are irreducible values')  
                
    def _baseEvaluate(self):
        '''
        Evaluate the Evaluatable when all operands are irreducible values.
        This is specific to each kind of Evaluatable and must be overridden.
        '''
        raise NotImplementedError('_baseEvaluate must be implemented to evaluate the Evaluatable when all operands are irreducible values')
        
        
class EvaluationError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

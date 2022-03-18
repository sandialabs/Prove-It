from proveit import Operation, Literal, equality_prover
from proveit.logic import Equals

class Norm(Operation):
    '''
    We define the norm of a vector to be the square root of
    its inner product with itself.  More generally, norms map vectors 
    to non-negative real values and obey:
        ‖a v‖ = |a| ‖v‖
        ‖u + v‖ ≤ ‖u‖ + ‖v‖
    Theorems using these only these general norm properties could 
    generalize the Norm operator (via literal generalization) for 
    expanded uses, but our literal operator will be defined as the
    InnerProd.
    '''

    # operator of the Norm operation.
    _operator_ = Literal(string_format='Abs', theory=__file__)
    
    def __init__(self, operand, *, styles=None):
        Operation.__init__(self, Norm._operator_, operand, 
                           styles=styles)
    
    def string(self, **kwargs):
        return '||' + self.operand.string() + '||'

    def latex(self, **kwargs):
        return r'\left \|' + self.operand.latex() + r'\right \|'

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False, 
                               **defaults_config):
        if must_evaluate and hasattr(self.operand, 'compute_norm'):
            return self.evaluation()
        return Operation.shallow_simplification(self)

    @equality_prover('computed', 'compute')
    def computation(self, **defaults_config):
        if hasattr(self.operand, 'compute_norm'):
            # If the operand has a 'deduce_norm' method, use
            # it in an attempt to evaluate the norm.
            return self.operand.compute_norm()
        # If there is no 'compute_norm' method, see if there is a
        # known evaluation.
        return self.evaluation()
    
    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        if hasattr(self.operand, 'compute_norm'):
            # If the operand has a 'deduce_norm' method, use
            # it in an attempt to evaluate the norm.
            return self.computation().inner_expr().rhs.evaluate()
        return Operation.evaluation(self)

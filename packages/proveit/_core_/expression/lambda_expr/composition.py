from proveit.decorators import equality_prover
from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class Composition(Operation):
    '''
    A Composition is an Expression that represents the composition
    of functions (lambda maps).
    '''
    
    # operator of the Add operation
    _operator_ = Literal(string_format='o', latex_format=r'\circ', 
                         theory=__file__)
    
    def __init__(self, *maps, styles=None):
        Operation.__init__(self, Composition._operator_, maps, 
                           styles=styles)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        from proveit.core_expr_types.lambda_maps import unary_composition, binary_composition
        from proveit import Lambda, f, g, x, y, z
        if self.operands.is_single() and isinstance(self.operand, Lambda):
            return unary_composition.instantiate({f:self.operand, x:self.operand.parameter, y:self.operand.parameter})
            
        elif self.operands.is_double() and isinstance(self.operands[1], Lambda):
            return binary_composition.instantiate({f:self.operands[0], x:self.operands[0].parameter, g:self.operands[1], y:self.operands[1].parameter, z:self.operands[1].parameter})

        else:
            return Operation.shallow_simplification(self)
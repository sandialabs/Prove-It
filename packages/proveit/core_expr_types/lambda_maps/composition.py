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

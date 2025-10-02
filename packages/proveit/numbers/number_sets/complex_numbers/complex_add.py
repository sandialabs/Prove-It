from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class ComplexAdd(Operation):
    '''
    Addition of two complex numbers.
    '''
    
    _operator_ = Literal(string_format='+_C', 
                         latex_format=r'+_{\mathbb{C}}',
                         theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, ComplexAdd._operator_, (a, b),
                           styles=styles)

from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class RealAdd(Operation):
    '''
    Addition of two real numbers.
    '''
    
    _operator_ = Literal(string_format='+_R', 
                         latex_format=r'+_{\mathbb{R}}',
                         theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, RealAdd._operator_, (a, b),
                           styles=styles)

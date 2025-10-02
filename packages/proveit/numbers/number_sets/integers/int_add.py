from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class IntAdd(Operation):
    '''
    Addition of two integers.
    '''
    
    _operator_ = Literal(string_format='+_Z', 
                         latex_format=r'+_{\mathbb{Z}}',
                         theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, IntAdd._operator_, (a, b),
                           styles=styles)

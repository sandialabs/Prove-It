from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class RealMult(Operation):
    '''
    Multiplication of two real numbers.
    '''

    _operator_ = Literal(string_format='*_R', 
                         latex_format=r'*_{\mathbb{R}}',
                         theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, RealMult._operator_, (a, b),
                           styles=styles)


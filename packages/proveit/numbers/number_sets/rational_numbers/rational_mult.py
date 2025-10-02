from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal

class RationalMult(Operation):
    '''
    Multiplication of two rational numbers.
    '''

    _operator_ = Literal(string_format='*_Q', 
                         latex_format=r'*_{\mathbb{Q}}',
                         theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, RationalMult._operator_, (a, b),
                           styles=styles)


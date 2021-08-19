from proveit import Operation, Literal
from proveit.numbers import Neg

class VecNeg(Operation):
    '''
    The VecAdd operation is the default for the addition of vectors
    in a vector space.
    '''
    
    _operator_ = Literal(string_format='-', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        Operation.__init__(self, operands, styles=styles)

    def string(self, **kwargs):
        return Neg.string(self, **kwargs)

    def latex(self, **kwargs):
        return Neg.latex(self, **kwargs)
    
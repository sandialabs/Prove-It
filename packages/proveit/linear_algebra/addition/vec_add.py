from proveit import Literal
from proveit.abstract_algebra import GroupAdd

class VecAdd(GroupAdd):
    '''
    The VecAdd operation is the default for the addition of vectors
    in a vector space.
    '''
    
    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        GroupAdd.__init__(self, VecAdd._operator_,
                          operands, styles=styles)

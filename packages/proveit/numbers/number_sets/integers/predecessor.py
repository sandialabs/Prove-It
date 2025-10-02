from proveit import Function, Literal
from .integer import IntegerSet
from proveit.numbers import Integer

class IntPredecessor(Function):
    '''
    Represents the predecessor function for integers, the inverse of
    the successor function.
    '''

    # operator of the Add operation FOR NATURAL NUMBERS ONLY
    _operator_ = Literal(string_format='P_{%s}'%Integer.string_format, 
                         latex_format='P_{%s}'%Integer.latex_format, 
                         theory=__file__)
    
    def __init__(self, int_number, *, styles=None):
        r'''
        Predecessor of an integer (addition by 1).
        '''
        Function.__init__(self, IntPredecessor._operator_, int_number, 
                           styles=styles)

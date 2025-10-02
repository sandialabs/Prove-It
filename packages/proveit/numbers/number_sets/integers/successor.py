from proveit import Function, Literal
from .integer import IntegerSet
from proveit.numbers import Integer

class IntSuccessor(Function):
    '''
    Represents the successor function (adding 1) for all integers 
    (positive and negative).
    '''

    # operator of the Add operation FOR NATURAL NUMBERS ONLY
    _operator_ = Literal(string_format='S_{%s}'%Integer.string_format, 
                         latex_format='S_{%s}'%Integer.latex_format, 
                         theory=__file__)
    
    def __init__(self, int_number, *, styles=None):
        r'''
        Successor of an integer (addition by 1).
        '''
        Function.__init__(self, IntSuccessor._operator_, int_number, 
                           styles=styles)

from proveit import Function, Literal
from proveit.numbers import Natural

class NatSuccessor(Function):
    '''
    Represents the successor function for all natural numbers (adding 1).
    '''

    # operator of the Add operation FOR NATURAL NUMBERS ONLY
    _operator_ = Literal(string_format='S_{%s}'%Natural.string_format, 
                         latex_format='S_{%s}'%Natural.latex_format, 
                         theory=__file__)
    
    def __init__(self, nat_number, *, styles=None):
        r'''
        Successor of a natural number (addition by 1).
        '''
        Function.__init__(self, NatSuccessor._operator_, nat_number, 
                           styles=styles)
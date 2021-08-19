from proveit import Function, Literal

class Rings(Function):
    '''
    A Rings expression denotes the class of sets that are rings
    under particular "addition" and "multiplication" operations.
    '''
    
    _operator_ = Literal(
            string_format=r'Rings', latex_format=r'\textrm{Rings}',
            theory=__file__)
    
    def __init__(self, add_operator, mult_operator, *, styles=None):
        Function.__init__(self, Rings._operator_, 
                          (add_operator, mult_operator), 
                          styles=styles)

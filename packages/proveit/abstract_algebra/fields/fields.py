from proveit import Function, Literal

class Fields(Function):
    '''
    A Fields expression denotes the class of sets that are rings
    under particular "addition" and "multiplication" operations.
    '''
    
    _operator_ = Literal(
            string_format=r'Fields', latex_format=r'\textrm{Fields}',
            theory=__file__)
    
    def __init__(self, add_operator, mult_operator, *, styles=None):
        Function.__init__(self, Fields._operator_, 
                          (add_operator, mult_operator), 
                          styles=styles)

    @property
    def is_proper_class(self):
        '''
        This is a proper class. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

from proveit import Function, Literal

class Groups(Function):
    '''
    A Groups expression denotes the class of sets that are groups
    under a particular group operation.
    '''
    
    _operator_ = Literal(
            string_format=r'Groups', latex_format=r'\textrm{Groups}',
            theory=__file__)
    
    def __init__(self, group_operator, *, styles=None):
        Function.__init__(self, Groups._operator_, group_operator, 
                          styles=styles)

    @property
    def is_proper_class(self):
        '''
        This is a proper class. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

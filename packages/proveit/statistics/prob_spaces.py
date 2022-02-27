from proveit import Literal

class ProbSpaces(Literal):
    '''
    ProbSpaces denotes the class of all probability spaces.
    '''
    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='ProbSpaces',
            latex_format=r'\textrm{ProbSpaces}',
            styles=styles)
    
    @property
    def is_proper_class(self):
        '''
        Probability spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

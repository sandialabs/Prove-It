from proveit import Literal

class SampleSpacesClass(Literal):
    '''
    SampleSpaces denotes the class of all sample spaces of
    probability spaces.  A sample space represents the set of all 
    possible outcomes of an experiment.
    '''
    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='SampleSpaces',
            latex_format=r'\textrm{SampleSpaces}',
            styles=styles)
    
    @property
    def is_proper_class(self):
        '''
        Samples spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

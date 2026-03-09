from proveit import Literal, ClassMembership

class IsSampleSpace(ClassMembership):
    '''
    A sample space represents the set of all 
    possible outcomes of an experiment.
    '''

    _operator_ = Literal(
            string_format=r'IsSampleSpace', latex_format=r'\textrm{IsSampleSpace}',
            theory=__file__)
    
    def __init__(self, space, *, styles=None):
        ClassMembership.__init__(self, IsSampleSpace._operator_, 
                                 space, styles=styles)

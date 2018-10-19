from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import n, x, AA

class Intersect(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='intersect', latexFormat=r'\cap', context=__file__)    
    
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        Operation.__init__(self, Intersect._operator_, operands)
    
    def membershipObject(self, element):
        from intersect_membership import IntersectMembership
        return IntersectMembership(element, self)

    def nonmembershipObject(self, element):
        from intersect_membership import IntersectNonmembership
        return IntersectNonmembership(element, self)

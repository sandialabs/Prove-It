from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import n, x, AA
        
class Union(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='union', latexFormat=r'\cup', context=__file__)    
    
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        Operation.__init__(self, Union._operator_, operands)

    def membershipObject(self, element):
        from union_membership import UnionMembership
        return UnionMembership(element, self)

    def nonmembershipObject(self, element):
        from union_membership import UnionNonmembership
        return UnionNonmembership(element, self)

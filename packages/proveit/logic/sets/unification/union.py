from proveit import Literal, Operation, USE_DEFAULTS
from proveit import n, x


class Union(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(
        string_format='union',
        latex_format=r'\cup',
        theory=__file__)

    def __init__(self, *operands, styles=None):
        '''
        Union any number of sets: A union B union C
        '''
        Operation.__init__(self, Union._operator_, operands,
                           styles=styles)

    def membership_object(self, element):
        from .union_membership import UnionMembership
        return UnionMembership(element, self)

    def nonmembership_object(self, element):
        from .union_membership import UnionNonmembership
        return UnionNonmembership(element, self)

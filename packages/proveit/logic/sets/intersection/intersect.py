from proveit import Literal, Operation, USE_DEFAULTS
from proveit import n, x


class Intersect(Operation):
    # operator of the Intersect operation
    _operator_ = Literal(
        string_format='intersect',
        latex_format=r'\cap',
        theory=__file__)

    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        Operation.__init__(self, Intersect._operator_, operands)

    def membership_object(self, element):
        from .intersect_membership import IntersectMembership
        return IntersectMembership(element, self)

    def nonmembership_object(self, element):
        from .intersect_membership import IntersectNonmembership
        return IntersectNonmembership(element, self)

from proveit import Literal, Operation, USE_DEFAULTS
from proveit import x, A, B


class Difference(Operation):
    # operator of the Difference operation
    _operator_ = Literal(string_format='-', theory=__file__)

    def __init__(self, A, B):
        Operation.__init__(self, Difference._operator_, [A, B])
    
    def membership_object(self, element):
        from .difference_membership import DifferenceMembership
        return DifferenceMembership(element, self)

    def nonmembership_object(self, element):
        from .difference_membership import DifferenceNonmembership
        return DifferenceNonmembership(element, self)

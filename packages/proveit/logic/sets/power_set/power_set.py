from proveit import Literal, Function, USE_DEFAULTS
from proveit._common_ import n, x


class PowerSet(Function):
    # operator of the Intersect operation
    _operator_ = Literal(
        string_format='power_set',
        latex_format=r'\mathbb{P}',
        theory=__file__)

    def __init__(self, operand):
        '''
        Power set of a set.
        '''
        Function.__init__(self, PowerSet._operator_, operand)

    """
    # Needs implementation

    def membership_object(self, element):
        from .powerset_membership import PowerSetMembership
        return PowerSetMembership(element, self)

    def nonmembership_object(self, element):
        from .powerset_membership import PowerSetNonmembership
        return PowerSetNonmembership(element, self)
    """

from proveit import Literal, Function, USE_DEFAULTS
from proveit import n, x


class PowerSet(Function):
    # operator for the PowerSet function
    _operator_ = Literal(
        string_format='power_set',
        latex_format=r'\mathcal{P}',
        theory=__file__)

    def __init__(self, operand, *, styles=None):
        '''
        Power set of a set.
        '''
        Function.__init__(self, PowerSet._operator_, operand,
                          styles=styles)

    """
    # Needs implementation

    def membership_object(self, element):
        from .powerset_membership import PowerSetMembership
        return PowerSetMembership(element, self)

    def nonmembership_object(self, element):
        from .powerset_membership import PowerSetNonmembership
        return PowerSetNonmembership(element, self)
    """

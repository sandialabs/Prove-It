from proveit import Literal, Function, USE_DEFAULTS
from proveit._common_ import n, x
        
class PowerSet(Function):
    # operator of the Intersect operation
    _operator_ = Literal(stringFormat='power_set', latexFormat=r'\mathbb{P}', theory=__file__)    
    
    def __init__(self, operand):
        '''
        Power set of a set.
        '''
        Function.__init__(self, PowerSet._operator_, operand)
    
    """
    # Needs implementation
    
    def membershipObject(self, element):
        from .powerset_membership import PowerSetMembership
        return PowerSetMembership(element, self)

    def nonmembershipObject(self, element):
        from .powerset_membership import PowerSetNonmembership
        return PowerSetNonmembership(element, self)
    """

from proveit import prover
import proveit
from proveit.logic import Equals, NotEquals
from proveit import USE_DEFAULTS, maybe_fenced_string
from proveit import a, x, y
from proveit.numbers.number_sets.number_set import NumberSet


class RealSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Real', r'\mathbb{R}',
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .real_membership import RealMembership    
        return RealMembership(element)


class RealNonZeroSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonZero', r'\mathbb{R}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonZeroMembership    
        return RealNonZeroMembership(element)


class RealPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealPos', r'\mathbb{R}^+', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealPosMembership    
        return RealPosMembership(element)


class RealNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNeg', r'\mathbb{R}^-', 
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNegMembership    
        return RealNegMembership(element)


class RealNonNegSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonNeg', r'\mathbb{R}^{\ge 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonNegMembership    
        return RealNonNegMembership(element)


class RealNonPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RealNonPos', r'\mathbb{R}^{\le 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .real_membership import RealNonPosMembership    
        return RealNonPosMembership(element)


if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from . import (
        int_within_real,
        nat_within_real,
        nat_pos_within_real,
        nat_pos_within_real_pos,
        nat_within_real_nonneg,
        nat_pos_within_real_nonneg,
        rational_within_real,
        rational_nonzero_within_real_nonzero,
        rational_pos_within_real_pos,
        rational_neg_within_real_neg,
        rational_nonneg_within_real_nonneg,
        rational_nonpos_within_real_nonpos,
        real_pos_within_real,
        real_pos_within_real_nonzero,
        real_pos_within_real_nonneg,
        real_neg_within_real,
        real_neg_within_real_nonzero,
        real_neg_within_real_nonpos,
        real_nonneg_within_real,
        real_nonpos_within_real)

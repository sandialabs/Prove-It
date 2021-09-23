import proveit
from proveit import prover, maybe_fenced_string
from proveit import q
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership


class RationalSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Rational', r'\mathbb{Q}',
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .rational_membership import RationalMembership    
        return RationalMembership(element, self)


class RationalNonZeroSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonZero', r'\mathbb{Q}^{\neq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonZeroMembership    
        return RationalNonZeroMembership(element)


class RationalPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalPos', r'\mathbb{Q}^+',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalPosMembership    
        return RationalPosMembership(element)


class RationalNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNeg', r'\mathbb{Q}^-',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNegMembership    
        return RationalNegMembership(element)


class RationalNonNegSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonNeg', r'\mathbb{Q}^{\geq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonNegMembership    
        return RationalNonNegMembership(element)


class RationalNonPosSet(NumberSet):

    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'RationalNonPos', r'\mathbb{Q}^{\leq 0}',
                           theory=__file__, styles=styles, 
                           fence_when_forced=True)

    def membership_object(self, element):
        from .rational_membership import RationalNonPosMembership    
        return RationalNonPosMembership(element)


if proveit.defaults.automation:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for
    # the first time, but fine after that.
    from . import (nat_within_rational, 
                   int_within_rational,
                   nonzero_int_within_rational_nonzero,
                   nat_within_rational_nonneg,
                   nat_pos_within_rational_pos,
                   neg_int_within_rational_neg,
                   nonpos_int_within_rational_nonpos,
                   rational_nonzero_within_rational,
                   rational_pos_within_rational,
                   rational_neg_within_rational,
                   rational_nonneg_within_rational,
                   rational_nonpos_within_rational,
                   rational_pos_within_rational_nonzero,
                   rational_neg_within_rational_nonzero,
                   rational_pos_within_rational_nonneg,
                   rational_neg_within_rational_nonpos,
                   zero_is_rational)

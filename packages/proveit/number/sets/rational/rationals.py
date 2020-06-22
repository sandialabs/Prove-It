from proveit import USE_DEFAULTS, maybeFencedString
from proveit.logic import Membership
from proveit.number.sets.number_set import NumberSet

class RationalsSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'Rationals', r'\mathbb{Q}', context=__file__)

    def deduceMembershipInBool(self, member):
        from ._theorems_ import xInRationalsInBool
        from proveit._common_ import x
        return xInRationalsInBool.specialize({x:member})

class RationalsPosSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsPos', r'\mathbb{Q}^+', context=__file__)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member):
        from ._theorems_ import xInRationalsPosInBool
        from proveit._common_ import x
        return xInRationalsPosInBool.specialize({x:member})

class RationalsNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsNeg', r'\mathbb{Q}^-', context=__file__)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member):
        from ._theorems_ import xInRationalsNegInBool
        from proveit._common_ import x
        return xInRationalsNegInBool.specialize({x:member})

class RationalsNonNegSet(NumberSet):

    def __init__(self):
        NumberSet.__init__(self, 'NaturalsNonNeg', r'\mathbb{Q}^{\geq 0}', context=__file__)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if forceFence=True (nested exponents is an example of when fencing must be forced)
        kwargs['fence'] = kwargs['forceFence'] if 'forceFence' in kwargs else False
        return maybeFencedString(inner_str, **kwargs)

    def deduceMembershipInBool(self, member):
        from ._theorems_ import xInRationalsNonNegInBool
        from proveit._common_ import x
        return xInRationalsNonNegInBool.specialize({x:member})

try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import (rationalsInReals,
                             rationalsPosInRationals,
                             rationalsNegInRationals, 
                             rationalsNonNegInRationals,
                             rationalsPosInRationalsNonNeg
                             zeroInRationals)
except:
    pass

from proveit import USE_DEFAULTS
from proveit._common_ import a
from proveit.number.sets.number_set import NumberSet

class IntegerSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Integers', r'\mathbb{Z}', context=__file__)

    def deduceInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from ._theorems_ import inIntsIsBool
        return inIntsIsBool.specialize({a:element}, assumptions=assumptions)
    
    def deduceNotInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from ._theorems_ import notInIntsIsBool
        return notInIntsIsBool.specialize({a:element}, assumptions=assumptions)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInIntsInBool
        from proveit._common_ import x
        return xInIntsInBool.specialize({x:member}, assumptions=assumptions)

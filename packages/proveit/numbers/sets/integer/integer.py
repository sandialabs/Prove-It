from proveit import USE_DEFAULTS
from proveit._common_ import a
from proveit.numbers.sets.number_set import NumberSet

class IntegerSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Integer', r'\mathbb{Z}', theory=__file__)
    
    def membershipSideEffects(self, judgment):
        '''
        Yield side-effects when proving 'n in NaturalPos' for a given n.
        '''
        member = judgment.element
        yield lambda assumptions : self.deduceMemberInRational(member, assumptions)
    
    def deduceInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from ._theorems_ import inIntsIsBool
        return inIntsIsBool.instantiate({a:element}, assumptions=assumptions)
    
    def deduceNotInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from ._theorems_ import notInIntsIsBool
        return notInIntsIsBool.instantiate({a:element}, assumptions=assumptions)

    def deduceMembershipInBool(self, member, assumptions=USE_DEFAULTS):
        from ._theorems_ import xInIntInBool
        from proveit._common_ import x
        return xInIntInBool.instantiate({x:member}, assumptions=assumptions)

    def deduceMemberInRational(self, member, assumptions=USE_DEFAULTS):
        from proveit.numbers.sets.rational._theorems_ import intInRational
        return intInRational.deriveSupersetMembership(member, assumptions)
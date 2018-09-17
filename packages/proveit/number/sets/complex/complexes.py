from proveit import USE_DEFAULTS
from proveit._common_ import a
from proveit.number.sets.number_set import NumberSet

class ComplexSet(NumberSet):
    def __init__(self):
        NumberSet.__init__(self, 'Complexes', r'\mathbb{C}', context=__file__)

    def deduceInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from theorems import inComplexesIsBool
        return inComplexesIsBool.specialize({a:element}, assumptions)
    
    def deduceNotInSetIsBool(self, element, assumptions=USE_DEFAULTS):
        from theorems import notInComplexesIsBool
        return notInComplexesIsBool.specialize({a:element}, assumptions)
    

try:
    # Import some fundamental axioms and theorems without quantifiers.
    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
    from ._theorems_ import realsInComplexes, realsPosInComplexes, realsNegInComplexes, intsInComplexes, natsInComplexes
except:
    pass

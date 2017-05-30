from proveit import Literal

class IntegerSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'Integers', r'\mathbb{Z}', context=__file__)

    def deduceInSetIsBool(self, element):
        from integer.theorems import inIntsIsBool
        return inIntsIsBool.specialize({a:element})
    
    def deduceNotInSetIsBool(self, element):
        from integer.theorems import notInIntsIsBool
        return notInIntsIsBool.specialize({a:element})

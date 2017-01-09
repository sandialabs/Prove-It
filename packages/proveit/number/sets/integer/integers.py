from proveit import Literal

class IntegerSet(Literal):
    def __init__(self, pkg):
        Literal.__init__(self, pkg, 'Integers', r'\mathbb{Z}')

    def deduceInSetIsBool(self, element):
        from integer.theorems import inIntsIsBool
        return inIntsIsBool.specialize({a:element})
    
    def deduceNotInSetIsBool(self, element):
        from integer.theorems import notInIntsIsBool
        return notInIntsIsBool.specialize({a:element})
    
Integers = IntegerSet(__package__)

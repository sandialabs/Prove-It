from proveit import Literal
from proveit.common import a

class ComplexSet(Literal):
    def __init__(self):
        Literal.__init__(self, 'Integers', r'\mathbb{Z}', context=__file__)

    def deduceInSetIsBool(self, element):
        from theorems import inComplexesIsBool
        return inComplexesIsBool.specialize({a:element})
    
    def deduceNotInSetIsBool(self, element):
        from theorems import notInComplexesIsBool
        return notInIntsIsBool.specialize({a:element})
    
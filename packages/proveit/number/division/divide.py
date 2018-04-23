from proveit import Literal, Operation

class Divide(Operation):
    # operator of the Add operation
    _operator_ = Literal(stringFormat='/', latexFormat= r'\div', context=__file__)    
    
    def __init__(self, operandA, operandB):
        r'''
        Divide two operands.
        '''
        Operation.__init__(self, Divide._operator_, [operandA, operandB])

    def _closureTheorem(self, numberSet):
        import theorems
        if numberSet == Reals:
            return theorems.divideRealClosure
        elif numberSet == RealsPos:
            return theorems.divideRealPosClosure
        elif numberSet == Complexes:
            return theorems.divideComplexClosure

    def _notEqZeroTheorem(self):
        import complex.theorems
        return complex.theorems.divideNotEqZero

class IrreducibleValue:
    def __init__(self):
        pass
    
    def evaluate(self):
        '''
        IrreducibleValues evaluate to themselves.
        '''
        from proveit.logic import Equals
        return Equals(self, self).prove()
    
    def evalEquality(self, otherIrreducible):
        '''
        Returns the evaluation of the equality between this irreducible
        value and the other irreducible value, if it is well-defined.
        '''
        raise NotImplementedError("evalEquality method must be implemented by IrreducibleValue objects")

    def notEqual(self, otherIrreducible):
        '''
        Attempt to prove that this irreducible values is not equal to
        the other irreducible value, returning the KnownTruth.
        '''
        raise NotImplementedError("notEqual method must be implemented by IrreducibleValue objects")
        
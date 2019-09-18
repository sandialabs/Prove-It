'''
The evaluation of an expression (see the evaluate method
of Expression) should reduce to an IrreducibleValue --
a value that cannot be reduced to anything more fundamental.
Classes used to represent expressions that are irreducible
(TRUE, FALSE, basic numbers, etc) should inherit from
IrreducibleValue.
'''

from proveit import USE_DEFAULTS

class IrreducibleValue:
    def __init__(self):
        pass
    
    def irreducibleValue(self):
        return True
    
    def evaluation(self):
        '''
        IrreducibleValues evaluate to themselves.
        '''
        from proveit.logic import Equals
        return Equals(self, self).prove()
    
    def evalEquality(self, otherIrreducible, assumptions=USE_DEFAULTS):
        '''
        Returns the evaluation of the equality between this irreducible
        value and the other irreducible value, if it is well-defined.
        '''
        raise NotImplementedError("evalEquality method must be implemented by IrreducibleValue objects")

    def notEqual(self, otherIrreducible, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove that this irreducible values is not equal to
        the other irreducible value, returning the KnownTruth.
        '''
        raise NotImplementedError("notEqual method must be implemented by IrreducibleValue objects")

def isIrreducibleValue(expr):
    if hasattr(expr, 'irreducibleValue'):
        return expr.irreducibleValue()
    return False

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
    
    def irreducible_value(self):
        return True
    
    def evaluation(self):
        '''
        IrreducibleValues evaluate to themselves.
        '''
        from proveit.logic import Equals
        return Equals(self, self).prove()
    
    def eval_equality(self, other_irreducible, assumptions=USE_DEFAULTS):
        '''
        Returns the evaluation of the equality between this irreducible
        value and the other irreducible value, if it is well-defined.
        '''
        raise NotImplementedError("eval_equality method must be implemented by IrreducibleValue objects")

    def not_equal(self, other_irreducible, assumptions=USE_DEFAULTS):
        '''
        Attempt to prove that this irreducible values is not equal to
        the other irreducible value, returning the Judgment.
        '''
        raise NotImplementedError("not_equal method must be implemented by IrreducibleValue objects")

def is_irreducible_value(expr):
    if hasattr(expr, 'irreducible_value'):
        return expr.irreducible_value()
    return False

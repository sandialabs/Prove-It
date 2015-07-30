from eqOps import Equals

class Equation:
    '''
    Equation wraps an Equals expression, A=B, that can be updated via
    new equations that involve A or B, deriving each new equation from
    the previous equations.
    '''
    def __init__(self, eqn):
        '''
        Initialize the Equation with an Equals expression.
        '''
        if not isinstance(eqn, Equals):
            raise EquationException('Equation must be initialized with an Equals expression')
        self.eqn = eqn
    
    def update(self, next_eqn):
        '''
        Update the old equation via next_eqn to a new equation that is
        derived from the old equation and next_eqn.  This new equation
        is then stored as "the equation" and returned.  For example, if 
        the old equation is A=B and next_eqn is B=C, then update derives, 
        stores (ready for the next update), and returns A=C.
        '''
        if not isinstance(next_eqn, Equals):
            raise EquationException('Equation may only be updated with an Equals expression')
        self.eqn = self.eqn.applyTransitivity(next_eqn).check({self.eqn, next_eqn})
        return self.eqn
    
    def prove(self, assumptions=frozenset()):
        '''
        Forwards this prove "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.eqn.prove(assumptions)
        return self

    def qed(self, filename):
        '''
        Forwards this qed "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.eqn.qed(filename)
        return self.eqn

class EquationException(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

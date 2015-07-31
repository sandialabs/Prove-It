from eqOps import Equals

class Equation:
    '''
    Equation wraps an Equals expression, A=B, that can be updated via
    new equations that involve A or B, deriving each new equation from
    the previous equations.
    '''
    def __init__(self, eqExpr):
        '''
        Initialize the Equation with an Equals expression.
        '''
        if not isinstance(eqExpr, Equals):
            raise EquationException('Equation must be initialized with an Equals expression')
        self.eqExpr = eqExpr
    
    def update(self, nextEqExpr):
        '''
        Update the old equation via nextEqExpr to a new equation that is
        derived from the old equation and nextEqExpr.  This new equation
        is then stored as "the equation" and returned.  For example, if 
        the old equation is A=B and nextEqExpr is B=C, then update derives, 
        stores (ready for the next update), and returns A=C.
        '''
        if not isinstance(nextEqExpr, Equals):
            raise EquationException('Equation may only be updated with an Equals expression')
        self.eqExpr = self.eqExpr.applyTransitivity(nextEqExpr).check({self.eqExpr, nextEqExpr})
        return self.eqExpr
    
    def prove(self, assumptions=frozenset()):
        '''
        Forwards this prove "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.eqExpr.prove(assumptions)
        return self

    def qed(self, filename):
        '''
        Forwards this qed "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.eqExpr.qed(filename)
        return self.eqExpr

class EquationException(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

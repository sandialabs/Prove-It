from eqOps import Equals

class Equation:
    '''
    Equation wraps an Equals expression, A=B, that can be updated via
    new equations that involve A or B, deriving each new equation from
    the previous equations.
    '''
    def __init__(self, *equationExpressions):
        '''
        Initialize the Equation with any number of Equals expression,
        a starting expression a subsequent updates.  If there are no
        expressions given, the starting expression will be the first update.
        '''
        self.eqExpr = None
        for expr in equationExpressions:
            self.update(expr)
    
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
        if self.eqExpr is None:
            self.eqExpr = nextEqExpr
        else:
            self.eqExpr = self.eqExpr.applyTransitivity(nextEqExpr).checked({self.eqExpr, nextEqExpr})
        return self.eqExpr
    
    def proven(self, assumptions=frozenset()):
        '''
        Forwards this proven "command" to the wrapped equation Expression but
        then returns this Equation wrapper.
        '''
        self.eqExpr.proven(assumptions)
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

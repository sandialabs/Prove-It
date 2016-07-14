import hashlib, os

class Defaults:
    def __init__(self):
        self.assumptions = frozenset()
    
    def checkedAssumptions(self, assumptions):
        '''
        If the given assumptions is None, return the default;
        otherwise return the given assumptions after checking
        that it is an iterable collection of Expressions.
        '''
        if assumptions is None:
            return self.assumptions
        self._checkAssumptions(assumptions)
        return assumptions
    
    def _checkAssumptions(self, assumptions):
        '''
        Check that the given assumptions are valid -- an iterable
        collection of Expressions.
        '''
        from expression.expr import Expression
        for assumption in assumptions:
            if not isinstance(assumption, Expression):
                raise TypeError('The assumptions must be an iterable collection of Expression objects')
        
    def __setattr__(self, attr, value):
        '''
        When setting the assumptions, check that they are valid.
        '''
        if attr == 'assumptions' and hasattr(self, attr):
            self._checkAssumptions(value)
        self.__dict__[attr] = value             

class InvalidAssumptions:
    def __init__(self):
        pass
    def __str__(self):
        return 'The assumptions must be an iterable collection of Expression objects'
        
# USE_DEFAULTS is used to indicate that default assumptions
# should be used.  This value is simply None, but with
# USE_DEFAULTS, it is more explicit in the code.
USE_DEFAULTS = None

defaults = Defaults()

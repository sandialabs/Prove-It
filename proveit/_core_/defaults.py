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
            return tuple(self.assumptions)
        return tuple(self._checkAssumptions(assumptions))
    
    def _checkAssumptions(self, assumptions):
        '''
        Check that the given assumptions are valid -- an iterable
        collection of Expressions, and skip any repeats.
        '''
        from expression.expr import Expression
        assumptionsSet = set()
        for assumption in assumptions:
            if not isinstance(assumption, Expression):
                raise TypeError('The assumptions must be an iterable collection of Expression objects')
            if assumption not in assumptionsSet:
                yield assumption
            assumptionsSet.add(assumption)
        
    def __setattr__(self, attr, value):
        '''
        When setting the assumptions, check that they are valid.
        '''
        if attr == 'assumptions' and hasattr(self, attr):
            value = tuple(self._checkAssumptions(value))
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

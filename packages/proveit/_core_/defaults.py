import hashlib, os

class Defaults:
    provingAssumptions = set() # used to avoid infinite recursion
    
    def __init__(self):
        self.assumptions = tuple()
        self.automation = True
    
    def checkedAssumptions(self, assumptions):
        '''
        If the given assumptions is None, return the default;
        otherwise return the given assumptions after
        checking that the new assumptions are valid and
        performing appropriate automation (deriving side-effects).
        '''
        from .proof import Assumption
        if assumptions is None:
            return tuple(self.assumptions)
            
        assumptions = tuple(self._checkAssumptions(assumptions))
        for assumption in assumptions:
            # Prove each assumption, by assumption, to deduce any side-effects.
            if assumption not in Defaults.provingAssumptions: # avoid infinite recursion
                Defaults.provingAssumptions.add(assumption)
                # Note that while we only need THE assumption to prove itself, 
                Assumption.makeAssumption(assumption, assumptions) # having the other assumptions around can be useful for deriving side-effects.
                Defaults.provingAssumptions.remove(assumption) 
        return assumptions
    
    def _checkAssumptions(self, assumptions):
        '''
        Check that the given assumptions are valid -- an iterable
        collection of Expressions, and skip any repeats.
        '''
        from expression.expr import Expression
        assumptionsSet = set()
        try:
            assumptions = list(assumptions)
        except TypeError:
            raise TypeError('The assumptions must be an iterable collection of Expression objects')
        for assumption in list(assumptions):
            if assumption not in assumptionsSet:
                if assumption==WILDCARD_ASSUMPTIONS:
                    # just pass the wildcard assumption along
                    yield assumption
                    assumptionsSet.add(assumption)
                    continue
                if not isinstance(assumption, Expression):
                    raise TypeError("The assumptions must be an iterable collection of Expression objects (or '*' as a wildcard to include anything else that is needed)")
                yield assumption
                assumptionsSet.add(assumption)
        
    def __setattr__(self, attr, value):
        '''
        When setting the assumptions, check that they are valid
        and derive their side-effects.
        '''
        if attr == 'assumptions' and hasattr(self, attr):
            value = tuple(self.checkedAssumptions(value))
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

# use WILDCARD_ASSUMPTIONS (or simply '*'), in assumptions
# lists to indicate that extra necessary assumptions should
# be added automatically without trying to prove them from
# other assumptions.  This is used in KnownTruth.deriveSideEffects
# to derive side-effects with extra assumptions as needed.
WILDCARD_ASSUMPTIONS = '*'

defaults = Defaults()

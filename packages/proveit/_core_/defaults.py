import hashlib, os

class Defaults:
    consideredAssumptionSets = set() # used to avoid infinite recursion and extra work
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        self.assumptions = tuple()
        
        # Enable/disable `automation` by performing automatic
        # side-effects (via `sideEffects` methods) when proving 
        # statements as well as automatically concluding 
        # statements (via `conclude` methods) when possible.
        self.automation = True
        
        # Display LaTeX versions of expressions.
        self.display_latex = True
        
        # Automatic reductions may be applied to expressions that
        # have an "auto_reduction" method if 'auto_reduce' is True
        # and the Expression class is not in 
        # 'disabled_auto_reduction_types'.
        self.auto_reduce = True
        # Note: you can do "with defaults.disabled_auto_reduction_types"
        # for temporary changes to the disabled_auto_reduction_types
        # set.  See DisabledAutoReductionTypes class definition
        # below.
        self.disabled_auto_reduction_types = DisabledAutoReductionTypes()
        
        # Put expression pngs inline versus using links.
        self.inline_pngs = True
        
        Defaults.consideredAssumptionSets.clear()
    
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
        sorted_assumptions = tuple(sorted(assumptions,  key=lambda expr : hash(expr)))
        
        # avoid infinite recursion and extra work
        if sorted_assumptions not in Defaults.consideredAssumptionSets: 
            Defaults.consideredAssumptionSets.add(sorted_assumptions) 
            #print("consider assumptions", assumptions)
            for assumption in assumptions:
                # Prove each assumption, by assumption, to deduce any side-effects.
                # Note that while we only need THE assumption to prove itself, 
                Assumption.makeAssumption(assumption, assumptions) # having the other assumptions around can be useful for deriving side-effects.
            if not self.automation:
                # consideration doesn't fully count if automation is off
                Defaults.consideredAssumptionSets.remove(sorted_assumptions) 
            #print("considered assumptions")
        return assumptions
    
    def _checkAssumptions(self, assumptions):
        '''
        Check that the given assumptions are valid -- an iterable
        collection of Expressions, and skip any repeats.
        '''
        from .expression.expr import Expression
        assumptionsSet = set()
        try:
            assumptions = list(assumptions)
        except TypeError:
            raise TypeError('The assumptions must be an iterable collection of '
                            'Expression objects')
        for assumption in list(assumptions):
            if assumption not in assumptionsSet:
                if not isinstance(assumption, Expression):
                    raise TypeError("The assumptions must be an iterable "
                                    "collection of Expression objects")
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

class DisabledAutoReductionTypes(set):
    '''
    The DisabledAutoReductionTypes class stores the set of Expression
    class types whose auto-reduction feature is currently disabled.
    It is a "context manager" with an __enter__() and __exit__() 
    method such that one may do the following:
        
    with defaults.disabled_auto_reduction_types as disabled_types:
        disabled_types.add(..)
        disabled_types.discard(..)
        etc.
    
    Or equivalently
    with defaults.disabled_auto_reduction_types:
        defaults.disabled_auto_reduction_types.add(..)
        defaults.disabled_auto_reduction_types.discard(..)
        etc.
        
    When it finishes, the disabled_auto_reduction_types will return
    to its original state.
    '''
    def __init__(self):
        set.__init__(self)
    
    def __enter__(self):
        self._original_disabled_types = set(self)
        return self
    
    def __exit__(self, type, value, traceback):
        # Restore to the state of when we "entered".
        self.clear()
        self.update(self._original_disabled_types)

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

import hashlib
import os
import copy


class Defaults:
    # used to avoid infinite recursion and extra work
    considered_assumption_sets = set()

    def __init__(self):
        self.reset()

    def reset(self):
        # Default assumptions to use for proofs.
        self.assumptions = tuple()
        
        # Default styles to use as applicable.
        self.styles = dict()
        
        # When True, match the style of newly created Expression
        # objects to the last "touched" (created or styled) Expression
        # of the same meaning (when use_consistent_styles was True).  
        # This overrides defaults.styles.
        self.use_consistent_styles = True

        # Enable/disable `automation` by performing automatic
        # side-effects (via `side_effects` methods) when proving
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

        # Will be set to a (theory, kind) object when a common
        # expressions, axioms, or theorms notebook is being executed.
        self._running_proveit_notebook = None
        # When running a common expressions notebook, this will be
        # set to the appropriate file to send information about failed
        # imports of other common expressions.
        self.import_failure_filename = None

        Defaults.considered_assumption_sets.clear()

    def temporary(self):
        '''
        Return a context manager that acts as 'defaults' but
        will revert 'defaults' to its original state upon exiting.
        
        For example:
            with defaults.temporary() as temp_defaults:
                temp_defaults.styles['direction'] = 'reversed'
                ...
        
        Will temporarily set the 'direction' style to 'reversed'
        within the "with" block.
        '''
        return TemporaryDefaults()

    def checked_assumptions(self, assumptions):
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
        sorted_assumptions = tuple(
            sorted(
                assumptions,
                key=lambda expr: hash(expr)))

        # avoid infinite recursion and extra work
        if sorted_assumptions not in Defaults.considered_assumption_sets:
            Defaults.considered_assumption_sets.add(sorted_assumptions)
            #print("consider assumptions", assumptions)
            for assumption in assumptions:
                # Prove each assumption, by assumption, to deduce any side-effects.
                # Note that while we only need THE assumption to prove itself,
                # having the other assumptions around can be useful for
                # deriving side-effects.
                Assumption.make_assumption(assumption, assumptions)
            if not self.automation:
                # consideration doesn't fully count if automation is off
                Defaults.considered_assumption_sets.remove(sorted_assumptions)
            #print("considered assumptions")
        return assumptions

    def _checkAssumptions(self, assumptions):
        '''
        Check that the given assumptions are valid -- an iterable
        collection of Expressions, and skip any repeats.
        '''
        from .expression.expr import Expression
        from .expression.composite.expr_tuple import ExprTuple
        assumptions_set = set()
        if isinstance(assumptions, ExprTuple):
            assumptions = assumptions.entries
        else:
            try:
                assumptions = list(assumptions)
            except TypeError:
                raise TypeError(
                    'The assumptions must be an iterable collection of '
                    'Expression objects')
        for assumption in assumptions:
            if assumption not in assumptions_set:
                if not isinstance(assumption, Expression):
                    raise TypeError("The assumptions must be an iterable "
                                    "collection of Expression objects")
                yield assumption
                assumptions_set.add(assumption)

    def __setattr__(self, attr, value):
        '''
        When setting the assumptions, check that they are valid
        and derive their side-effects.
        '''
        if attr == 'assumptions' and hasattr(self, attr):
            value = tuple(self.checked_assumptions(value))
        self.__dict__[attr] = value

class TemporaryDefaults(object):
    '''
    TemporaryDefaults is a context manager that allows us to
    temporarily modify attributes of defaults.  These will revert
    back to the original settings upon exiting the context manager.
    See Defaults.temporary.
    '''
    def __init__(self):
        self._original_values = dict()

    def _safekeep_original(self, attr):
        '''
        Make a copy of the original attribute if we haven't already.
        '''
        if attr not in self._original_values:
            # Remember the original.
            self._original_values[attr] = defaults.__dict__[attr]
            # Use a copy for now. A shallow copy should be sufficient.
            defaults.__dict__[attr] = copy.copy(defaults.__dict__[attr])

    def __setattr__(self, attr, val):
        '''
        Temporarily set the default attribute.
        '''
        if attr == '_original_values':
            object.__setattr__(self, attr, val)
            return
        if defaults.__dict__[attr] == val:
            return # Nothing needs to be done.
        self._safekeep_original(attr)    
        defaults.__dict__[attr] = val
    
    def __getattr__(self, attr):
        '''
        Return the attribute of the aliased attribute of defaults.
        '''
        self._safekeep_original(attr)
        return getattr(defaults, attr)

    def __enter__(self):
        '''
        Return this TemporaryDefaults object as the proper interface 
        into 'defaults' so that the original attribute values of
        'defaults' can be restored upon exiting.
        '''
        return self
    
    def __exit__(self, type, value, traceback):
        '''
        Return the original values of 'defaults'.
        '''
        # Restore to the state of when we "entered".
        for attr, val in self._original_values.items():
            defaults.__dict__[attr] = val

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

import hashlib
import os
import copy
import collections


class Defaults:
    # used to avoid infinite recursion and extra work
    considered_assumption_sets = set()
    
    last_simplifications_directives_id = 0

    def __init__(self):
        self.reset()

    def reset(self):
        # Default assumptions to use for proofs.
        self.assumptions = tuple()
        
        # Enable/disable `automation` by performing automatic
        # side-effects (via `side_effects` methods) when proving
        # statements as well as automatically concluding
        # statements (via `conclude` methods) when possible.
        self.automation = True
        
        # If True, limit the amount of automation that will be
        # employed, making it apply only locally.
        self.minimal_automation = False

        # Display LaTeX versions of expressions.
        self.display_latex = True
        
        # Proven equalities which specify desired replacements.
        # Occurrences of the left side will be replaced with
        # occurrences of the right side during instantiations
        # (and calls to Expression.replaced or 
        # Expression.equality_replaced).
        self.replacements = tuple()
        
        # Automatically simplify expressions as replacements are
        # made (e.g. during instantiations), except for the
        # 'preserved_exprs' (see below).
        self.auto_simplify = True

        # Expressions that should be 'preserved' and not simplified
        # or replaced using an equality-base replacement.
        self.preserved_exprs = set()
        
        # Map expression classes to directives that should be
        # employed when simplifying expressions with that class.
        self._simplification_directives_by_expr_class = dict()
        
        """
        # Hash that unique to the simplification directives.
        self._simplification_directives_hash = None
        
        # Unique id given for a particular set of assumptions and
        # simplification_directives_by_expr_class
        self._assumptions_and_simplification_directives_id = None
        """
        
        """
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
        """

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

    def preserve_expr(self, expr):
        '''
        Preserve the given expression so it is not automatically
        simplified.
        '''
        from proveit._core_.judgment import Judgment
        if isinstance(expr, Judgment):
            expr = expr.expr
        self.preserved_exprs.add(expr)

    """
    def get_simplification_directives_id(self):
        '''
        Get the identifier of the current simplification directives,
        unique for assumptions as well as expression class
        simplification directives.
        '''
        if self._assumptions_and_simplification_directives_id is None:
            # The id must be computed.
            if self._simplification_directives_hash is None:
                # Prepare the simplification directives hash.
                self._simplification_directives_hash = hash(tuple(
                        self._simplification_directives_by_expr_class.items()))   
            # Compute the identifier for the assumptions and the
            # simplification directives.
            self._assumptions_and_simplification_directives_id = hash(
                    (self.assumptions, self._simplification_directives_hash))
        return self._assumptions_and_simplification_directives_id

    def set_expr_class_simplification_directives(self, expr_class, 
                                                 directives):
        '''
        Set the given simplification directives for the given
        expression class and invalidate the simplification directives
        identifier.  Note, directives must be immutable (therefore,
        we check that it is hashable).
        Generally, this should be called indirectly
        via a staticmethod of the particular Expression class.
        '''
        if not isinstance(directives, collections.abs.Hashable):
            raise ValueError("Simplification directives must be mutable "
                             "(and therefore hashable)")
        # Set the new directives:
        self._simplification_directives_by_expr_class[expr_class] = (
                directives)
        # Invalidate directives hash and the assumption-and-directives
        # identifier:
        self._simplification_directives_hash = None
        self._assumptions_and_simplification_directives_id = None        

    def get_expr_class_simplification_directives(self, expr_class):
        '''
        Return simplification directives specified for the given
        expression class.
        '''
        return self._simplification_directives_by_expr_class[expr_class]
    """

    def temporary(self):
        '''
        Return a context manager that acts as 'defaults' but
        will revert 'defaults' to its original state upon exiting.
        
        For example:
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = inner_assumptoins
                ...
        
        Will temporarily set defaults.assumptions to inner_assumptions.
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
            if self.__dict__['assumptions'] == value:
                return # Nothing has changed.
            # Invalidate the _simplification_directives_id since the
            # assumptions may have changed.
            self._simplification_directives_id = None
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
        setattr(defaults, attr, val)
    
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

    def preserve_expr(self, expr):
        '''
        Preserve the given expression so it is not automatically
        simplified.
        '''
        self._safekeep_original('preserved_exprs')
        defaults.preserved_exprs.add(expr)


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

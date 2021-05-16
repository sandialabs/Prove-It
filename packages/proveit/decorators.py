import functools
from inspect import signature, Parameter
from proveit._core_.defaults import defaults


def _make_decorated_prover(func):
    '''
    Use for decorating 'prover' methods 
    (@prover or @equivalence_prover).
    This allows for extra keyword arguments for temporarily altering
    any attributes of the Prove-It 'defaults' (e.g., 
    defaults.assumptions) before calling the decorated method.
    It will then check to see if the return type is a Judgment that is
    valid under "active" assumptions.
    '''    
    sig = signature(func)
    if ('defaults_config' not in sig.parameters or
            sig.parameters['defaults_config'].kind != Parameter.VAR_KEYWORD):
        raise Exception("As a @prover or any @..._prover method, the final "
                        "parameter of %s must be a keyword argument called "
                        "'defaults_config' to signify that it accepts "
                        "keyword arguments for temporarily re-configuring "
                        "attributes of proveit.defaults "
                        "('assumptions', 'styles', etc.)"%func)
    
    is_conclude_method = func.__name__.startswith('conclude')

    def decorated_prover(*args, **kwargs):
        from proveit import Expression, Judgment
        preserve_expr = kwargs.pop('preserve_expr', None)
        if is_conclude_method:
            # If the method starts with conclude 'conclude', we must
            # preserve _self.
            _self = args[0]
            preserve_expr = _self
        defaults_to_change = set(kwargs.keys()).intersection(
                defaults.__dict__.keys())
        # Check to see if there are any unexpected keyword
        # arguments.
        for key in kwargs.keys():
            if key in defaults_to_change: continue
            if key not in sig.parameters:
                raise TypeError(
                        "%s got an unexpected keyword argument '%s' which "
                        "is not an attribute of proveit.defaults"%
                        (func, key))
        def public_attributes_dict(obj):
            # Return a dictionary of public attributes and values of
            # an object.
            return {key:val for key, val in obj.__dict__.items() 
                    if key[0] != '_'}
        
        if preserve_expr is not None:
            # Preserve the 'self' expression.
            if ('preserved_exprs' in defaults_to_change
                    or  preserve_expr not in defaults.preserved_exprs):
                if 'preserved_exprs' in kwargs:
                    kwargs['preserved_exprs'].add(preserve_expr)
                else:
                    defaults_to_change.add('preserved_exprs')
                    kwargs['preserved_exprs'] = (
                            defaults.preserved_exprs.union({preserve_expr}))
        
        def checked_truth(proven_truth):
            # Check that the proven_truth is a Judgment and has
            # appropriate assumptions.
            if not isinstance(proven_truth, Judgment):
                raise TypeError("@prover method %s is expected to return "
                                "a proven Judgment, not %s of type %s."
                                %(func, proven_truth, proven_truth.__class__))
            if not proven_truth.is_applicable():
                raise TypeError("@prover method %s returned a Judgment, "
                                "%s, that is not proven under the active "
                                "assumptions: %s"
                                %(func, proven_truth, defaults.assumptions)) 
            return proven_truth
        
        if len(defaults_to_change) > 0:
            # Temporarily reconfigure defaults with 
            with defaults.temporary() as temp_defaults:
                for key in defaults_to_change:
                    # Temporarily alter a default:
                    setattr(temp_defaults, key, kwargs[key])
                kwargs.update(public_attributes_dict(defaults))
                proven_truth = checked_truth(func(*args, **kwargs))
        else:
            # No defaults reconfiguration.
            kwargs.update(public_attributes_dict(defaults))
            proven_truth = checked_truth(func(*args, **kwargs))
                
        if is_conclude_method:
            self = args[0]
            if isinstance(self, Expression):
                expr = self
            elif hasattr(self, 'expr'):
                expr = self.expr
            else:
                raise TypeError(
                        "The @prover method %s beginning with 'conclude' "
                        "expected to be a method for an Expression type "
                        "or the object must have an 'expr' attribute."%func)                
            if func.__name__.startswith('conclude_negation'):
                from proveit.logic import Not
                not_expr = Not(expr)
                if proven_truth.expr != not_expr:
                    raise ValueError(
                            "@prover method %s whose name starts with "
                            "'conclude_negation' must prove %s "
                            "but got %s."%(func, not_expr, proven_truth))   
                # Match the style of not_self.
                return proven_truth.with_matching_style(not_expr)
            else:
                if proven_truth.expr != expr:
                    print(proven_truth.expr.expr_info())
                    print(self.expr_info())
                    raise ValueError("@prover method %s whose name starts with "
                                     "'conclude' must prove %s but got "
                                     "%s."%(func, expr, proven_truth))
                # Match the style of self.
                return proven_truth.with_matching_style(expr)
        return proven_truth
    return decorated_prover    
    

def _wraps(func, wrapper):
    '''
    Perform functools.wraps as well as add an extra message to the doc
    string.
    '''
    wrapped = functools.wraps(func)(wrapper)
    if wrapped.__doc__ is None:
        wrapped.__doc__ = ""
    wrapped.__doc__ += """
    
    Keyword arguments are accepted for temporarily changing any
    of the attributes of proveit.defaults.
    """
    return wrapped

def prover(func):
    '''
    @prover is a decorator for methods that are to return a proven
    judgment valid under "active" (default) assumptions.  As a special
    feature, this decorator allows for extra keyword arguments for
    temporarily altering any attributes of the Prove-It 'defaults'
    (e.g., defaults.assumptions) before calling the decorated method.
    It will then check to see if the return type is a Judgment that is
    valid under "active" assumptions.
    '''
    return _wraps(func, _make_decorated_prover(func))

# Keep track of equivalence provers so we may register them during
# Expression class construction (see ExprType.__init__ in expr.py).
_equiv_prover_fn_to_tenses = dict()
_equiv_prover_name_to_tenses = dict()

def equivalence_prover(past_tense, present_tense):
    '''
    @equivalence_prover works the same way as the @prover decorator
    except that it also registers the "equivalence method" in
    InnerExpr with the past tense and present tense names.  The method
    name itself should be a noun form and return the proven equivalence
    with 'self' of the method on the left-hand side.  Calling the 
    past-tense version will return the right-hand side as equivalent
    to 'self'.  The present-tense version can be called on an
    InnerExpr of a Judgment to return a Judgment where inner expression
    is replaced according to the equivalence.
    
    To ensure that the left-hand side of the equivalence is not altered
    via automatic simplification, we temporarily 'preserve' the 'self'
    expression in the defaults before the equivalence method is called.
    '''    
    
    def wrapper_maker(func):
        '''
        Make the wrapper for the equivalence_prover decorator.
        '''
        name = func.__name__
        if name in _equiv_prover_name_to_tenses:
            # This name was used before; make sure past and present
            # tenses are consistent.
            previous_tenses = (
                _equiv_prover_name_to_tenses[name])
            current_tenses = (past_tense, present_tense)
            if (previous_tenses != current_tenses):
                raise InconsistentTenseNames(func, previous_tenses, 
                                             current_tenses)
        else:
            _equiv_prover_name_to_tenses[name] = (
                    past_tense, present_tense)
        is_simplification_method = (name == 'simplification')
        is_evaluation_method = (name == 'evaluation')
        is_shallow_evaluation_method = (name == 'shallow_evaluation')
        decorated_prover = _make_decorated_prover(func)

        def wrapper(*args, **kwargs):   
            '''
            The wrapper for the equivalence_prover decorator.
            '''
            from proveit._core_.expression.expr import Expression
            from proveit.relation import TransitiveRelation
            # 'preserve' the 'self' expression so it will be on the 
            # left side without simplification.
            _self = args[0]
            kwargs['preserve_expr'] = _self
            proven_truth = None
            if is_simplification_method or is_evaluation_method:
                from proveit.logic import (is_irreducible_value,
                                           Equals)
                # See if there is a known evaluation (or if one may
                # be derived via known equalities if defaults.automation
                # is enabled).
                known_evaluation = Equals.get_known_evaluation(_self)
                if known_evaluation is None:
                    if is_irreducible_value(_self):
                        # Already irreducible.
                        proven_truth = Equals(_self, _self).prove()
                    """
                    elif is_simplification_method:
                        # See if there is a known simplification (or if 
                        # one may be derived via known equalities if
                        # defaults.automation is enabled).
                        known_simplification = (
                                Equals.get_known_simplification(_self))
                        if known_simplification is not None:
                            proven_truth = known_simplification
                    """
                else:
                    proven_truth = known_evaluation
            if proven_truth is None:
                proven_truth = decorated_prover(*args, **kwargs)
            proven_expr = proven_truth.expr
            if not isinstance(proven_expr, TransitiveRelation):
                raise TypeError(
                        "@equivalence_prover, %s, expected to prove a "
                        "TranstiveRelation expression (more "
                        "specifically, the EquivalenceClass type "
                        "of relation), not %s of type %s."
                        %(func, proven_expr, proven_expr.__class__))
            if not isinstance(proven_expr, 
                              proven_expr.__class__.EquivalenceClass()):
                raise TypeError(
                        "@equivalence_prover, %s, expected to prove a "
                        "TranstiveRelation of the EquivalenceClass, "
                        "not %s of type %s."
                        %(func, proven_expr, proven_expr.__class__))
            if isinstance(_self, Expression):
                expr = _self
            elif hasattr(_self, 'expr'):
                expr = _self.expr
            else:
                raise TypeError("@equivalence_prover, %s, expected to be "
                                "a method for an Expression type or it "
                                "must have an 'expr' attribute."%func)
            if proven_expr.lhs != expr:
                raise TypeError(
                        "@equivalence_prover, %s, expected to prove an "
                        "equivalence relation with %s on its left side "
                        "('lhs').  %s does not satisfy this "
                        "requirement."%(func, expr, proven_expr))
            if not proven_expr.lhs.has_same_style(expr):
                # Make the left side of the proven truth have a style
                # that matches the original expression.
                inner_lhs = proven_truth.inner_expr().lhs
                proven_truth = inner_lhs.with_matching_style(expr)
            if is_simplification_method or is_evaluation_method:
                from proveit.logic import Equals
                if not isinstance(proven_expr, Equals):
                    raise TypeError(
                            "%s method expected to prove an equality"
                            %str(func))
                """
                # Remember that the rhs is a simplified expression
                # under current simplification directives.
                directive_id = defaults.get_simplification_directives_id()
                Expression.simplified_exprs.setdefault(
                        directive_id, set()).add(
                                proven_expr.rhs)
                """
            """
            if is_simplification_method:
                from proveit.logic import Equals
                Equals.remember_simplification(proven_truth)
            el
            """
            if is_evaluation_method or is_shallow_evaluation_method:
                # The right side of an evaluation must be irreducible.
                from proveit.logic import is_irreducible_value
                if not is_irreducible_value(proven_expr.rhs):
                    raise TypeError(
                            "An 'evaluation' for %s via %s must have an "
                            "irreducible value in the right side, "
                            "is_irreducible_value(%s) is False."
                            %(_self, func, proven_expr.rhs))
            return proven_truth

        _equiv_prover_fn_to_tenses[wrapper] = (past_tense, present_tense)
        return _wraps(func, wrapper)

    return wrapper_maker

"""
def equivalence_prover(past_tense, present_tense):
    '''
    @equivalence_prover works the same way as the @prover decorator
    except that it also registers the "equivalence method" in
    InnerExpr with the past tense and present tense names.  The method
    name itself should be a noun form and return the proven equivalence
    with 'self' of the method on the left-hand side.  Calling the 
    past-tense version will return the right-hand side as equivalent
    to 'self'.  The present-tense version can be called on an
    InnerExpr of a Judgment to return a Judgment where inner expression
    is replaced according to the equivalence.
    
    To ensure that the left-hand side of the equivalence is not altered
    via automatic simplification, we temporarily 'preserve' the 'self'
    expression in the defaults before the equivalence method is called.
    '''    
    class EquivalenceProverDecorator:
        def __init__(self, func):
            functools.update_wrapper(self, func)
            self.func = func
        
        def __set_name__(self, owner, name):
            # Solution for obtaining the method class (owner) seen at: 
            # https://stackoverflow.com/questions/2366713/can-a-decorator-of-an-instance-method-access-the-class

            # Register the equivalence method:
            _register_equivalence_method(
                owner, name, past_tense, present_tense)        

        def __call__(self, *args, **kwargs):
            from proveit.relation import TransitiveRelation
            # 'preserve' it so it will be on the left side without
            # simplification.
            print(self.func, args, kwargs)
            kwargs['preserved_exprs'] = set(defaults.preserved_exprs)
            kwargs['preserved_exprs'].add(self.func.__self__)
            proven_truth = _make_decorated_prover(self.func)(*args, **kwargs)
            proven_expr = proven_truth.expr
            if not isinstance(proven_expr, TransitiveRelation):
                raise TypeError("@equivalence_prover expected to prove a "
                                "TranstiveRelation expression (more "
                                "specifically, the EquivalenceClass type of "
                                "relation), not %s of type %s"
                                %(proven_expr, proven_expr.__class__))
            if not isinstance(proven_expr, 
                              proven_expr.__class__.EquivalenceClass()):
                raise TypeError("@equivalence_prover expected to prove a "
                                "TranstiveRelation of the EquivalenceClass, "
                                "not %s of type %s"
                                %(proven_expr, proven_expr.__class__))
            if proven_expr.lhs != self.func.__self__:
                raise TypeError("@equivalence_prover expected to prove an "
                                "equivalence relation with 'self', %s, on "
                                "its left side ('lhs').  %s does not satisfy "
                                "this requirement"%(self, proven_expr))
            return proven_truth
    
    return EquivalenceProverDecorator
"""

class InconsistentTenseNames(Exception):
    def __init__(self, func, previous_tenses, current_tenses):
        self.func = func
        self.previous_tenses = previous_tenses
        self.current_tenses = current_tenses
    
    def __str__(self):
        return ("Past and present tenses for %s are inconsistent "
                "with another occurrence: %s vs %s.  It may be a typo."
                %(self.func, self.previous_tenses, 
                  self.current_tenses))

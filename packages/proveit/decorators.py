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
    
    def decorated_prover(*args, **kwargs):
        from proveit import Judgment
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
        if len(defaults_to_change) > 0:
            # Temporarily reconfigure defaults with 
            with defaults.temporary() as temp_defaults:
                for key in defaults_to_change:
                    # Temporarily alter a default:
                    setattr(temp_defaults, key, kwargs[key])
                assumptions = temp_defaults.assumptions
                kwargs.update(public_attributes_dict(defaults))
                proven_truth = func(*args, **kwargs)
        else:
            # No defaults reconfiguration.
            assumptions = defaults.assumptions
            kwargs.update(public_attributes_dict(defaults))
            proven_truth = func(*args, **kwargs)
        
        is_conclude_method = func.__name__.startswith('conclude')
        if not is_conclude_method and proven_truth is None:
            # It is okay for a prover method to return None.
            return None
        
        if not isinstance(proven_truth, Judgment):
            raise TypeError("@prover method %s is expected to return "
                            "a proven Judgment, not %s of type %s."
                            %(func, proven_truth, proven_truth.__class__))
        if not proven_truth.is_sufficient(assumptions):
            raise TypeError("@prover method %s returned a Judgment "
                            "that is not proven under the active "
                            "assumptions: %s"%(func, assumptions))
        if is_conclude_method:
            self = args[0]
            if func.__name__.startswith('conclude_negation'):
                from proveit.logic import Not
                not_self = Not(self)
                if proven_truth.expr != not_self:
                    raise ValueError(
                            "@prover method %s whose name starts with "
                            "'conclude_negation' must prove 'Not(self)', "
                            "%s, but got %s."%(func, not_self, proven_truth))                
            else:
                if proven_truth.expr != self:
                    raise ValueError("@prover method %s whose name starts with "
                                     "'conclude' must prove 'self', %s, but got "
                                     "%s."%(func, self, proven_truth))
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
    @prover is a decorators for methods that are to return a proven
    judgment valid under "active" (default) assumptions.  As a special
    feature, this decorator allows for extra keyword arguments for
    temporarily altering any attributes of the Prove-It 'defaults'
    (e.g., defaults.assumptions) before calling the decorated method.
    It will then check to see if the return type is a Judgment that is
    valid under "active" assumptions.
    '''
    return _wraps(func, _make_decorated_prover(func))


class equivalence_prover:
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
    
    name_to_past_and_present_tense = dict()
    
    def __init__(self, past_tense, present_tense):
        self.past_tense = past_tense
        self.present_tense = present_tense

    def __set_name__(self, owner, name):
        # Solution for obtaining the method class (owner) seen at: 
        # https://stackoverflow.com/questions/2366713/can-a-decorator-of-an-instance-method-access-the-class

        if name in equivalence_prover.name_to_past_and_present_tense:
            # This name was used before; make sure past and present
            # tenses are consistent.
            previous_tenses = (
                    equivalence_prover.name_to_past_and_present_tense[name])
            current_tenses = (self.past_tense, self.present_tense)
            if (previous_tenses != current_tenses):
                raise InconsistentTenseNames(name, previous_tenses, 
                                             current_tenses)
        else:
            equivalence_prover.name_to_past_and_present_tense[name] = (
                    self.past_tense, self.present_tense)

        # Register the equivalence method:
        _register_equivalence_method(
            owner, name, self.past_tense, self.present_tense)    
    
    def __call__(self, func):
        _decorated_prover = _make_decorated_prover(func)
        def wrapper(*args, **kwargs):
            from proveit.relation import TransitiveRelation
            # 'preserve' it so it will be on the left side without
            # simplification.
            _self = args[0]
            kwargs['preserved_exprs'] = set(defaults.preserved_exprs)
            kwargs['preserved_exprs'].add(_self)     
            proven_truth = None
            if func.name in ('simplification', 'evaluation'):
                from proveit.logic import (Equals, SimplificationError,
                                           EvaluationError)
                known_evaluation = Equals.get_known_evaluation(self)
                if known_evaluation is None:
                    if func.name == 'simplification':
                        known_simplification = (
                                Equals.get_known_simplification(self))
                        if known_simplification is not None:
                            proven_truth = known_simplification
                else:
                    proven_truth = known_evaluation
                if proven_truth is None:
                    if func.name == 'simplification':
                        raise SimplificationError(
                                "Unable to perform simplification with "
                                "automation disabled")
                    if func.name == 'evaluation':
                        raise EvaluationError(
                                "Unable to perform evaluation "
                                "with automation disabled")
            if proven_truth is None:
                proven_truth = _decorated_prover(*args, **kwargs)
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
            if func.name in ('simplification', 'evaluation'):
                from proveit.logic import Equals
                if not isinstance(proven_expr, Equals):
                    raise TypeError("%s method expected to prove an equality"
                                    %str(func))
            if proven_expr.lhs != _self:
                raise TypeError("@equivalence_prover expected to prove an "
                                "equivalence relation with 'self', %s, on "
                                "its left side ('lhs').  %s does not satisfy "
                                "this requirement"%(self, proven_expr))
            if func.name == 'simplification':
                from proveit.logic import Equals
                Equals.remember_simplification(proven_truth)
            elif func.name in ('evaluation', 'shallow_evaluation'):
                # The right side of an evaluation must be irreducible.
                from proveit.logic import is_irreducible_value
                if not is_irreducible_value(proven_expr.rhs):
                    raise TypeError(
                            "An 'evaluation' must have an irreducible "
                            "value in the right side, "
                            "is_irreducible_value(%s) is False"
                            %proven_expr.rhs)
                    
            return proven_truth
        return _wraps(func, wrapper)

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


def _register_equivalence_method(
        expr_class, equiv_method, past_tense_name, present_tense_name):
    '''
    Register a method of an expression class that is used to derive and 
    return (as a Judgment) the equivalence of that expression on the
    left side with a new form on the right side.
    (e.g., 'simplification', 'evaluation', 'commutation', 
    'association').
    In addition to the expression class and the method (as a name or 
    function object), also provide the "past-tense" form of the name 
    for deriving the equivalence and returning the right side, and 
    provide the "action" form of the name that may be used to make
    the replacement directly within a Judgment to produce a revised 
    Judgment.  The "past-tense" version will be added automatically as 
    a method to the given expression class with an appropriate doc 
    string.
    '''
    if not isinstance(equiv_method, str):
        # can be a string or a function:
        equiv_method = equiv_method.__name__
    if not hasattr(expr_class, equiv_method):
        raise Exception(
            "Must have '%s' method defined in class '%s' in order to register it as an equivalence method in InnerExpr." %
            (equiv_method, str(expr_class)))

    # Store information in the Expression class that will enable calling
    # InnerExpr methods when an expression of that type
    # is the inner expression for generating equivalences or performing
    # in-place replacements.
    setattr(
        expr_class, '_equiv_method_%s_' %
        equiv_method, ('equiv', equiv_method))
    setattr(
        expr_class, '_equiv_method_%s_' %
        past_tense_name, ('rhs', equiv_method))
    setattr(
        expr_class, '_equiv_method_%s_' %
        present_tense_name, ('action', equiv_method))

    # Automatically create the "paste-tense" equivalence method for the
    # expression class which returns the right side.
    """
    if hasattr(expr_class, past_tense_name):
        raise Exception(
            "Should not manually define '%s' in class '%s'.  This "
            "'past-tense' equivalence method will be generated "
            "automatically by registering it in InnerExpr." %
            (past_tense_name, str(expr_class)))
    """

    def equiv_rhs(expr, *args, **kwargs):
        return getattr(expr, equiv_method)(*args, **kwargs).rhs
    equiv_rhs.__name__ = past_tense_name
    equiv_rhs.__doc__ = (
            "Return an equivalent form of this expression derived via '%s'." 
            % equiv_method)
    setattr(expr_class, past_tense_name, equiv_rhs)

class InconsistentTenseNames(Exception):
    def __init__(self, noun, previous_tenses, current_tenses):
        self.noun = noun
        self.previous_tenses = previous_tenses
        self.current_tenses = current_tenses
    
    def __str__(self):
        return ("Past and present tenses of an @equivalence_prover called "
                "%s are inconsistent with another occurrence: %s vs %s. "
                "It may be a typo."%(self.noun, self.previous_tenses,
                                     self.current_tenses))
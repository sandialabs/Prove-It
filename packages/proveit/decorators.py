import functools
from inspect import signature
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
    def decorated_prover(*args, **kwargs):
        from proveit import Judgment
        defaults_to_change = set(kwargs.keys()).intersection(
                defaults.__dict__.keys())
        if len(defaults_to_change) > 0:
            sig = signature(func)            
            with defaults.temporary() as temp_defaults:
                for key in defaults_to_change:
                    # Temporarily alter a default:
                    setattr(temp_defaults, key, kwargs[key])
                    if key not in sig.parameters:
                        # Don't pass on this keyword if it isn't
                        # an explicit parameter in the 'func'
                        # signature.
                        kwargs.pop(key)
                assumptions = temp_defaults.assumptions
                proven_truth = func(*args, **kwargs)
        else:
            assumptions = defaults.assumptions
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
    return functools.wraps(func)(_make_decorated_prover(func))


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
    
    def __init__(self, past_tense, present_tense):
        self.past_tense = past_tense
        self.present_tense = present_tense

    def __set_name__(self, owner, name):
        # Solution for obtaining the method class (owner) seen at: 
        # https://stackoverflow.com/questions/2366713/can-a-decorator-of-an-instance-method-access-the-class

        print(owner, name)
        # Register the equivalence method:
        _register_equivalence_method(
            owner, name, self.past_tense, self.present_tense)    
    
    def __call__(self, func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            from proveit.relation import TransitiveRelation
            # 'preserve' it so it will be on the left side without
            # simplification.
            _self = args[0]
            kwargs['preserved_exprs'] = set(defaults.preserved_exprs)
            kwargs['preserved_exprs'].add(_self)
            proven_truth = _make_decorated_prover(func)(*args, **kwargs)
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
            if proven_expr.lhs != _self:
                raise TypeError("@equivalence_prover expected to prove an "
                                "equivalence relation with 'self', %s, on "
                                "its left side ('lhs').  %s does not satisfy "
                                "this requirement"%(self, proven_expr))
            return proven_truth
        return wrapper

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

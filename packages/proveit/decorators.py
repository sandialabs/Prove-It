import functools
from inspect import signature, Parameter
from proveit._core_.defaults import defaults
from proveit.util import OrderedSet

def _make_decorated_prover(func, automatic=False):
    '''
    Use for decorating 'prover' methods 
    (@prover, @relation_prover, or @equality_prover).
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
        from proveit import Expression, Judgment, InnerExpr, ProofFailure
        from proveit._core_.proof import Assumption
        from proveit.logic import Equals
        if (kwargs.get('preserve_all', False) and 
                len(kwargs.get('replacements', tuple())) > 0):
            raise ValueError(
                    "Adding 'replacements' and setting 'preserve_all' "
                    "to True are incompatible settings.")
        preserve_lhs = kwargs.pop('preserve_lhs', False)
        preserve_expr = kwargs.pop('preserve_expr', None)
        if len(args) > 0:
            _self = args[0]
            if isinstance(_self, Judgment) or isinstance(_self, InnerExpr):
                # Include the assumptions of the Judgment or InnerExpr
                _assumptions = kwargs.get('assumptions', None)
                if _assumptions is None:
                    _assumptions = defaults.assumptions
                if not _self.assumptions.issubset(_assumptions):
                    _assumptions = OrderedSet(_assumptions, mutable=False)
                    kwargs['assumptions'] = _assumptions + _self.assumptions
            if is_conclude_method:
                # If the method starts with conclude 'conclude', we must
                # preserve _self.
                if (not isinstance(_self, Expression) 
                        and hasattr(_self, 'expr')):
                    # preserve_expr = _self.expr
                    kwargs['preserved_exprs'] = {_self.expr}
                else:
                    # preserve_expr = _self
                    kwargs['preserved_exprs'] = {_self}
        defaults_to_change = set(kwargs.keys()).intersection(
                defaults.__dict__.keys())
        if 'automation' in kwargs.keys():
            # While 'automation' isn't a defaults key, it can be set
            # to set 'sideeffect_automation' and 'conclude_automation'.
            defaults_to_change.add('automation')
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

        exprs_to_replace = set()
        if 'replacements' in kwargs:
            for replacement in kwargs['replacements']:
                if not isinstance(replacement, Judgment):
                    raise TypeError("The 'replacements' must be Judgments")
                if not isinstance(replacement.expr, Equals):
                    raise TypeError(
                        "The 'replacements' must be equality Judgments")
                exprs_to_replace.add(replacement.expr.lhs)

        # Make sure a preserved expression isn't also being replaced.
        if 'preserved_exprs' in kwargs:
            # Make sure a preserved expression isn't also
            # being replaced.
            preserved_exprs = kwargs['preserved_exprs']
            if not exprs_to_replace.isdisjoint(preserved_exprs):
                raise ValueError(
                    "Cannot simultaneously replace and preserve these "
                    "expression: %s"
                    %exprs_to_replace.intersection(preserved_exprs))

        if preserve_expr is not None:
            # Make sure this preserved expression isn't also being replaced.
            if preserve_expr in exprs_to_replace:
                raise ValueError(
                    "Cannot simultaneously replace and preserve %s"
                    %preserve_expr)
            # Preserve the 'preserve_expr'.
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
            if proven_truth is None and is_conclude_method:
                return proven_truth # we'll raise an exception later.
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

        if (automatic and not defaults.preserve_all) or (
                len(defaults_to_change) > 0):
            # Temporarily reconfigure defaults
            with defaults.temporary() as temp_defaults:
                if 'assumptions' in defaults_to_change:
                    # Set 'assumptions' first (before turning off
                    # 'automation', for example, so that the 
                    # side-effects will be processed).
                    key = 'assumptions'
                    setattr(temp_defaults, key, kwargs[key])
                for key in defaults_to_change:
                    if key != 'assumptions':
                        # Temporarily alter a default:
                        setattr(temp_defaults, key, kwargs[key])
                if automatic:
                    temp_defaults.preserve_all=True
                    temp_defaults.preserved_exprs = set()
                internal_kwargs = dict(kwargs)
                internal_kwargs.update(public_attributes_dict(defaults))
                # Make sure we derive assumption side-effects first.
                Assumption.make_assumptions()
                # Now call the prover function.
                proven_truth = checked_truth(func(*args, **internal_kwargs))
        else:
            # No defaults reconfiguration.
            internal_kwargs = dict(kwargs)
            internal_kwargs.update(public_attributes_dict(defaults))
            # Make sure we derive assumption side-effects first.
            Assumption.make_assumptions()
            # Now call the prover function.
            proven_truth = checked_truth(func(*args, **internal_kwargs))

        if automatic and not defaults.preserve_all:
            # Temporarily reconfigure defaults
            with defaults.temporary() as temp_defaults:
                for key in defaults_to_change:
                    # Temporarily alter a default:
                    setattr(temp_defaults, key, kwargs[key])
                #print(func.__name__, proven_truth)
                # Effect the replacements and/or auto-simplification by
                # regenerating the proof object under the active defaults.
                orig_proven_truth = proven_truth
                if preserve_lhs:
                    from proveit import safe_dummy_var
                    from proveit.relation import Relation
                    _expr = proven_truth.expr
                    if not isinstance(_expr, Relation):
                        raise TypeError(
                            "@relation_proven, %s, expected to prove a"
                            "Relation expression but got %s"%(func, _expr))
                    simplify_only_where_marked = True
                    dummy_var = safe_dummy_var(_expr)
                    markers_and_marked_expr = (
                        (dummy_var,), type(_expr)(_expr.lhs, dummy_var))
                else:
                    simplify_only_where_marked = False
                    marker_and_Marked_expr = None
                new_proven_truth = (
                    proven_truth.proof().regenerate_proof_object(
                        simplify_only_where_marked, markers_and_marked_expr)
                    .proven_truth)
                proven_truth = (new_proven_truth.inner_expr()
                                .with_mimicked_style(proven_truth.expr))
                #print('preserved_exprs', defaults.preserved_exprs,
                #      'orig_proven_truth', orig_proven_truth,
                #      'proven_truth', proven_truth)

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
            if proven_truth is None:
                raise NotImplementedError("@prover method %s is not implemented "
                                 "for %s."
                                %(func, expr))
            if func.__name__.startswith('conclude_negation'):
                from proveit.logic import Not
                not_expr = Not(expr)
                if proven_truth.expr != not_expr:
                    raise ProofFailure( # previously ValueError
                            not_expr,
                            defaults.assumptions,
                            "@prover method %s whose name starts with "
                            "'conclude_negation' must prove %s "
                            "but got %s."%(func, not_expr, proven_truth))   
                # Match the style of not_self.
                return proven_truth.with_matching_style(not_expr)
            else:
                if proven_truth.expr != expr:
                    raise ProofFailure( # previously ValueError
                           expr,
                           defaults.assumptions,
                           "@prover method %s whose name starts with "
                                     "'conclude' must prove %s but got "
                                     "%s."%(func, expr, proven_truth))
                # Match the style of self.
                return proven_truth.with_matching_style(expr)
        return proven_truth
    return decorated_prover    

def _make_decorated_relation_prover(func, automatic=False):
    '''
    Use for decorating 'relation_prover' methods 
    (@relation_prover or @equality_prover).  In addition
    to the @prover capabilities, temporarily altering 'defaults' and
    checking that a Judgment is returned check that the
    Judgment is for a Relation.  Furthermore, unless alter_lhs=True 
    is set in the keyword arguments when the method is called,
    automatically 'preserve' the 'self' expression and make sure it
    is on the left side of the returned Relation Judgment.
    '''

    decorated_prover = _make_decorated_prover(func, 
                                              automatic=automatic)
    
    def decorated_relation_prover(*args, **kwargs):
        from proveit._core_.expression.expr import Expression
        from proveit._core_.expression.composite import ExprRange, ExprTuple
        from proveit.relation import Relation  
        
        # 'preserve' the 'self' or 'self.expr' expression so it will 
        # be on the left side without simplification.
        _self = args[0]
        if isinstance(_self, Expression):
            expr = _self
        elif hasattr(_self, 'expr'):
            expr = _self.expr
        else:
            raise TypeError("@relation_prover, %s, expected to be a "
                            "method for an Expression type or it must "
                            "have an 'expr' attribute."%func)
        alter_lhs = kwargs.pop('alter_lhs', False)
        if not alter_lhs:
            if automatic:
                kwargs['preserve_lhs'] = True
            else:
                # preserve the left side.
                if 'preserve_expr' in kwargs:
                    if 'preserved_exprs' in kwargs:
                        kwargs['preserved_exprs'] = (
                            kwargs['preserved_exprs'].union([expr]))
                    else:
                        kwargs['preserved_exprs'] = (
                            defaults.preserved_exprs.union([expr]))
                else:
                    kwargs['preserve_expr'] = expr
        
        # Use the regular @prover wrapper.
        proven_truth = decorated_prover(*args, **kwargs)
        
        # Check that the result is of the expected form.
        proven_expr = proven_truth.expr
        if not isinstance(proven_expr, Relation):
            raise TypeError(
                    "@relation_prover, %s, expected to prove a "
                    "Relation expression, not %s of type %s."
                    %(func, proven_expr, proven_expr.__class__))
        if not alter_lhs:
            expected_lhs = expr
            if isinstance(expr, ExprRange):
                expected_lhs = ExprTuple(expr)
            if proven_expr.lhs != expected_lhs:
                raise TypeError(
                        "@relation_prover, %s, expected to prove a "
                        "relation with %s on its left side "
                        "('lhs').  %s does not satisfy this "
                        "requirement."%(func, expected_lhs, proven_expr))
            # Make the style consistent with the original expression.
            if not proven_expr.lhs.has_same_style(expected_lhs):
                # Make the left side of the proven truth have a style
                # that matches the original expression.
                inner_lhs = proven_truth.inner_expr().lhs
                proven_truth = inner_lhs.with_matching_style(expected_lhs)
        return proven_truth
    return decorated_relation_prover


def _wraps(func, wrapper, extra_doc=None):
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
    if extra_doc is not None:
        wrapped.__doc__ += extra_doc
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

def auto_prover(func):
    '''

    '''
    return _wraps(func, _make_decorated_prover(func, automatic=True))

def relation_prover(func):
    '''
    @relation_prover is a decorator for methods that are to return a 
    proven judgment valid under "active" (default) assumptions, is a
    Relation type Expression, and has the original expression (self
    or self.expr) on the left hand side.  This "original expression"
    will automatically be "preserved" (not automatically simplified).
    The style of the original expression will be used on the left side.  
    As with @prover methods, defaults may be temporarily set.
    '''
    return _wraps(func, _make_decorated_relation_prover(func))

def auto_relation_prover(func):
    '''

    '''
    return _wraps(func, _make_decorated_relation_prover(func, 
                                                        automatic=True))

# Keep track of equivalence provers so we may register them during
# Expression class construction (see ExprType.__init__ in expr.py).
_equality_prover_fn_to_tenses = dict()
_equality_prover_name_to_tenses = dict()

def equality_prover(past_tense, present_tense, automatic=False):
    '''
    @equality_prover works the same way as the @relation_prover decorator
    except that it also registers the "equality method" in
    InnerExpr with the past tense and present tense names.  The method
    name itself should be a noun form and return the proven equality
    with 'self' of the method on the left-hand side.  Calling the 
    past-tense version will return the right-hand side as equal
    to 'self'.  The present-tense version can be called on an
    InnerExpr of a Judgment to return a Judgment where inner expression
    is replaced according to the equality.
    '''    
    
    def wrapper_maker(func):
        '''
        Make the wrapper for the equality_prover decorator.
        '''
        name = func.__name__
        if name in _equality_prover_name_to_tenses:
            # This name was used before; make sure past and present
            # tenses are consistent.
            previous_tenses = (
                _equality_prover_name_to_tenses[name])
            current_tenses = (past_tense, present_tense)
            if (previous_tenses != current_tenses):
                raise InconsistentTenseNames(func, previous_tenses, 
                                             current_tenses)
        else:
            _equality_prover_name_to_tenses[name] = (
                    past_tense, present_tense)
        is_evaluation_method = (name == 'evaluation')
        is_shallow_simplification_method = (name == 'shallow_simplification')
        is_simplification_method = (name == 'simplification')
        decorated_relation_prover = _make_decorated_relation_prover(
            func, automatic=automatic)

        def wrapper(*args, **kwargs):   
            '''
            The wrapper for the equality_prover decorator.
            '''
            from proveit._core_.expression.expr import Expression
            from proveit._core_.proof import (Assumption, 
                                              UnsatisfiedPrerequisites)
            from proveit.logic import Equals, EvaluationError
            # Obtain the original Expression to be on the left side
            # of the resulting equality Judgment.
            _self = args[0]
            if isinstance(_self, Expression):
                expr = _self
            elif hasattr(_self, 'expr'):
                expr = _self.expr
            else:
                raise TypeError("@equality_prover, %s, expected to be a "
                                "method for an Expression type or it must "
                                "have an 'expr' attribute."%func)            
            proven_truth = None
            if is_simplification_method or is_evaluation_method:
                from proveit.logic import is_irreducible_value
                if is_irreducible_value(expr):
                    # Already irreducible.  Done.
                    proven_truth = (
                            Equals(expr, expr).conclude_via_reflexivity())

            # If _no_eval_check is set to True, don't bother
            # checking for an existing evaluation.  Used internally
            # in Operation.simplification, Operation.evaluation,
            # Conditional.simplification, and Judgment.simplify.
            _no_eval_check = kwargs.pop('_no_eval_check', False)
            if (not _no_eval_check and (
                    is_evaluation_method or
                    (defaults.simplify_with_known_evaluations 
                     and is_simplification_method))):
                from proveit.logic import evaluate_truth
                # See if there is a known evaluation (directly or
                # indirectly and/or via canonical forms).
                # First, make sure we derive assumption side-effects.
                with defaults.temporary() as tmp_defaults:
                    if 'assumptions' in kwargs:
                        tmp_defaults.assumptions = kwargs['assumptions']
                    Assumption.make_assumptions()
                    cf = expr.canonical_form()
                    if expr.proven():
                        # The expression is proven so it equals true.
                        proven_truth = evaluate_truth(expr)
                    elif is_irreducible_value(cf):
                        eq_cf = Equals(expr, cf)
                        if eq_cf.proven():
                            proven_truth = eq_cf.prove()
                        else:
                            # Note: If the canonical form is 
                            # irreducible, don't divert from calling
                            # the appropriate method to perform the
                            # evaluation.
                            proven_truth = None
                    else:
                        try:
                            proven_truth = (Equals.get_readily_provable_evaluation(
                                            expr, use_canonical_forms=True))
                        except UnsatisfiedPrerequisites:
                            proven_truth = None
                # For an 'evaluation' or 'simplification', we should
                # force auto_simplify on and preserve_all off to
                # simplify as much as possible.
                kwargs['auto_simplify'] = True
                kwargs['preserve_all'] = False
            if proven_truth is None:
                proven_truth = decorated_relation_prover(*args, **kwargs)
            proven_expr = proven_truth.expr
            if not isinstance(proven_expr, Equals):
                raise TypeError(
                        "@equality_prover, %s, expected to prove an "
                        "Equals expression, not %s of type %s."
                        %(func, proven_expr, proven_expr.__class__))
            if is_evaluation_method or (
                    is_shallow_simplification_method and
                    kwargs.get('must_evaluate', False)==True):
                # The right side of an evaluation must be irreducible.
                from proveit.logic import is_irreducible_value
                if not is_irreducible_value(proven_expr.rhs):
                    raise EvaluationError(_self)
            return proven_truth

        _equality_prover_fn_to_tenses[wrapper] = (past_tense, present_tense)
        extra_doc = """
        '%s' returns the right-hand side of '%s'.
        '%s', called on an InnerExpr of a Judgment,
        substitutes the right-hand side of '%s' for
        the inner expression.            
        """%(past_tense, name, present_tense, name)
        return _wraps(func, wrapper, extra_doc=extra_doc)

    return wrapper_maker

def auto_equality_prover(past_tense, present_tense):
    return equality_prover(past_tense, present_tense, automatic=True)

"""
def equality_prover(past_tense, present_tense):
    '''
    @equality_prover works the same way as the @prover decorator
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
                raise TypeError("@equality_prover expected to prove a "
                                "TranstiveRelation expression (more "
                                "specifically, the EquivalenceClass type of "
                                "relation), not %s of type %s"
                                %(proven_expr, proven_expr.__class__))
            if not isinstance(proven_expr, 
                              proven_expr.__class__.EquivalenceClass()):
                raise TypeError("@equality_prover expected to prove a "
                                "TranstiveRelation of the EquivalenceClass, "
                                "not %s of type %s"
                                %(proven_expr, proven_expr.__class__))
            if proven_expr.lhs != self.func.__self__:
                raise TypeError("@equality_prover expected to prove an "
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

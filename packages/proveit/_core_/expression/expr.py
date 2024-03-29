"""
This is the expression module.
"""

from proveit.util import OrderedSet
from proveit._core_.defaults import (defaults, USE_DEFAULTS, 
                                     SimplificationDirectives)
from proveit._core_.theory import Theory
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_._unique_data import meaning_data, style_data
from proveit.decorators import (
    prover, relation_prover, equality_prover,
    _equality_prover_fn_to_tenses)
import sys
import re
import inspect
import urllib.request
import urllib.parse
import urllib.error
from base64 import encodebytes
from copy import copy

class ExprType(type):
    '''
    By overriding the Expression type, we can make Operation-type
    expressions automatically populate the Operation.operation_class_of_operator
    when any Expression class is provided with an '_operator_' class attribute.
    '''

    # These attributes should not be overridden by classes outside
    # of the core.
    protected = {'_apply', 'replaced', 'basic_replaced', 'instance_context',
                 '_replaced_entries', 
                 'equality_replaced', '_manual_equality_replaced',
                 '_auto_simplified', '_auto_simplified_sub_exprs',
                 '_range_reduction', 'relabeled',
                 'sub_expr_substitution',
                 'canonically_labeled', 'canonical_form',
                 '_make', '_checked_make', '_reduced', '_used_vars',
                 '_free_var_ranges', '_parameterized_var_ranges',
                 '_repr_html_', '_core_info',
                 '_sub_expressions', '_canonically_labeled',
                 '_meaning_data', '_meaning_id',
                 '_style_data', '_style_id',
                 'is_parameter_independent', 'literal_int_extent'}

    def __new__(meta, name, bases, attrs):
        # Tip from
        # https://stackoverflow.com/questions/3948873
        #             /prevent-function-overriding-in-python
        core_package = 'proveit._core_'
        if attrs['__module__'][:len(core_package)] != core_package:
            for attribute in attrs:
                if attribute in ExprType.protected:
                    raise AttributeError('Overriding of attribute "%s" '
                                         'not allowed.' % attribute)
        return super().__new__(meta, name, bases, attrs)

    def __init__(cls, *args, **kwargs):
        type.__init__(cls, *args, **kwargs)
        
        # Register the '_operator_' if there is one.
        if hasattr(cls, '_operator_'):
            from proveit._core_.expression.operation import Operation
            from proveit._core_.expression.label.literal import Literal
            if issubclass(cls, Operation):
                if not isinstance(cls._operator_, Literal):
                    raise TypeError("'_operator_' class attributes must be "
                                    "Literal expressions.")
                Operation.operation_class_of_operator[cls._operator_] = cls
                
        if hasattr(cls, '_simplification_directives_'):
            simplification_directives = cls._simplification_directives_
            if not isinstance(simplification_directives, 
                              SimplificationDirectives):
                raise TypeError(
                        "%s._simplification_directives_ expected to be "
                        "of type SimplificationDirectives")
            simplification_directives._expr_class = cls
        if not hasattr(cls, '__init__'):
            raise TypeError("%s, an Expression-derived class, must have an "
                            "__init__ method"%cls)
        
        # Check that the __init__ method of the Expression class
        # has a 'styles' method that is keyword only.
        def raise_invalid_styles_init_arg():
            raise TypeError(
                    "The __init__ method of %s, an Expression-derived "
                    "class must accept 'styles' as a keyword-only "
                    "argument, with 'None' as its default if it has a one. "
                    "Simply pass the 'styles' along to parent __init__ "
                    "method)."%cls)            
        init_sig = inspect.signature(cls.__init__)
        if 'styles' not in init_sig.parameters.keys():
            raise_invalid_styles_init_arg()
        styles_param = init_sig.parameters['styles']
        if (styles_param.kind != inspect.Parameter.KEYWORD_ONLY or
                styles_param.default not in (None, inspect.Parameter.empty)):
            raise_invalid_styles_init_arg()
        
        # Register @equality_prover methods.
        for attr, val in list(cls.__dict__.items()):
            if callable(val) and val in _equality_prover_fn_to_tenses:
                fn = val
                past_tense, present_tense = _equality_prover_fn_to_tenses[fn]
                cls._register_equality_method(
                        fn, past_tense, present_tense)

    def _register_equality_method(
            cls, equality_method, past_tense_name, present_tense_name):
        '''
        Register a method of an expression class that is used to derive
        and return (as a Judgment) the equivalence of that expression 
        on the left side with a new form on the right side.
        (e.g., 'simplification', 'evaluation', 'commutation', 
        'association').
        In addition to the expression class and the method (as a name or 
        function object), also provide the "past-tense" form of the name 
        for deriving the equivalence and returning the right side, and 
        provide the "action" form of the name that may be used to make
        the replacement directly within a Judgment to produce a revised 
        Judgment.  The "past-tense" version will be added automatically
        as a method to the given expression class with an appropriate
        doc string.
        '''
        if not isinstance(equality_method, str):
            # can be a string or a function:
            equality_method = equality_method.__name__
        if not hasattr(cls, equality_method):
            raise Exception(
                "Must have '%s' method defined in class '%s' in order to "
                "register it as an equivalence method in InnerExpr." %
                (equality_method, str(cls)))
    
        # Store information in the Expression class that will enable 
        # calling InnerExpr methods when an expression of that type
        # is the inner expression for generating equivalences or
        # performing in-place replacements.
        setattr(
            cls, '_equiv_method_%s_' %
            equality_method, ('equiv', equality_method))
        setattr(
            cls, '_equiv_method_%s_' %
            past_tense_name, ('rhs', equality_method))
        setattr(
            cls, '_equiv_method_%s_' %
            present_tense_name, ('action', equality_method))
    
        # Automatically create the "past-tense" equivalence method for
        # the expression class which returns the right side.
        """
        # Doesn't work with overloading.  Must be fixed. To use this
        # check.
        if hasattr(cls, past_tense_name):
            raise Exception(
                "Should not manually define '%s' in class '%s'.  This "
                "'past-tense' equivalence method will be generated "
                "automatically by registering it in InnerExpr." %
                (past_tense_name, str(cls)))
        """
    
        def equiv_rhs(expr, *args, **kwargs):
            return getattr(expr, equality_method)(*args, **kwargs).rhs
        equiv_rhs.__name__ = past_tense_name
        equiv_rhs.__doc__ = (
                "Return an equivalent form of this expression derived "
                "via '%s'."% equality_method)
        setattr(cls, past_tense_name, equiv_rhs)


class Expression(metaclass=ExprType):
    # (expression, assumption) pairs for which conclude is in progress, 
    # tracked to prevent infinite recursion in the `prove` method.
    in_progress_to_conclude = set()
    
    # (expression, assumption) pairs for which '_readily_provable' is
    # in progress. Tracked to prevent infinite recursion.
    in_progress_to_check_provability = set()

    # Map "labeled" meaning data to "canonical" meaning data.
    labeled_to_canonical_meaning_data = dict()
    
    # Map canonincal forms to sets of expressions with that canonical
    # form and vice-versa.
    canonical_form_to_exprs = dict()    
    expr_to_canonical_form = dict()

    # Map Expression classes to their proper paths (as returned
    # by the Expression._class_path method).
    class_paths = dict()
    
    """
    # Map simplification directive identifiers to expressions
    # that have been simplified under the corresponding directive.
    # See decorators.py in the proveit package.
    simplified_exprs = dict()
    """

    """
    # Map "labeled meaning ids" of expressions to default styles.
    # That is, expressions with a specific labeling will establish
    # default styles; expressions with the same meaning but different
    # labels with have their own separate default style.
    default_labeled_expr_styles = dict()
    """

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        assert len(Expression.in_progress_to_conclude) == 0, (
                "Unexpected remnant 'in_progress_to_conclude' items "
                "(should have been temporary)")
        assert len(Expression.in_progress_to_check_provability) == 0, (
                "Unexpected remnant 'in_progress_to_check_provability'"
                "items (should have been temporary)")
        Expression.labeled_to_canonical_meaning_data.clear()
        Expression.canonical_form_to_exprs.clear()
        Expression.expr_to_canonical_form.clear()
        Expression.class_paths.clear()
        #Expression.default_labeled_expr_styles.clear()

    def __init__(self, core_info, sub_expressions=tuple(), *, styles):
        '''
        Initialize an expression with the given core_info (information relevant
        at the core Expression-type level) which should be a list (or tuple) of
        strings, and a list (or tuple) of sub_expressions.  "styles" is a
        dictionary used to indicate how the Expression should be formatted
        when there are different possibilities (e.g. division with '/' or as a
        fraction).  The meaning of the expression is independent of its styles
        signature.
        '''
        from proveit._core_.theory import UnsetCommonExpressionPlaceholder
        for core_info_elem in core_info:
            if not isinstance(core_info_elem, str):
                raise TypeError(
                    'Expecting core_info elements to be of string type')
        for sub_expression in sub_expressions:
            if isinstance(sub_expression, UnsetCommonExpressionPlaceholder):
                sub_expression.raise_attempted_use_error()
            if not isinstance(sub_expression, Expression):
                raise TypeError(
                    'Expecting sub_expression elements to be of Expression type')

        # note: these contained expressions are subject to style changes on an
        # Expression instance basis
        self._sub_expressions = tuple(sub_expressions)

        # check for illegal characters in core-info or styles
        if any(',' in info for info in core_info):
            raise ValueError("core_info is not allowed to contain a comma.")
        if styles is not None:
            ignore_inapplicable_styles = (
                    styles.pop('__IGNORE_INAPPLICABLE_STYLES__', False))
            for style in styles.values():
                if not {',', ':', ';'}.isdisjoint(style):
                    raise ValueError(
                        "Styles are not allowed to contain a ',', ':', or ';'.  Just use spaces.")
        else:
            ignore_inapplicable_styles = False

        # Create the "labeled" meaning data.  This is data common
        # to equivalent expressions which use the same lambda labels.
        # This isn't the "true" meaning data which is based upon using
        # "canonical" lambda labels.
        def object_rep_fn(expr): return hex(expr._labeled_meaning_id)
        self._labeled_meaning_data = meaning_data(
            self._generate_unique_rep(object_rep_fn, core_info))
        if not hasattr(self._labeled_meaning_data, '_core_info'):
            # initialize the data of self._labeledMeaningData
            self._labeled_meaning_data._core_info = tuple(core_info)

        # reference this unchanging data of the unique 'labeled meaning'
        # data.
        self._labeled_meaning_id = self._labeled_meaning_data._unique_id
        self._core_info = self._labeled_meaning_data._core_info
        # The "true" meaning "data" and id (based upon the canonical
        # version of the exrpession) will be generated on demand,
        # when expressions are compared (__eq__) or hashed (__hash__).

        if styles is None:
            styles = dict()
        style_options = self.style_options()
        """
        if (defaults.use_consistent_styles and 
                self._labeled_meaning_id in 
                Expression.default_labeled_expr_styles):
            # Any styles that have not been explicitly set will
            # use the default style for an expression of this "meaning".
            styles_to_emulate = (
                Expression.default_labeled_expr_styles[self._labeled_meaning_id])
            option_names = set(style_options.option_names())
            for name, val in styles_to_emulate.items():
                if name not in styles and name in option_names:
                    styles[name] = val
        """
        styles = style_options.standardized_styles(
                styles, ignore_inapplicable_styles=ignore_inapplicable_styles)

        # The style data is shared among Expressions with the same structure
        # and style -- this will contain the 'png' generated on demand.
        self._style_data = style_data(
            self._generate_unique_rep(lambda expr: hex(expr._style_id),
                core_info, styles, style_options))
        # initialize the style options
        # formatting style options that don't affect the meaning of the
        # expression
        self._style_data.styles = styles
        self._style_id = self._style_data._unique_id
        
        if (styles == style_options.canonical_styles() and
                len(self._sub_expressions) == 0):
            # When there are no sub-expressions, we can immediately
            # declare that the canonical expression is simply "self"
            # and the "true" meaning data is the "labeled" meaning data.
            self._canonically_labeled = self
            self._meaning_data = self._labeled_meaning_data
            self._meaning_id = self._meaning_data._unique_id
        
        # Track the number of potentially-independent interanally
        # bound variables to simplify generating a canonical form.
        # This number will be increased in Lambda.__init__ according
        # to the number of its parameters.
        if len(self._sub_expressions) == 0:
            self._num_indep_internal_bound_vars = 0
        else:
            self._num_indep_internal_bound_vars = max(
                    subexpr._num_indep_internal_bound_vars for 
                    subexpr in self._sub_expressions)
        """
        if defaults.use_consistent_styles:
            # Make this the default style.
            Expression.default_labeled_expr_styles[
                    self._labeled_meaning_id] = styles
        """

    def canonically_labeled(self):
        '''
        Retrieve (and create if necessary) the canonical version of this
        expression in which deterministic 'dummy' variables are used as
        Lambda parameters, determining the 'meaning' of the expression.
        '''
        if hasattr(self, '_canonically_labeled'):
            return self._canonically_labeled
        if hasattr(self, '_meaning_data'):
            # Set via '_meaning_data':
            self._canonically_labeled = self._meaning_data.canonically_labeled
            return self._canonically_labeled
        labeled_to_canonical_meaning_data = (
            Expression.labeled_to_canonical_meaning_data)
        if self._labeled_meaning_data in labeled_to_canonical_meaning_data:
            # Set the '_meaning_data' via '_labeled_meaning_data' and
            # 'labeled_to_canonical_meaning_data'.
            self._meaning_data = (
                labeled_to_canonical_meaning_data[self._labeled_meaning_data])
            self._meaning_id = self._meaning_data._unique_id
            # Now we can set the _canonically_labeled via the
            # '_meaning_data'.
            return self.canonically_labeled()

        # Get the canonical labeling of the sub-expressions.
        canonical_sub_expressions = tuple(
            sub_expr.canonically_labeled()
            for sub_expr in self._sub_expressions)
        # Get the styles of the sub expressions.
        sub_expression_styles = tuple(sub_expr._style_data
                                      for sub_expr in self._sub_expressions)
        # Get the styles of the canonical versions of the
        # sub-expressions.
        canonical_sub_expression_styles = \
            tuple(canonical_sub_expr._style_data
                  for canonical_sub_expr in canonical_sub_expressions)
        
        # See if this is a canonical version already by virtue of having
        # canonical styles and sub-expressions.
        style_options = self.style_options()
        canonical_styles = style_options.canonical_styles()
        if (self._style_data.styles == canonical_styles and
                sub_expression_styles == canonical_sub_expression_styles):
            # This is the canonical version.
            self._canonically_labeled = self
            return self

        # The 'canonical' sub-expressions are different than the
        # sub-expressions, so that propagates to this Expression's
        # canonical version.
        """
        with defaults.temporary() as temp_defaults:
            # Force the canonical styles.
            temp_defaults.use_consistent_styles = False
            canonically_labeled = self.__class__._checked_make(
                self._core_info, canonical_sub_expressions, 
                style_preferences=canonical_styles)
        """
        canonically_labeled = self.__class__._checked_make(
            self._core_info, canonical_sub_expressions, 
            style_preferences=canonical_styles)
        assert (canonically_labeled.canonically_labeled() ==
                canonically_labeled), (
                        "The canonical version of a canonical expression "
                        "should be itself.")
        self._canonically_labeled = canonically_labeled
        return canonically_labeled

    def canonical_form(self):
        '''
        Returns a form of this expression that should be provably
        equal to the original, assuming the original expression is
        known not to be "garbage" (e.g., proper types, no division
        by zero, etc.).
        
        For example,
            "a + b + c + d" and "d + c + a + b" should have the
        same canonical forms (which has an arbitrary but
        deterministic order for the terms) and we can prove that these 
        are equal as long as we know that a, b, c, and d are numbers
        (members of the set of complex numbers).
        
        See _build_canonical_form: this method should be overriden by
        each Expression type for build type-specific canonical forms.
        '''
        if self in Expression.expr_to_canonical_form:
            cf = Expression.expr_to_canonical_form[self]
        else:
            cf = self._build_canonical_form()
            Expression.expr_to_canonical_form[self] = cf
            if cf in Expression.expr_to_canonical_form:
                cf_of_cf = Expression.expr_to_canonical_form[cf]
                if cf != cf_of_cf:
                    raise ValueError("Inconsistent canonical forms: %s vs %s"
                                     %(cf, cf_of_cf))
            else:
                Expression.expr_to_canonical_form[cf] = cf
            Expression.canonical_form_to_exprs.setdefault(
                    cf, OrderedSet()).update({self, cf})
        return cf

    def _build_canonical_form(self):
        '''
        Build the canonical form of the Expression (see the
        Expression.canonical_form method).  Override to build
        type-specific canonical forms.  By default, recurse to
        use canonical forms of sub-expressions.        
        '''
        canonical_sub_exprs = []
        has_distinct_canonical_form = False
        for sub_expr in self.sub_expr_iter():
            canonical_sub_expr = sub_expr.canonical_form()
            if sub_expr != canonical_sub_expr:
                has_distinct_canonical_form = True
            canonical_sub_exprs.append(canonical_sub_expr)
        if has_distinct_canonical_form:
            # Use the canonical forms of the sub-expressions.
            return self._checked_make(
                self._core_info, canonical_sub_exprs,
                style_preferences=self._style_data.styles)
        else:
            # No canonical form that is different from self.
            return self
    
    @equality_prover('canonical_equated', 'canonical_equate')
    def deduce_canonically_equal(self, rhs, **defaults_config):
        '''
        Prove that this expression is equal another one that has the
        same canonical form.  Calls '_deduce_canonically_equal' which 
        may have type-specific implementations.
        '''
        from proveit import Judgment, UnsatisfiedPrerequisites
        from proveit.logic import Equals
        lhs = self
        lhs_cf = lhs.canonical_form() 
        rhs_cf = rhs.canonical_form()
        if lhs_cf != rhs_cf:
            raise UnsatisfiedPrerequisites(
                    "'deduce_canonically_equal' can only be used to prove "
                    "equality between expressions with the same canonical "
                    "form. %s and %s have distinct canonical forms "
                    "%s and %s respectively"%(lhs, rhs, lhs_cf, rhs_cf))
        if lhs == lhs_cf or (type(lhs) == type(lhs_cf) and
                             type(rhs) != type(lhs_cf)):
            # If the lhs is already in the canonical form or
            # if the lhs has the same type as the canonical form but
            # the rhs does not, deduce the equality from the other side.
            proven_eq = rhs._deduce_canonically_equal(lhs)
            proven_eq = proven_eq.derive_reversed()
        else:
            proven_eq = self._deduce_canonically_equal(rhs)
        if not isinstance(proven_eq, Judgment):
            raise TypeError("Expecting a proven Judgment to be returned "
                            "by '_deduce_canonically_equal")
        equality = Equals(lhs, rhs)
        if not defaults.auto_simplify and len(defaults.replacements)==0 and (
                proven_eq.expr != equality):
            raise ValueError("Expecting '_deduce_canonically_equal' to "
                             "return %s but got %s"%(
                                     equality, proven_eq.expr))
        return proven_eq
                                               
    def _deduce_canonically_equal(self, rhs):
        '''
        Helper method for 'deduce_canonically_equal'.  Typically, this 
        should have a type-specific implementation if 
        '_build_canonical_form' is type-specific.
        '''
        # The generic version will work via direct substitutions 
        # equating sub-expressions that differ.
        from proveit.logic import Equals
        equality = Equals(self, rhs)
        return equality.conclude_via_direct_substitution() 
                                               
    def _establish_and_get_meaning_id(self):
        '''
        The "meaning" of an expression is determined by it's
        canonical version and is only established as needed (on demand).
        Return the "meaning id" after it is established.
        '''
        if hasattr(self, '_meaning_id'):
            return self._meaning_id
        canonically_labeled = self.canonically_labeled()
        if hasattr(self, '_meaning_id'):
            # It may have been set via the 'canonically_labeled' call.
            return self._meaning_id
        if canonically_labeled is self:
            # The "true" meaning data is the "labeled" meaning data.
            self._meaning_data = self._labeled_meaning_data
        else:
            canonically_labeled._establish_and_get_meaning_id()
            self._meaning_data = canonically_labeled._meaning_data
        if not hasattr(self._meaning_data, 'canonically_labeled'):
            # store the canonical expression for future reference
            self._meaning_data.canonically_labeled = canonically_labeled
        # Anything with the same "labeled meaning data" must have the
        # same "canonical meaning data".
        labeled_to_canonical_meaning_data = \
            Expression.labeled_to_canonical_meaning_data
        labeled_to_canonical_meaning_data[self._labeled_meaning_data] = \
            self._meaning_data
        self._meaning_id = self._meaning_data._unique_id
        return self._meaning_id

    def _generate_unique_rep(self, object_rep_fn, core_info=None, 
                             styles=None, style_options=None):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        if core_info is None:
            core_info = self._core_info
        if styles is None and hasattr(self, '_style_data'):
            styles = self._style_data.styles
            style_options = self.style_options()
        if styles is not None:
            canonical_styles = style_options.canonical_styles()
            style_str = ','.join(style_name + ':' + styles[style_name]
                                 for style_name in sorted(styles.keys())
                                 if styles[style_name] != canonical_styles.get(
                                         style_name, None))
        else:
            style_str = ''
        sub_expr_info = ','.join(object_rep_fn(expr)
                                 for expr in self._sub_expressions)
        # Note: putting the sub-expressions at the front makes it convenient
        # to just grab that piece which is used when adding or removing
        # references to stored information.
        return '%s;%s;%s;%s' % (sub_expr_info, self._class_path(),
                                ','.join(core_info), style_str)
    #self._class_path() + '[' + ','.join(core_info) + ']' + style_str + ';[' +  + ']'

    def _class_path(self):
        ExprClass = self.__class__
        if ExprClass in Expression.class_paths:
            return Expression.class_paths[ExprClass]
        class_module = sys.modules[ExprClass.__module__]
        if hasattr(class_module, '__file__'):
            theory = Theory(class_module.__file__)
        else:
            theory = Theory()  # use the current directory if using the main module
        # get the full class path relative to the root theory where the class
        # is defined
        class_path = theory.name + '.' + \
            ExprClass.__module__.split('.')[-1] + '.' + ExprClass.__name__
        # Store for future reference:
        Expression.class_paths[ExprClass] = class_path
        return class_path

    @staticmethod
    def _parse_unique_rep(unique_rep):
        sub_expr_info, expr_class_str, core_info_str, style_str = \
            unique_rep.split(';')
        core_info = [_ for _ in core_info_str.split(',') if _ != '']
        style_pairs = [_ for _ in style_str.split(',') if _ != '']
        style_dict = dict(style_pair.split(':') for style_pair in style_pairs)
        sub_expr_refs = [_ for _ in sub_expr_info.split(',') if _ != '']
        return expr_class_str, core_info, style_dict, sub_expr_refs

    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        sub_expr_end = unique_rep.find(';')
        ref_info = unique_rep[:sub_expr_end]
        # Split by ',' or ';' to get the individual reference ids.
        return [_ for _ in re.split(',|;', ref_info) if _ not in ('', '.')]

    def __setattr__(self, attr, value):
        '''
        Expressions should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).
        '''
        if attr[0] != '_' and attr in self.__dict__:
            raise Exception("Attempting to alter read-only value '%s'" % attr)
        self.__dict__[attr] = value

    def __repr__(self):
        return str(self)  # just use the string representation

    def __eq__(self, other):
        if isinstance(other, Expression):
            if self._labeled_meaning_id == other._labeled_meaning_id:
                # Equal in a strong sense -- not only the same meaning
                # but the same labeling.
                return True
            return (self._establish_and_get_meaning_id() ==
                    other._establish_and_get_meaning_id())
        else:
            return False  # other must be an Expression to be equal to self

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._establish_and_get_meaning_id()

    def __str__(self):
        '''
        Return a string representation of the Expression.
        '''
        return self.string()

    def string(self, **kwargs):
        '''
        Return a string representation of the Expression.  The kwargs can contain formatting
        directives (such as 'fence' used to indicate when a sub-expression should be wrapped in
        parentheses if there can be ambiguity in the order of operations).
        '''
        raise NotImplementedError(
            "'string' method not implemented for " + str(self.__class__))

    def latex(self, **kwargs):
        '''
        Return a latex-formatted representation of the Expression.  The kwargs can contain formatting
        directives (such as 'fence' used to indicate when a sub-expression should be wrapped in
        parentheses if there can be ambiguity in the order of operations).
        '''
        raise NotImplementedError(
            "'latex' method not implemented for " + str(self.__class__))

    def formatted(self, format_type, **kwargs):
        '''
        Returns a formatted version of the expression for the given format_type
        ('string' or 'latex').  In the keyword arguments, fence=True indicates
        that parenthesis around the sub-expression may be necessary to avoid
        ambiguity.
        '''
        if format_type == 'string':
            return self.string(**kwargs)
        if format_type == 'latex':
            return self.latex(**kwargs)

    @classmethod
    def _make(cls, core_info, sub_expressions, *, styles, 
              canonically_labeled=None):
        '''
        Should make the Expression object for the specific Expression sub-class
        based upon the core_info and sub_expressions.  Must be implemented for
        each core Expression sub-class that can be instantiated.
        '''
        raise MakeNotImplemented(cls)

    @classmethod
    def _checked_make(cls, core_info, sub_expressions, *, style_preferences,
                      canonically_labeled=None):
        '''
        Check that '_make' is done appropriately since it is not
        entirely within the control of the core.
        '''
        core_info = tuple(core_info)
        sub_expressions = tuple(sub_expressions)
        # Indicate that inapplicable styles can simply be ignored
        # rather than raising an expection.
        style_preferences = dict(style_preferences)
        style_preferences['__IGNORE_INAPPLICABLE_STYLES__'] = True
        if canonically_labeled is None:
            made = cls._make(core_info, sub_expressions,
                             styles=style_preferences)
        else:
            made = cls._make(core_info, sub_expressions,
                             canonically_labeled=canonically_labeled, 
                             styles=style_preferences)
        assert made._core_info == core_info, (
            "%s vs %s" % (made._core_info, core_info))
        assert made._sub_expressions == sub_expressions, (
            "%s vs %s" % (made._sub_expressions, sub_expressions))
        return made

    def core_info(self):
        '''
        Copy out the core information.
        '''
        return tuple(self._core_info)

    def sub_expr(self, idx):
        return self._sub_expressions[idx]

    def sub_expr_iter(self):
        '''
        Iterator over the sub-expressions of this expression.
        '''
        return iter(self._sub_expressions)

    def num_sub_expr(self):
        '''
        Return the number of sub-expressions of this expression.
        '''
        return len(self._sub_expressions)

    def inner_expr(self, assumptions=USE_DEFAULTS):
        '''
        Return an InnerExpr object to wrap the expression and
        access any inner sub-expression for the purpose of replacing
        the inner expression, or change its styles, or relabeling its
        variables.
        '''
        from .inner_expr import InnerExpr
        return InnerExpr(self, assumptions=assumptions)

    def style_options(self):
        '''
        Return a StyleOptions object that indicates the possible
        styles and values that is available to determine how
        this Expression may be presented.
        '''
        return StyleOptions(self)  # the default is empty

    def has_same_style(self, expr):
        '''
        Return True if this 'self' expression is the same as the given
        'expr' expression with the same style.
        '''
        return self._style_id == expr._style_id

    def with_styles(self, ignore_inapplicable_styles=False, **kwargs):
        '''
        Alter the styles of this expression, and anything containing 
        this particular expression object, according to kwargs.
        '''
        styles = dict(self._style_data.styles)
        # update the _styles, _style_rep, and _style_id
        styles.update(kwargs)
        return self._with_these_styles(
                styles, ignore_inapplicable_styles=ignore_inapplicable_styles)
    
    def with_default_style(self, name):
        '''
        Remove one of the styles from the styles dictionary for this
        expression.  Sometimes you want to remove a style and use
        default behavior (which is allowed to be different for string
        and LaTeX formatting).
        '''
        styles = dict(self._style_data.styles)
        styles.discard(name)
        return self._with_these_styles(styles)
    
    def _with_these_styles(self, styles, ignore_inapplicable_styles=False):
        '''
        Helper for with_styles and without_style methods.
        '''
        style_options = self.style_options()
        styles = style_options.standardized_styles(
                styles, ignore_inapplicable_styles)
        if styles == self._style_data.styles:
            return self  # no change in styles, so just use the original
        """
        if defaults.use_consistent_styles:
            Expression.default_labeled_expr_styles[
                    self._labeled_meaning_id] = styles
        """
        new_style_expr = copy(self)
        new_style_expr._style_data = style_data(
            new_style_expr._generate_unique_rep(lambda expr: hex(expr._style_id),
                styles=styles, style_options=style_options))
        new_style_expr._style_data.styles = dict(styles)
        new_style_expr._style_id = new_style_expr._style_data._unique_id
        return new_style_expr

    def with_matching_style(self, expr_with_different_style):
        '''
        Return the expression with the diffent style after making
        sure it as the same meaning as this original expression.
        '''
        if self != expr_with_different_style:
            raise ValueError(
                "'with_matching_style' must be an expression with "
                "the same meaning as self: %s ≠ %s."%
                (self, expr_with_different_style))
        return expr_with_different_style

    def with_mimicked_style(self, other_expr, *,
                            ignore_inapplicable_styles=False):
        '''
        Given an 'other_expr' with the same style options as
        'self', return self with a style that mimicks that
        of 'other_expr' just at the top level.
        '''
        if not ignore_inapplicable_styles:
            if (self.style_options().options != 
                    other_expr.style_options().options):
                raise ValueError(
                    "'other_expr' must be an expression with "
                    "the same style options as 'self'.")
        return self.with_styles(
                **other_expr.get_styles(),
                ignore_inapplicable_styles=ignore_inapplicable_styles)

    def style_names(self):
        '''
        Return the name of the styles that may be set.
        '''
        return list(self._style_data.styles.keys())

    def get_style(self, style_name, default=None):
        '''
        Return the current style setting for the given style name.
        '''
        if default is None:
            return self._style_data.styles[style_name]
        else:
            return self._style_data.styles.get(style_name, default)

    def get_styles(self):
        '''
        Return a copy of the internally maintained styles dictionary.
        '''
        return dict(self._style_data.styles)

    def remake_constructor(self):
        '''
        Method to call to reconstruct this Expression.  The default is the class name
        itself to use the __init__ method, but sometimes a different method is more
        appropriate for setting the proper style (e.g. the Frac method in
        proveit.numbers.division.divide which constructs a Div object with a different
        style).  This constructor method must be in the same module as the class.
        '''
        return self.__class__.__name__

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Expression.
        '''
        raise NotImplementedError(
            "remake_arguments method should be implemented for all ProveIt core Expression sub-classes.")

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  For example,
        ["with_wrapping_at(3)", "with_justification('right')"].
        '''
        return tuple()

    @prover
    def prove(self, **defaults_config):
        '''
        Attempt to prove this expression automatically under the
        given assumptions (if None, uses defaults.assumptions).  First
        it tries to find an existing Judgment, then it tries a simple
        proof by assumption (if self is contained in the assumptions),
        then it attempts to call the 'conclude' method.  If successful,
        the Judgment is returned, otherwise an exception is raised.
        Cyclic attempts to `conclude` the same expression under the
        same set of assumptions will be blocked, so `conclude` methods are
        free make attempts that may be cyclic.
        '''
        from proveit import Judgment, Assumption, ProofFailure
        from proveit.relation import Relation
        from proveit.logic import Not, TRUE, Equals
        assumptions = defaults.assumptions
        automation = defaults.conclude_automation

        if defaults.sideeffect_automation:
            # Generate assumption side-effects.
            Assumption.make_assumptions()

        # See if this Expression already has a legitimate proof.
        found_truth = Judgment.find_judgment(self, assumptions)
        if found_truth is not None:
            found_truth.with_matching_styles(
                self, assumptions)  # give it the appropriate style
            # found an existing Judgment that does the job!
            return found_truth

        if self in assumptions:
            # prove by assumption if self is in the list of assumptions.
            from proveit._core_.proof import Assumption
            return Assumption.make_assumption(self).proven_truth

        if not automation:
            raise ProofFailure(self, assumptions, "No pre-existing proof")

        if not self._readily_provable():
            # Maybe this Expression isn't readily provable by
            # expression-specific means (note that '_readily_provable'
            # is intended, not 'readily_provable'), but something else 
            # does with the same canonical form.
            # If it is a Relation, however, and it's canonical form is
            # not simply from the canonical form on each side, we 
            # should use its 'conclude' method instead to derive
            # the relation more directly.
            canonical_form = self.canonical_form()
            if canonical_form != TRUE and (
                    not self._is_effective_relation() or
                    canonical_form == Expression._build_canonical_form(self)):
                cf_to_proven_exprs = (
                        Judgment.canonical_form_to_proven_exprs)
                if canonical_form in cf_to_proven_exprs:
                    for proven_expr in cf_to_proven_exprs[canonical_form]:
                        if proven_expr != self and proven_expr.proven():
                            # Something with the same canonical form has 
                            # been proven under applicable assumptions.
                            # So prove what we want by equating it with what
                            # we know.
                            return Equals(proven_expr, 
                                          self).derive_right_via_equality()

        # Use Expression.in_progress_to_conclude set to prevent an infinite
        # recursion
        in_progress_key = (self, defaults.sorted_assumptions)
        if in_progress_key in Expression.in_progress_to_conclude:
            raise ProofFailure(
                self,
                assumptions,
                "Infinite 'conclude' recursion blocked.")
        Expression.in_progress_to_conclude.add(in_progress_key)

        try:
            concluded_truth = None
            if isinstance(self, Not):
                # if it is a Not expression, try conclude_negation on the
                # operand
                try:
                    concluded_truth = self.operands[0].conclude_negation(
                        assumptions=assumptions)
                except NotImplementedError:
                    pass  # that didn't work, try conclude on the Not expression itself
            if concluded_truth is None:
                try:
                    # first attempt to prove via implication
                    concluded_truth = self.conclude_via_implication(
                            assumptions=assumptions)
                except ProofFailure:
                    # try the 'conclude' method of the specific Expression
                    # class
                    concluded_truth = self.conclude(assumptions=assumptions)
            if concluded_truth is None:
                raise ProofFailure(
                    self, assumptions, "Failure to automatically 'conclude'")
            if not isinstance(concluded_truth, Judgment):
                raise ValueError(
                    "'conclude' method should return a Judgment "
                    "(or raise an exception), not %s"%concluded_truth)
            if concluded_truth.expr != self:
                raise ValueError(
                    "'conclude' method should return a Judgment for this Expression object: " + str(
                        concluded_truth.expr) + " does not match " + str(self))
            if not concluded_truth.assumptions.issubset(assumptions):
                raise ValueError("While proving " +
                                 str(self) +
                                 ", 'conclude' method returned a Judgment with extra assumptions: " +
                                 str(set(concluded_truth.assumptions) -
                                     assumptions))
            if concluded_truth.expr._style_id == self._style_id:
                # concluded_truth with the same style as self.
                return concluded_truth
            return concluded_truth.with_matching_styles(
                self, assumptions)  # give it the appropriate style
        except NotImplementedError:
            raise ProofFailure(
                self,
                assumptions,
                "'conclude' method not implemented for proof automation")
        finally:
            Expression.in_progress_to_conclude.remove(in_progress_key)

    def proven(self, assumptions=USE_DEFAULTS):
        '''
        Return True if and only if the expression is known to be true.
        '''
        from proveit import ProofFailure
        try:
            self.prove(assumptions=assumptions, automation=False)
            return True
        except ProofFailure:
            return False

    def readily_provable(self, assumptions=USE_DEFAULTS, 
                         must_be_direct=False,**kwargs):
        '''
        May return True only if we readily know that this expression,
        under the given assumptions, can be proven automatically and 
        easily through its 'conclude' method and will return True if
        it is already proven.
        
        If must_be_direct=False, we will check if an Expression with
        the same canonical form is provable.
        
        For special purposes, optional keyword arguments may be
        passed through to the _readily_provable method.
        '''
        from proveit import Judgment, ExprTuple
        from proveit.logic import TRUE

        if isinstance(self, ExprTuple):
            return False # An ExprTuple cannot be true or false.

        with defaults.temporary() as tmp_defaults:
            # Make sure we derive assumption side-effects first.
            if assumptions is not USE_DEFAULTS:
                tmp_defaults.assumptions = assumptions
            tmp_defaults.automation=False
                
            if self.proven(): # this will "make" the assumptions
                return True
            
            if not must_be_direct:
                # Maybe this Expression doesn't have a proof, but 
                # something else does with the same canonical form.
                cf = self.canonical_form()
                cf_to_proven_exprs = Judgment.canonical_form_to_proven_exprs
                if cf in cf_to_proven_exprs and cf != TRUE and (
                        not self._is_effective_relation() or
                        cf == Expression._build_canonical_form(self)):
                    # We must use the same stipulations as those
                    # used in Expression.prove for using a proven
                    # expression with the same canonical form.
                    for proven_expr in cf_to_proven_exprs[cf]:
                        if proven_expr != self and proven_expr.proven():
                            return True
            
            # Try something specific to the Expression.
            in_progress_key = (self, defaults.sorted_assumptions)
            if in_progress_key in Expression.in_progress_to_check_provability:
                # avoid infinite recursion by using
                # in_progress_to_check_provability
                return False
            try:
                Expression.in_progress_to_check_provability.add(
                        in_progress_key)
                if must_be_direct:
                    return self._readily_provable(must_be_direct=True,
                                                  **kwargs)
                return self._readily_provable(**kwargs)
            finally:
                Expression.in_progress_to_check_provability.remove(
                        in_progress_key)

    def _readily_provable(self, **kwargs):
        '''
        Override for Expression-specific strategies to see if the
        expression is readily provable.  May return True only if we
        readily know that this expression can be proven automatically
        and easily through its 'conclude' method.
        '''
        return False
    
    def _is_effective_relation(self):
        '''
        Return True if self is a Relation or the logical negation
        of a relation which is essentially also a relation.
        '''
        from proveit.relation import Relation
        from proveit.logic import Not
        return isinstance(self, Relation) or (
                isinstance(self, Not) and
                isinstance(self.operand, Relation))        

    @prover
    def disprove(self, **defaults_config):
        '''
        Attempt to prove the logical negation (Not) of this expression.
        If successful, the Judgment is returned, otherwise an exception
        is raised.  By default, this simply calls prove on the negated
        expression. Override `conclude_negation` for automation specific to
        the type of expression being negated.
        '''
        from proveit.logic import Not
        return Not(self).prove()

    def disproven(self, assumptions=USE_DEFAULTS):
        '''
        Return True if and only if the expression is known to be false.
        '''
        from proveit import ProofFailure
        try:
            self.disprove(assumptions=assumptions, automation=False)
            return True
        except ProofFailure:
            return False

    def readily_disprovable(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        May return True only if we readily know that this expression,
        under the given assumptions, can be disproven automatically 
        and easily through its 'conclude' method and will return True 
        if it is already disproven.

        For special purposes, optional keyword arguments may be
        passed through to the _readily_disprovable method.
        '''
        from proveit import ExprTuple
        from proveit.logic import Not
        if isinstance(self, ExprTuple):
            return False # An ExprTuple cannot be true or false.
        
        # Not._readily_provable will call _readily_disprovable on
        # its operand.
        return Not(self).readily_provable(assumptions=assumptions, )

    def _readily_disprovable(self, **kwargs):
        '''
        Override for Expression-specific strategies to see if the
        expression is readily disprovable.  May return True only if we
        readily know that this expression can be disproven automatically
        and easily through its 'conclude_negation' method.
        '''
        return False

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude this expression under the given assumptions,
        using automation specific to this type of expression.
        Return the Judgment if successful, or raise an exception.
        This is called by the `prove` method when no existing proof was found
        and it cannot be proven trivially via assumption or default_conclude.
        The `prove` method has a mechanism to prevent infinite recursion,
        so there are no worries regarding cyclic attempts to conclude an expression.

        As a rule of thumb, 'conclude' methods should only attempt
        one non-trivial strategy for the automation.  Simple checks if
        something is already known to be true is deemed "trivial".
        If everything fails, other methods could be recommended to the
        user to be attempted manually.
        '''
        raise NotImplementedError(
            "'conclude' not implemented for " + str(self.__class__))

    @prover
    def conclude_via_implication(self, **defaults_config):
        '''
        Attempt to conclude this expression via applying
        modus ponens of known implications.
        '''
        from proveit.logic import conclude_via_implication
        return conclude_via_implication(self)

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude the negation of this expression under the given
        assumptions, using automation specific to the type of expression being negated.
        Return the Judgment if successful, or raise an exception.
        This is called by the `prove` method of the negated expression
        when no existing proof for the negation was found.
        The `prove` method has a mechanism to prevent infinite recursion,
        so there are no worries regarding cyclic attempts to conclude an expression.
        '''
        raise NotImplementedError(
            "'conclude_negation' not implemented for " + str(self.__class__))

    def side_effects(self, judgment):
        '''
        Yield methods to attempt as side-effects when this expression
        is proven as a judgment.  These should each accept an
        'assumptions' parameter.
        These should be obvious and useful consequences, trivial and limited.
        There is no need to call this manually; it is called automatically when
        the corresponding Judgment is created.
        It also may be desirable to store the judgment for future automation.
        '''
        return iter(())
    
    def _record_as_proven(self, judgment):
        '''
        Record any Expression-specific information for future reference.
        '''
        pass
    
    @equality_prover('sub_expr_substituted', 'sub_expr_substitute')
    def sub_expr_substitution(self, new_sub_exprs, **defaults_config):
        '''
        Given new sub-expressions to replace existing sub-expressions,
        return the equality between this Expression and the new
        one with the new sub-expressions.
        '''
        raise NotImplementedError(
                "sub_expr_substitution method not implemented "
                "for %s"%self.__class__)

    """
    def is_simplified(self):
        directive_id = defaults.get_simplification_directives_id()
        return self in Expression.simplified_exprs.get(directive_id, tuple())
    """

    def complete_replaced(self, repl_map, *, allow_relabeling=False, 
                          requirements=None, equality_repl_requirements=None):
        '''
        Returns this expression with sub-expressions replaced
        according to the replacement map (repl_map) dictionary
        which maps Expressions to Expressions.  When used for
        instantiation, this should specifically map variables,
        indexed variables, or ranges of indexed variables to
        Expressions.  Additionally, if defaults.auto_simplify is
        True and/or defaults.equality_repl_map has applicable
        replacements, we may make automatic equality-based replacements
        subject to defaults.preserved_exprs limitations.

        If allow_relabeling is True then internal Lambda parameters
        may be replaced when it is a valid replacement of parameter(s)
        (i.e., Variable's, IndexedVar's, or an ExprRange of
        IndexedVar's, and unique parameter variables).
        Otherwise, the Lambda parameter variables will be masked
        within its scope.  Partial masked of a range of indexed
        varaibles is not allowed and will cause an error.
        For example, we cannot replace (x_1, ..., x_{n+1}) within
        (x_1, ..., x_n) -> f(x_1, ..., x_n).
        
        'requirements' (and defaults.assumptions) are used when an 
        operator is replaced by a Lambda map that has a range of 
        parameters (e.g., x_1, ..., x_n) such that the length of the 
        parameters and operands must be proven to be equal. For more 
        details, see Operation.replaced, Lambda.apply, and 
        ExprRange.replaced (which is the sequence of calls involved).
        They may also be used to ensure indices match when performing
        parameter-dependent ExprRange expansions that require indices
        to match.  'requirements' are also needed to perform ExprRange
        reductions (for empty or singular ExprRanges).  When equality-
        based replacements are made, the equality requirements are
        recorded in both requirements and equality_repl_requirements.

        Also applies any enabled automatic simplifcations and
        explicit replacements -- that is why this version is "complete".
        '''
        if requirements is None:
            requirements = []  # Not passing back requirements.
        if equality_repl_requirements is None:
            # Not passing back the equality replacement requirements.
            equality_repl_requirements = set()
        expr = self.basic_replaced(
            repl_map, allow_relabeling=allow_relabeling,
            requirements=requirements)
        new_equality_repl_requirements = []
        replaced_expr = expr.equality_replaced(
                new_equality_repl_requirements,
                auto_simplify_top_level=defaults.auto_simplify)
        requirements.extend(new_equality_repl_requirements)
        equality_repl_requirements.update(new_equality_repl_requirements)
        return replaced_expr

    def basic_replaced(self, repl_map, *, 
                       allow_relabeling=False, requirements=None):
        '''
        Implementation for Expression.replaced except for equality
        replacements.
        '''
        if len(repl_map) > 0 and (self in repl_map):
            return repl_map[self]
        else:
            sub_exprs = self._sub_expressions
            subbed_sub_exprs = tuple(
                    sub_expr.basic_replaced(
                            repl_map, allow_relabeling=allow_relabeling,
                            requirements=requirements)
                    for sub_expr in sub_exprs)
            if all(subbed_sub._style_id == sub._style_id for
                   subbed_sub, sub in zip(subbed_sub_exprs, sub_exprs)):
                # Nothing change, so don't remake anything.
                return self
            return self.__class__._checked_make(
                self._core_info, subbed_sub_exprs,
                style_preferences=self._style_data.styles)

    def equality_replaced(self, requirements,
                          auto_simplify_top_level=USE_DEFAULTS,
                          simplify_only_where_marked=False,
                          markers_and_marked_expr=None):
        '''
        Return something equal to this expression with replacements
        made via proven equalities, either simplifications or
        replacements specified in defaults.equality_repl_map (which maps
        expressions to equalities having the expression on the left side
        and replacement on the right side).
        
        If auto_simplify_top_level is False, don't simplify this 
        top-level expression.  If you re-derive something, you don't
        generally don't want to get back TRUE as the judgment.
        Deeper sub-expressions are fair game, however.
        '''
        from proveit import Judgment, Variable
        from proveit.logic import Equals
        
        if defaults.preserve_all:
            return self
        
        # Convert the replacements tuple to an equality_repl_map.
        equality_repl_map = dict()
        for replacement in defaults.replacements:
            if not isinstance(replacement, Judgment):
                raise TypeError("The 'replacements' must be Judgments")
            if not isinstance(replacement.expr, Equals):
                raise TypeError(
                        "The 'replacements' must be equality Judgments")
            if replacement.expr.lhs == replacement.expr.rhs:
                # Don't bother with reflexive (x=x) reductions.
                continue
            equality_repl_map[replacement.expr.lhs] = replacement
        
        expr = self
        if len(equality_repl_map) > 0:
            expr = expr._manual_equality_replaced(
                    equality_repl_map, requirements=requirements,
                    stored_replacements=dict())
        if defaults.auto_simplify:
            with defaults.temporary() as temp_defaults:
                # Let's turn on automation while auto-simplifying at
                # least.
                temp_defaults.automation = True
                if simplify_only_where_marked:
                    markers, marked_expr = markers_and_marked_expr
                    for marker in markers:
                        if not isinstance(marker, Variable):
                            raise TypeError("'marker', should be a Variable. "
                                            "Got %s of type %s"
                                            %(marker, type(marker)))
                    if not isinstance(marked_expr, Expression):
                        raise TypeError("'marked_expr', should be an "
                                        "Expression. Got %s of type %s"
                                        %(marked_expr, type(marked_expr)))
                else:
                    markers_and_marked_expr = None
                try:
                    expr = expr._auto_simplified(
                        requirements=requirements,
                        stored_replacements=dict(),
                        auto_simplify_top_level=auto_simplify_top_level,
                        markers_and_marked_expr=markers_and_marked_expr)
                except MarkedExprError as e:
                    raise ValueError(
                        "%s doesn't match %s while delving into %s "
                        "which should match %s except where "
                        "marked by %s."
                        %(e.actual_subexpr, e.marked_expr_subexpr,
                          self, markers_and_marked_expr[1],
                          markers_and_marked_expr[0]))

        return expr

    def _manual_equality_replaced(self, equality_repl_map, *,
                                  requirements, stored_replacements):
        '''
        Helper method for equality_replaced which handles the manual
        replacements.
        '''
        from proveit import ExprRange, Judgment, Lambda, Conditional
        from proveit.logic import Equals
        if self in defaults.preserved_exprs:
            # This expression should be preserved, so don't make
            # any equality-based replacement.
            return self
        if self in equality_repl_map:
            replacement = equality_repl_map[self]
            if replacement.proven():
                # The replacement must be proven under current
                # assumptions (in the current scope) to be applicable.
                requirements.append(replacement)
                return replacement.expr.rhs
        elif self in stored_replacements:
            # We've handled this one before, so reuse it.
            return stored_replacements[self]
        # Recurse into the sub-expressions.
        new_requirements = []
        sub_exprs = self._sub_expressions
        if isinstance(self, Lambda):
            # Can't use assumptions involving lambda parameter 
            # variables. Also, don't replace lambda parameters.
            inner_assumptions = \
                [assumption for assumption in defaults.assumptions if
                 free_vars(assumption).isdisjoint(self.parameter_vars)]
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = inner_assumptions
                # Since the assumptions have changed, we can no longer
                # use the stored_replacements from before.
                subbed_body = self.body._manual_equality_replaced(
                        equality_repl_map, requirements=new_requirements, 
                        stored_replacements=dict())
            subbed_sub_exprs = (self.parameters, subbed_body)
        elif isinstance(self, Conditional):
            # Add the condition as an assumption for the equality
            # replacement of the value.
            recursion_fn = lambda expr, requirements, stored_repls, _ : (
                         expr._manual_equality_replaced(
                                 equality_repl_map,
                                 requirements=requirements, 
                                 stored_replacements=stored_repls))
            subbed_sub_exprs = self._equality_replaced_sub_exprs(
                    recursion_fn, requirements=requirements,
                    stored_replacements=stored_replacements)
        else:
            subbed_sub_exprs = \
                tuple(sub_expr._manual_equality_replaced(
                        equality_repl_map, requirements=new_requirements,
                        stored_replacements=stored_replacements)
                      for sub_expr in sub_exprs)
            
        if all(subbed_sub._style_id == sub._style_id for
               subbed_sub, sub in zip(subbed_sub_exprs, sub_exprs)):
            # Nothing changed, so don't remake anything.
            new_expr = self
        else:
            if isinstance(self, ExprRange):
                # This is an ExprRange.  If the start and end indices
                # are the same, force them to be different here
                # (we can't create an ExprRange where they are the same)
                # but it will be simplified in the containing ExprTuple
                # via a singlular range reduction.
                subbed_sub_exprs = ExprRange._proper_sub_expr_replacements(
                    sub_exprs, subbed_sub_exprs)
            new_expr = self.__class__._checked_make(
                self._core_info, subbed_sub_exprs,
                style_preferences=self._style_data.styles)   
        # Check if the revised expression has a replacement.
        if (new_expr is not self) and new_expr in equality_repl_map:
            replacement = equality_repl_map[new_expr]
            # The replacement must be proven under current
            # assumptions (in the current scope) to be applicable.           
            if replacement.proven():
                # The revised expression has a replacement, so use it
                # and make one requirement that encompasses the cascade
                # of replacements (sub-expressions and at this level).
                replacement1 = Equals(
                        self, new_expr).conclude_via_direct_substitution()
                requirement = replacement1.apply_transitivity(
                        replacement)
                new_expr = requirement.rhs
                assert (requirement.proven() and 
                        isinstance(requirement, Judgment) and
                        isinstance(requirement.expr, Equals) and
                        requirement.expr.lhs == self and
                        requirement.expr.rhs == new_expr)
                requirements.append(requirement)
        else:
            # Use each sub-expression replacement as-is.
            requirements.extend(new_requirements)
        stored_replacements[self] = new_expr
        return new_expr
    
    def _auto_simplified(
            self, *, requirements, stored_replacements,
            auto_simplify_top_level=USE_DEFAULTS,
            markers_and_marked_expr = None):
        '''
        Helper method for equality_replaced which handles the automatic
        simplification replacements.
        '''
        from proveit import Judgment, Operation, ExprRange   
        from proveit._core_.proof import (
                ProofFailure, UnsatisfiedPrerequisites)
        from proveit.logic import (Equals, SimplificationError,
                                   is_irreducible_value)

        if self in defaults.preserved_exprs:
            # This expression should be preserved, so don't 
            # auto-simplify.
            return self
        elif markers_and_marked_expr is not None:
            markers, marked_expr = markers_and_marked_expr
            if free_vars(marked_expr).isdisjoint(markers):
                # This is unmarked territory; preserve it.
                if self != marked_expr:
                    raise MarkedExprError(marked_expr, self)
                return self
            elif isinstance(marked_expr, Operation) and (
                    marked_expr.operator in markers):
                # If the operator is a marker then all of this
                # sub-expression is fair game for simplification
                # (the operation itself may have been substituted).
                markers_and_marked_expr = None
            elif len(self._sub_expressions) == 0 and (
                    len(marked_expr._sub_expressions) > 0):
                # The marked expression has sub-expressions, but self
                # does not.  That is a mismatch.
                raise MarkedExprError(marked_expr, self)

        elif self in stored_replacements:
            # We've handled this one before, so reuse it.
            return stored_replacements[self]

        # Recurse into the sub-expressions.
        new_requirements = []
        expr = self._auto_simplified_sub_exprs(
                requirements=new_requirements, 
                stored_replacements=stored_replacements,
                markers_and_marked_expr=markers_and_marked_expr)
        if (expr != self) and (expr in defaults.preserved_exprs):
            # The new expression should be preserved, so don't make
            # any further auto-simplification.
            requirements.extend(new_requirements)
            return expr
        if auto_simplify_top_level is USE_DEFAULTS:
            auto_simplify_top_level = defaults.auto_simplify
        replacement = None
        if (auto_simplify_top_level and not is_irreducible_value(expr)
              and not isinstance(expr, ExprRange)):
            if defaults.simplify_with_provable_evaluations:
                # Look for an readily provable evaluation.
                try:
                    replacement = Equals.get_readily_provable_evaluation(expr)
                except UnsatisfiedPrerequisites:
                    replacement = None
            elif defaults.simplify_with_known_evaluations:
                # Look for an explicitly known evaluation.
                try:
                    replacement = Equals.get_known_evaluation(expr)
                except UnsatisfiedPrerequisites:
                    replacement = None
            else:
                replacement = None
            if (replacement is None and 
                    hasattr(expr, 'shallow_simplification')):
                # Attempt a shallow simplification (after recursion).
                try:
                    replacement = expr.shallow_simplification(
                            must_evaluate=False)
                    if replacement.rhs == expr:
                        # Trivial simplification -- don't use it.
                        replacement = None
                except (SimplificationError, UnsatisfiedPrerequisites, 
                        NotImplementedError, ProofFailure):
                    # Failure in the simplification attempt; 
                    # just skip it.
                    pass
        if replacement is None:
            stored_replacements[self] = expr
            requirements.extend(new_requirements)
            return expr
        elif replacement.is_applicable():
            # We have a replacement here; make sure it is a valid one.
            if not isinstance(replacement, Judgment):
                raise TypeError("'replacement' must be a "
                                "proven equality as a Judgment: "
                                "got %s for %s" % (replacement, expr))
            if not isinstance(replacement.expr, Equals):
                raise TypeError("'replacement' must be a "
                                "proven equality: got %s for %s"
                                % (replacement, expr))
            if replacement.expr.lhs != expr:
                raise TypeError("'replacement' must be a "
                                "proven equality with 'self' on the "
                                "left side: got %s for %s"
                                % (replacement, expr))
            
            new_expr = replacement.expr.rhs
            if new_expr != expr and expr != self:
                # There was a simplification after sub-expressions have
                # been simplified.  Make one requirement that 
                # encompasses the cascade of simplifications 
                # (sub-expressions and at this level).
                replacement1 = Equals(self, expr)
                if not replacement1.proven():
                    replacement1.conclude_via_direct_substitution()
                replacement = replacement1.apply_transitivity(
                        replacement)
                assert (replacement.proven() and 
                        isinstance(replacement, Judgment) and
                        isinstance(replacement.expr, Equals) and
                        replacement.expr.lhs == self and
                        replacement.expr.rhs == new_expr)
                requirements.append(replacement)
            elif expr != self:
                # Just sub-expression simplifications.
                requirements.extend(new_requirements)
            else:
                # Just the simplification at this level.
                assert new_expr != expr
                requirements.append(replacement)
            stored_replacements[self] = new_expr
            return new_expr
        else:
            # The assumptions aren't adequate to use this reduction.
            return self

    def _auto_simplified_sub_exprs(
            self, *, requirements, stored_replacements,
            markers_and_marked_expr):
        '''
        Helper method for _auto_simplified to handle auto-simplification
        replacements for sub-expressions.
        '''
        # Recurse into the sub-expressions.
        sub_exprs = self._sub_expressions
        subbed_sub_exprs = \
            tuple(sub_expr._auto_simplified(
                    requirements=requirements, 
                    stored_replacements=stored_replacements,
                    markers_and_marked_expr=self._update_marked_expr(
                            markers_and_marked_expr, 
                            lambda _expr : _expr._sub_expressions[_k]))
                  for _k, sub_expr in enumerate(sub_exprs))
        if all(subbed_sub._style_id == sub._style_id for
               subbed_sub, sub in zip(subbed_sub_exprs, sub_exprs)):
            # Nothing change, so don't remake anything.
            return self
        return self.__class__._checked_make(
            self._core_info, subbed_sub_exprs,
            style_preferences=self._style_data.styles)

    def _update_marked_expr(self, markers_and_marked_expr,
                            sub_expr_fn):
        if markers_and_marked_expr is None:
            return None
        try:
            markers, marked_expr = markers_and_marked_expr
            if marked_expr in markers:
                # This entire sub-expression is marked, so we
                # all simplifications are fair game here.
                return None
            marked_expr = sub_expr_fn(marked_expr)
            assert isinstance(marked_expr, Expression)
            return (markers, marked_expr)
        except:
            raise MarkedExprError(marked_expr, self)
    
    def copy(self):
        '''
        Make a copy of the Expression with the same styles.
        '''
        # vacuous substitution makes a copy
        expr_copy = self.basic_replaced({})
        return expr_copy

    def _used_literals(self):
        '''
        Return all of the used Literals of this Expression,
        included those in sub-expressions.
        Call externally via the used_literals method in expr.py.
        '''
        return set().union(*[expr._used_literals() for
                             expr in self._sub_expressions])

    def _used_vars(self):
        '''
        Return all of the used Variables of this Expression,
        included those in sub-expressions.
        Call externally via the used_vars method in expr.py.
        '''
        return set().union(*[expr._used_vars() for
                             expr in self._sub_expressions])

    def _contained_parameter_vars(self):
        '''
        Return all of the Variables of this Expression that
        are parameter variables of a contained Lambda.
        '''
        return set().union(*[expr._contained_parameter_vars() for
                             expr in self._sub_expressions])

    def _free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free
        (not within a lambda map that parameterizes the base variable).
        Examples of "forms":
            x
            x_i
            x_1, ..., x_n
            x_{i, 1}, ..., x_{i, n_i}
            x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}
        
        Note: Lambda maps are not supposed to partially masked ranges
        of parameters.  For example,
        (x_1, ..., x_n) -> x_1 + ... + x_n + x_{n+1}
        is not proper.  However, it won't be caught until it
        really matters (an instantiation or relabeling is attempted
        that reveals the issue).  Meanwhile, we simply assume
        the masking is complete and report no ranges for x in
        this case (x is masked by the lambda map).

        If this Expression is in the exclusion set, or contributes
        directly to a form that is in the exclusions set, skip over it.
        For example, given the expression
            a*x_{i, 1} + ... + a*x_{i, n_1}
        if x_{i, 1}, ..., x_{i, n_i} is in the exclusion set,
        then 'a' will be the only free variable reported.

        Call externally via the free_var_forms method in expr.py.
        '''
        forms_dict = dict()
        if exclusions is not None and self in exclusions:
            return forms_dict  # this is excluded
        for expr in self._sub_expressions:
            for var, forms in \
                    expr._free_var_ranges(
                        exclusions=exclusions).items():
                forms_dict.setdefault(var, set()).update(forms)
        return forms_dict

    def safe_dummy_var(self):
        from proveit._core_.expression.label.var import safe_dummy_var
        return safe_dummy_var(self)

    def safe_dummy_vars(self, n):
        from proveit._core_.expression.label.var import safe_dummy_vars
        return safe_dummy_vars(n, self)
    
    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        If possible, return a Judgment of this expression equal to an
        irreducible value.  In the @equality_prover decorator
        for any 'evaluation' method, there is a check for an
        existing evaluation and a check that the resulting proven
        statement equates self with an irreducible value.
        
        See also Operation.evaluation, Expression.simplification,
        and Expression.shallow_simplification.
        '''
        from proveit.logic import EvaluationError
        # No other default options (though the Operation class
        # has some options via simplifying operands).
        raise EvaluationError(self)

    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        If possible, return a Judgment of this expression equal to an
        irreducible value.  This default raises an EvaluationError.
        '''       
        from proveit.logic import EvaluationError
        raise EvaluationError(self)

    @equality_prover('simplified', 'simplify')
    def simplification(self, **defaults_config):
        '''
        If possible, return a Judgment of this expression equal to a
        simplified form (according to strategies specified in 
        proveit.defaults).  In the @equality_prover decorator for any
        'simplification' method, there is a check for an existing 
        simplification, a check that the resulting proven statement is 
        an equality with self on the lhs, and it remembers the 
        simplification for next time.
        
        The default Expression.simplification only checks to see
        if there is an evaluation to be used as the simplification, but
        this may be overridden for particular Expression types.
        
        See also Operation.simplification and 
        Expression.shallow_simplification.

        '''
        # Resort to a shallow_simplification as the default.
        return self.shallow_simplification(must_evaluate=False)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False, 
                               **defaults_config):
        '''
        Attempt to simplify 'self' under the assumption that it's
        operands (sub-expressions) have already been simplified.
        Returns the simplification as a Judgment equality with 'self'
        on the left side.
        
        The default is to return the trivial reflexive equality.
        Must be overridden for class-specific simplification.
        '''
        from proveit.logic import Equals, is_irreducible_value
        if must_evaluate and not is_irreducible_value(self):
            raise NotImplementedError(
                "'shallow_simplification' applicable when 'must_evaluate' "
                "is True is not implemented for %s class" % str(
                    self.__class__))
        return Equals(self, self).conclude_via_reflexivity()

    @classmethod
    def simplification_directive_keys(cls, **kwargs):
        if not hasattr(cls, '_simplification_directives_'):
            raise AttributeError("%s has no _simplification_directives_ attribute" % cls)
        return [key for key in cls._simplification_directives_.__dict__.keys()
                if key[0] != '_']

    @classmethod
    def temporary_simplification_directives(cls, *, use_defaults=False):
        '''
        Returns a context manager for temporarily setting simplification
        directives for this expression class.  Specifically, the
        _simplification_directives_ attribute of the expression class
        will be temporarily altered.  An exception will be raised if
        the class has no _simplification_directives_ attribute.
        
        For example,
        
        with Add.temporary_simplification_directives() as tmp_directives:
            tmp_directives.ungroup = False
            ...
        
        will set the 'ungroup' attribute of 
        Add._simplification_directives_ to False but will restore it
        to its previous value upon exiting the 'with' block.
        
        If 'use_defaults' is True, the simplification directives will
        temporarily be set to the original values from when the
        SimplificationDirectives object was constructed
        
        See also change_simplification_directives.
        '''
        if not hasattr(cls, '_simplification_directives_'):
            raise AttributeError("%s has no _simplification_directives_ attribute" % cls)
        simplification_directives = cls._simplification_directives_
        if not isinstance(simplification_directives, SimplificationDirectives):
            raise TypeError(
                    "The '_simplification_directives_' of an Expression "
                    "class should be of type SimplificationDirectives")
        return simplification_directives.temporary(use_defaults=use_defaults)
    
    @classmethod
    def change_simplification_directives(cls, **kwargs):
        '''
        Change the simplification directives for a class.  This change
        is permanent, until it is changed back.
        
        See also tempary_simplification_directives.
        '''
        if not hasattr(cls, '_simplification_directives_'):
            raise AttributeError("%s has no _simplification_directives_ attribute" % cls)
        for key, val in kwargs.items():
            if key not in cls._simplification_directives_.__dict__:
                raise KeyError("'%s' is not a simplification directive "
                               "for %s"%(key, cls))
            if key[0] == '_':
                raise ValueError("Changing private data of the "
                                 "SimplificationDirective is not "
                                 "allowed")
            cls._simplification_directives_.__dict__[key] = val

    def order_of_appearance(self, sub_expressions):
        '''
        Yields the given sub-Expressions in the order in which they
        appear in this Expression.  There may be repeats.
        '''
        if self in sub_expressions:
            yield self
        for sub_expr in self._sub_expressions:
            for expr in sub_expr.order_of_appearance(sub_expressions):
                yield expr

    def literals_as_variables(self, *literals):
        '''
        Return this expression with instances of the given literals
        converted to corresponding variables.  
        '''
        return self.basic_replaced({lit:lit.as_variable() for lit in literals})

    def variables_as_literals(self, *literals):
        '''
        Return this expression with instances of the variables
        corresponding to the given literals converted to the literals.  
        '''
        return self.basic_replaced({lit.as_variable():lit for lit in literals})

    def _repr_html_(self, unofficial_name_kind_theory=None):
        '''
        Generate html to show a png compiled from the latex (that may be recalled
        from memory or storage if it was generated previously) with a link to
        an expr.ipynb notebook for displaying the expression information.
        If 'theory' is provided, find the stored expression information in
        that theory; otherwise, use the default, current directory Theory.
        If 'unofficial_name_kind_theory' is provided, it should be the
        (name, kind, theory) for a special expression that is not-yet-official
        (%end_[common/axioms/theorems] has not been called yet in the special
        expressions notebook).
        '''
        if not defaults.display_latex:
            return None  # No LaTeX display at this time.
        if not hasattr(self._style_data, 'png'):
            self._style_data.png, png_url = Theory._stored_png(
                self, self.latex(), self._config_latex_tool)
            self._style_data.png_url = png_url
        if self._style_data.png_url is not None:
            expr_notebook_rel_url = Theory.expression_notebook(
                self, unofficial_name_kind_theory)
            html = '<a class="ProveItLink" href="' + expr_notebook_rel_url + '">'
            if defaults.inline_pngs:
                encoded_png = encodebytes(self._style_data.png).decode("utf-8")
                html += '<img src="data:image/png;base64,' + encoded_png + \
                    r'" style="display:inline;vertical-align:middle;" />'
            else:
                html += '<img src="' + self._style_data.png_url + \
                    r'" style="display:inline;vertical-align:middle;" />'
            html += '</a>'
        return html

    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        for sub_expr in self._sub_expressions:
            sub_expr._config_latex_tool(lt)

    def expr_info(self, details=False):
        from proveit._core_.expression.expr_info import ExpressionInfo
        return ExpressionInfo(self, details)

    @relation_prover
    def derive_in_bool(self, **defaults_config):
        '''
        If the expression can be proven, it must
        be TRUE and therefore Boolean.
        '''
        from proveit import A
        from proveit.logic.booleans import in_bool_if_true
        return in_bool_if_true.instantiate({A: self})

def used_literals(expr):
    '''
    Return all of the used Literals of this Expression,
    included those in sub-expressions.
    '''
    return expr._used_literals()

def used_vars(expr):
    '''
    Return all of the used Variables of this Expression,
    included those in sub-expressions.
    '''
    return expr._used_vars()

def contained_parameter_vars(expr):
    '''
    Return all of the Variables of this Expression that may
    are parameter variables of a contained Lambda.
    '''
    return expr._contained_parameter_vars()


def free_var_ranges(expr, exclusions=None):
    '''
    Return the dictionary mapping Variables to forms w.r.t. ranges
    of indices (or solo) in which the variable occurs as free
    (not within a lambda map that parameterizes the base variable).    
    Examples of "forms":
        x
        x_i
        x_1, ..., x_n
        x_{i, 1}, ..., x_{i, n_i}
        x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}
    For example,
    (x_1, ..., x_n) -> x_1 + ... + x_n + x_{n+1}
    would report {x_{n+1}} for the x entry but not x_1, ..., x_n.
    In another example,
    (x_1, ..., x_n) -> x_1 + ... + x_k + x_{k+1} + ... + x_{n}
    would report {x_1, ..., x_k, x_{k+1}, ..., x_{n}} for the x
    entry because the masking is not "explicit" and actually depends
    upon what may be assumed about k.

    If this Expression is in the exclusion set, or contributes
    directly to a form that is in the exclusions set, skip over it.
    For example, given the expression
        a*x_{i, 1} + ... + a*x_{i, n_1}
    if x_{i, 1}, ..., x_{i, n_i} is in the exclusion set,
    then 'a' will be the only free variable reported.
    '''
    return expr._free_var_ranges(exclusions=exclusions)


def free_vars(expr):
    '''
    Returns the set of variables for that are free (unbound) in
    the given expression.
    For example, given
        (x_1, ..., x_n) -> x_1 + ... + x_{m}
    n is free.  Even though there is ambiguity about the range
    of indices of x on the right versus the left without knowing
    m relative to n, lambda maps in Prove-It are not allowed to
    partially mask a range of parameters (in this example, m>n
    is not allowed).  However, this restriction isn't enforced
    until it really matters.  When the ranges of x are relabeled
    or instantiated, then Prove-It will check that this
    restriction is satisfied.
    Axioms and theorems must not have any variables that are
    entirely free.
    '''
    from proveit._core_.expression.label.var import Variable
    from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
    if isinstance(expr, Variable):
        return {expr}
    fvars = set()
    for sub_expr in expr._sub_expressions:
        fvars.update(free_vars(sub_expr))
    if isinstance(expr, Lambda):
        return fvars.difference(expr.parameter_vars)
    return fvars


def expression_depth(expr):
    '''
    Returns the depth of the expression tree for the given expression.
    '''
    sub_depths = [expression_depth(sub_expr)
                  for sub_expr in expr.sub_expr_iter()]
    if len(sub_depths) == 0:
        return 1  # no sub-expressions
    # add 1 to the maximum of the sub-expression depths
    return max(sub_depths) + 1


def traverse_inner_expressions(expr):
    '''
    A simple algorithm to yield all inner expressions of an expression,
    including the expression itself.  These will be reported in a depth-
    first order.
    '''
    from proveit import Judgment
    if isinstance(expr, Judgment):
        expr = expr.expr
    yield expr
    for sub_expr in expr.sub_expr_iter():
        for inner_expr in traverse_inner_expressions(sub_expr):
            yield inner_expr


class MakeNotImplemented(NotImplementedError):
    def __init__(self, expr_sub_class):
        self.expr_sub_class = expr_sub_class

    def __str__(self):
        return "make method not implemented for " + str(self.expr_sub_class)


class ImproperReplacement(Exception):
    def __init__(self, orig_expr, repl_map, message):
        self.orig_expr = orig_expr
        self.repl_map = repl_map
        self.message = message

    def __str__(self):
        return ("Improper replacement of %s via %s:\n%s"
                % (self.orig_expr, self.repl_map, self.message))

class MarkedExprError(Exception):
    def __init__(self, marked_expr_subexpr, actual_subexpr):
        self.marked_expr_subexpr = marked_expr_subexpr
        self.actual_subexpr = actual_subexpr

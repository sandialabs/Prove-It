"""
This is the expression module.
"""

from proveit._core_.defaults import (defaults, USE_DEFAULTS, 
                                     SimplificationDirectives)
from proveit._core_.theory import Theory
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_._unique_data import meaning_data, style_data
from proveit.decorators import (prover, equality_prover,
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
    protected = ('_canonical_version',
                 'replaced', 'basic_replaced', '_replaced_entries', 
                 'equality_replaced', '_equality_replaced', 
                 '_equality_replaced_sub_exprs', '_range_reduction',
                 'relabeled',
                 '_make', '_checked_make', '_reduced', '_used_vars',
                 '_possibly_free_var_ranges', '_parameterized_var_ranges',
                 '_repr_html_', '_core_info',
                 '_sub_expressions', '_canonical_expr',
                 '_meaning_data', '_meaning_id',
                 '_style_data', '_style_id',
                 'is_parameter_independent', 'literal_int_extent')

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
    # (expression, assumption) pairs for which conclude is in progress, tracked to prevent infinite
    # recursion in the `prove` method.
    in_progress_to_conclude = set()

    # Map "labeled" meaning data to "canonical" meaning data.
    labeled_to_canonical_meaning_data = dict()

    # Map Expression classes to their proper paths (as returned
    # by the Expression._class_path method).
    class_paths = dict()
    
    # Map simplification directive identifiers to expressions
    # that have been simplified under the corresponding directive.
    # See decorators.py in the proveit package.
    simplified_exprs = dict()
    
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
        Expression.labeled_to_canonical_meaning_data.clear()
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
                core_info, styles))
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
            self._canonical_expr = self
            self._meaning_data = self._labeled_meaning_data
            self._meaning_id = self._meaning_data._unique_id
        
        """
        if defaults.use_consistent_styles:
            # Make this the default style.
            Expression.default_labeled_expr_styles[
                    self._labeled_meaning_id] = styles
        """

    def _canonical_version(self):
        '''
        Retrieve (and create if necessary) the canonical version of this
        expression in which deterministic 'dummy' variables are used as
        Lambda parameters, determining the 'meaning' of the expression.
        '''
        if hasattr(self, '_canonical_expr'):
            return self._canonical_expr
        if hasattr(self, '_meaning_data'):
            # Set via '_meaning_data':
            self._canonical_expr = self._meaning_data.canonical_expr
            return self._canonical_expr
        labeled_to_canonical_meaning_data = (
            Expression.labeled_to_canonical_meaning_data)
        if self._labeled_meaning_data in labeled_to_canonical_meaning_data:
            # Set the '_meaning_data' via '_labeled_meaning_data' and
            # 'labeled_to_canonical_meaning_data'.
            self._meaning_data = (
                labeled_to_canonical_meaning_data[self._labeled_meaning_data])
            self._meaning_id = self._meaning_data._unique_id
            # Now we can set the _canonical_expr via the '_meaning_data'.
            return self._canonical_version()

        # Get the canonical versions of the sub-expressions.
        canonical_sub_expressions = tuple(
            sub_expr._canonical_version()
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
            self._canonical_expr = self
            return self

        # The 'canonical' sub-expressions are different than the
        # sub-expressions, so that propagates to this Expression's
        # canonical version.
        """
        with defaults.temporary() as temp_defaults:
            # Force the canonical styles.
            temp_defaults.use_consistent_styles = False
            canonical_expr = self.__class__._checked_make(
                self._core_info, canonical_sub_expressions, 
                style_preferences=canonical_styles)
        """
        canonical_expr = self.__class__._checked_make(
            self._core_info, canonical_sub_expressions, 
            style_preferences=canonical_styles)
        assert canonical_expr._canonical_version() == canonical_expr, (
                "The canonical version of a canonical expression should "
                "be itself.")
        self._canonical_expr = canonical_expr
        return canonical_expr

    def _establish_and_get_meaning_id(self):
        '''
        The "meaning" of an expression is determined by it's
        canonical version and is only established as needed (on demand).
        Return the "meaning id" after it is established.
        '''
        if hasattr(self, '_meaning_id'):
            return self._meaning_id
        canonical_expr = self._canonical_version()
        if hasattr(self, '_meaning_id'):
            # It may have been set via the '_canonical_version' call.
            return self._meaning_id
        if canonical_expr is self:
            # The "true" meaning data is the "labeled" meaning data.
            self._meaning_data = self._labeled_meaning_data
        else:
            canonical_expr._establish_and_get_meaning_id()
            self._meaning_data = canonical_expr._meaning_data
        if not hasattr(self._meaning_data, 'canonical_expr'):
            # store the canonical expression for future reference
            self._meaning_data.canonical_expr = canonical_expr
        # Anything with the same "labeled meaning data" must have the
        # same "canonical meaning data".
        labeled_to_canonical_meaning_data = \
            Expression.labeled_to_canonical_meaning_data
        labeled_to_canonical_meaning_data[self._labeled_meaning_data] = \
            self._meaning_data
        self._meaning_id = self._meaning_data._unique_id
        return self._meaning_id

    def _generate_unique_rep(self, object_rep_fn, core_info=None, styles=None):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        if core_info is None:
            core_info = self._core_info
        if styles is None and hasattr(self, '_style_data'):
            styles = self._style_data.styles
        if styles is not None:
            style_str = ','.join(style_name + ':' + styles[style_name]
                                 for style_name in sorted(styles.keys()))
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
              canonical_version=None):
        '''
        Should make the Expression object for the specific Expression sub-class
        based upon the core_info and sub_expressions.  Must be implemented for
        each core Expression sub-class that can be instantiated.
        '''
        raise MakeNotImplemented(cls)

    @classmethod
    def _checked_make(cls, core_info, sub_expressions, *, style_preferences,
                      canonical_version=None):
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
        if canonical_version is None:
            made = cls._make(core_info, sub_expressions,
                             styles=style_preferences)
        else:
            made = cls._make(core_info, sub_expressions,
                             canonical_version=canonical_version, 
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

    def with_styles(self, **kwargs):
        '''
        Alter the styles of this expression, and anything containing this
        particular expression object, according to kwargs.
        '''
        styles = dict(self._style_data.styles)
        # update the _styles, _style_rep, and _style_id
        styles.update(kwargs)
        return self._with_these_styles(styles)
    
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
        styles = self.style_options().standardized_styles(
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
                styles=styles))
        new_style_expr._style_data.styles = dict(styles)
        new_style_expr._style_id = new_style_expr._style_data._unique_id
        return new_style_expr
    
    def with_matching_style(self, expr_with_different_style):
        '''
        Alter the styles of this expression to match that of the
        given "expr_with_different_style" which should be an
        Expression with the same meaning as 'self'.
        '''
        if self != expr_with_different_style:
            raise ValueError(
                "'with_matching_style' must an expression with "
                "the same meaning as self: %s ≠ %s."%
                (self, expr_with_different_style))
        return self._with_matching_style(expr_with_different_style)

    def _with_matching_style(self, expr_with_different_style):
        '''
        Helper function for 'with_matching_style'.
        '''
        if self._style_id == expr_with_different_style._style_id:
            return self # no difference in style actually; do nothing
        for my_sub_expr, other_sub_expr in zip(
                self.sub_expr_iter(), expr_with_different_style.sub_expr_iter()):
            my_sub_expr._with_matching_style(other_sub_expr)
        # Note, within lambda maps, "meanings" may diverge.
        # We only "guarantee" the new styles exist where "meanings"
        # are the same.
        ignore_inapplicable_styles = (self != expr_with_different_style)
        return self._with_these_styles(
                expr_with_different_style.get_styles(),
                ignore_inapplicable_styles = ignore_inapplicable_styles)
    
    def with_mimicked_style(self, other_expr):
        '''
        Given an 'other_expr' with the same style options as
        'self', return self with a style that mimicks that
        of 'other_expr' just at the top level.
        '''
        if (self.style_options().options != 
                other_expr.style_options().options):
            raise ValueError(
                "'other_expr' must an expression with "
                "the same style options as 'self'.")
        return self.with_styles(**other_expr.get_styles())

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

    def prove(self, assumptions=USE_DEFAULTS, automation=USE_DEFAULTS):
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
        from proveit import Judgment, ProofFailure
        from proveit.logic import Not
        assumptions = defaults.checked_assumptions(assumptions)
        assumptions_set = set(assumptions)
        if automation is USE_DEFAULTS:
            automation = defaults.automation

        found_truth = Judgment.find_judgment(self, assumptions_set)
        if found_truth is not None:
            found_truth.with_matching_styles(
                self, assumptions)  # give it the appropriate style
            return found_truth  # found an existing Judgment that does the job!

        if self in assumptions_set:
            # prove by assumption if self is in the list of assumptions.
            from proveit._core_.proof import Assumption
            return Assumption.make_assumption(self, assumptions).proven_truth

        if not automation:
            raise ProofFailure(self, assumptions, "No pre-existing proof")

        # Use Expression.in_progress_to_conclude set to prevent an infinite
        # recursion
        in_progress_key = (
            self, tuple(sorted(assumptions,
                               key=lambda expr: hash(expr))))
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
            if not concluded_truth.assumptions_set.issubset(assumptions_set):
                raise ValueError("While proving " +
                                 str(self) +
                                 ", 'conclude' method returned a Judgment with extra assumptions: " +
                                 str(set(concluded_truth.assumptions) -
                                     assumptions_set))
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
            self.prove(assumptions, automation=False)
            return True
        except ProofFailure:
            return False

    def disprove(self, assumptions=USE_DEFAULTS, automation=USE_DEFAULTS):
        '''
        Attempt to prove the logical negation (Not) of this expression.
        If successful, the Judgment is returned, otherwise an exception
        is raised.  By default, this simply calls prove on the negated
        expression. Override `conclude_negation` for automation specific to
        the type of expression being negated.
        '''
        from proveit.logic import Not
        return Not(self).prove(assumptions=assumptions, automation=automation)

    def disproven(self, assumptions=USE_DEFAULTS):
        '''
        Return True if and only if the expression is known to be false.
        '''
        from proveit import ProofFailure
        try:
            self.disprove(assumptions, automation=False)
            return True
        except ProofFailure:
            return False

    def conclude(self, assumptions=USE_DEFAULTS):
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

    def conclude_negation(self, assumptions=USE_DEFAULTS):
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

    """
    def is_simplified(self):
        directive_id = defaults.get_simplification_directives_id()
        return self in Expression.simplified_exprs.get(directive_id, tuple())
    """

    def replaced(self, repl_map, *, allow_relabeling=False, 
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

        Also applies any enabled automatic reductions.
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
        return expr.equality_replaced(
                new_equality_repl_requirements,
                auto_simplify_top_level=defaults.auto_simplify)
        requirements.extend(new_equality_repl_requirements)
        equality_repl_requirements.update(new_equality_repl_requirements)

    def basic_replaced(self, repl_map, *, 
                       allow_relabeling=False, requirements=None):
        '''
        Implementation for Expression.replaced except for equality
        replacements.
        '''
        if len(repl_map) > 0 and (self in repl_map):
            replaced = repl_map[self]
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
            replaced = self.__class__._checked_make(
                self._core_info, subbed_sub_exprs,
                style_preferences=self._style_data.styles)
        return replaced

    def equality_replaced(self, requirements,
                          auto_simplify_top_level=USE_DEFAULTS):
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
        from proveit import Judgment  
        from proveit.logic import Equals

        # Convert the replacements tuple to an equality_repl_map.
        equality_repl_map = dict()
        for replacement in defaults.replacements:
            if not isinstance(replacement, Judgment):
                raise TypeError("The 'reductions' must be Judgments")
            if not isinstance(replacement.expr, Equals):
                raise TypeError(
                        "The 'reductions' must be equality Judgments")
            if replacement.expr.lhs == replacement.expr.rhs:
                # Don't bother with reflexive (x=x) reductions.
                continue
            equality_repl_map[replacement.expr.lhs] = replacement

        # Use the recursive helper method.
        return self._equality_replaced(
                equality_repl_map, requirements,
                auto_simplify_top_level=auto_simplify_top_level)

    def _equality_replaced(self, equality_repl_map, requirements,
                           auto_simplify_top_level=USE_DEFAULTS):
        '''
        Recursive helper method for equality_replaced.
        '''
        from proveit import Judgment, Composite, ExprRange       
        from proveit._core_.proof import (
                ProofFailure, UnsatisfiedPrerequisites)
        from proveit.logic import (Equals, SimplificationError,
                                   EvaluationError,
                                   is_irreducible_value)

        # Check for an equality replacement via equality_repl_map
        # or as a simplification.  Note that 'replacements' override
        # 'preserved_exprs'.
        replacement = None
        if (not isinstance(self, Composite) and 
                not isinstance(self, ExprRange)):
            if self in equality_repl_map:
                replacement = equality_repl_map[self]
        if replacement is None:
            if self in defaults.preserved_exprs:
                # This expression should be preserved, so don't make
                # any equality-based replacement.
                return self
        expr = self
        if replacement is None:
            # Recurse into the sub-expressions.
            expr = self._equality_replaced_sub_exprs(
                    equality_repl_map, requirements)
            if expr in defaults.preserved_exprs:
                # The expression should be preserved, so don't make
                # any further equality-based replacement.
                return expr
            if auto_simplify_top_level is USE_DEFAULTS:
                auto_simplify_top_level = defaults.auto_simplify
            if (expr != self) and (expr in equality_repl_map):
                replacement = equality_repl_map[expr]
            elif (auto_simplify_top_level and not is_irreducible_value(expr)
                  and not isinstance(expr, ExprRange)):
                # Look for a known evaluation.
                replacement = Equals.get_known_evaluation(expr)
                if (replacement is None and 
                        hasattr(expr, 'shallow_evaluation')):
                    # Attempt a shallow evaluation (after recursion).
                    try:
                        replacement = expr.shallow_evaluation()
                    except (EvaluationError, UnsatisfiedPrerequisites, 
                            NotImplementedError, ProofFailure):
                        # Failure in the simplification attempt; 
                        # just skip it.
                        pass
                if (replacement is None and 
                        hasattr(expr, 'shallow_simplification')):
                    # Attempt a shallow simplification (after recursion).
                    try:
                        replacement = expr.shallow_simplification()
                        if replacement.rhs == expr:
                            # Trivial simplification -- don't use it.
                            return expr
                    except (SimplificationError, UnsatisfiedPrerequisites, 
                            NotImplementedError, ProofFailure):
                        # Failure in the simplification attempt; 
                        # just skip it.
                        pass
            if replacement is None:
                return expr
        
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
        if not replacement.is_applicable():
            # The assumptions aren't adequate to use this reduction.
            return self
        requirements.append(replacement)
        return replacement.expr.rhs

    def _equality_replaced_sub_exprs(self, equality_repl_map, requirements):
        '''
        Recursive helper method for equality_replaced.
        '''
        # Recurse into the sub-expressions.
        sub_exprs = self._sub_expressions
        subbed_sub_exprs = \
            tuple(sub_expr._equality_replaced(
                    equality_repl_map, requirements)
                  for sub_expr in sub_exprs)
        if all(subbed_sub._style_id == sub._style_id for
               subbed_sub, sub in zip(subbed_sub_exprs, sub_exprs)):
            # Nothing change, so don't remake anything.
            return self
        return self.__class__._checked_make(
            self._core_info, subbed_sub_exprs,
            style_preferences=self._style_data.styles)
            
    def copy(self):
        '''
        Make a copy of the Expression with the same styles.
        '''
        # vacuous substitution makes a copy
        expr_copy = self.basic_replaced({})
        return expr_copy

    def _used_vars(self):
        '''
        Return all of the used Variables of this Expression,
        included those in sub-expressions.
        Call externally via the used_vars method in expr.py.
        '''
        return set().union(*[expr._used_vars() for
                             expr in self._sub_expressions])

    def _possibly_free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free or
        not explicitly and completely masked.  Examples of "forms":
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
        entry because the masking is not "explicit" (obvious).

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
                    expr._possibly_free_var_ranges(
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

        The default Expression.evaluation only checks to see if the
        expression has been proven or disproven (and therefore equal
        to TRUE or FALSE respectively) or known to be equal to another
        expression that has been evaluated.  This method may be
        overridden for particular Expression types.
        
        See also Operation.evaluation and Expression.shallow_evaluation.
        '''
        from proveit.logic import (Equals, evaluate_truth,  
                                   evaluate_falsehood, EvaluationError)

        # If self is proven or disproven, we can equate it to
        # TRUE or FALSE respectively.
        if self.proven():
            return evaluate_truth(self)
        elif self.disproven():
            return evaluate_falsehood(self)

        # See if there is a known equal expression that has an
        # evaluation.
        for eq_expr in Equals.yield_known_equal_expressions(self):
            known_evaluation = Equals.get_known_evaluation(self)
            if known_evaluation is not None:
                # Found a known evaluation of an expression equal to 
                # self, so self is equal to the evaluation via
                # transitivity.
                return Equals(self, known_evaluation.rhs).prove()
        
        # No other default options (though the Operation class
        # has some options via simplifying operands).
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
        # The only default simplification is an evaluations (though the
        # Operation class has some options via simplifying operands).
        from proveit.logic import EvaluationError
        try:
            return self.evaluation()
        except EvaluationError:
            return self.shallow_simplification()


    @equality_prover('shallow_evaluated', 'shallow_evaluate')
    def shallow_evaluation(self, **defaults_config):
        '''
        Attempt to evaluate 'self' under the assumption that it's
        operands (sub-expressions) have already been simplified.
        Return the evaluation as a Judgment equality with 'self' on 
        the left side and an irreducible value on the right side.
        
        Must be overridden for class-specific evaluation.
        Raise a SimplificationError if the evaluation
        cannot be done.
        '''
        raise NotImplementedError(
            "'shallow_evaluation' not implemented for %s class" % str(
                self.__class__))

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, **defaults_config):
        '''
        Attempt to simplify 'self' under the assumption that it's
        operands (sub-expressions) have already been simplified.
        Returns the simplification as a Judgment equality with 'self'
        on the left side.
        
        The default is to return the trivial reflexive equality.
        Must be overridden for class-specific simplification.
        '''
        from proveit.logic import Equals
        return Equals(self, self).conclude_via_reflexivity()

    @classmethod
    def temporary_simplification_directives(cls):
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
        '''
        if not hasattr(cls, '_simplification_directives_'):
            raise AttributeError("%s has no _simplification_directives_ "
                                 "attribute")
        simplification_directives = cls._simplification_directives_
        if not isinstance(simplification_directives, SimplificationDirectives):
            raise TypeError(
                    "The '_simplification_directives_' of an Expression "
                    "class should be of type SimplificationDirectives")
        return simplification_directives.temporary()

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


def used_vars(expr):
    '''
    Return all of the used Variables of this Expression,
    included those in sub-expressions.
    '''
    return expr._used_vars()


def possibly_free_var_ranges(expr, exclusions=None):
    '''
    Return the dictionary mapping Variables to forms w.r.t. ranges
    of indices (or solo) in which the variable occurs as free or
    not explicitly and completely masked.  Examples of "forms":
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
    return expr._guaranteed_free_var_ranges(exclusions=exclusions)


def free_vars(expr, *, err_inclusively):
    '''
    Returns the set of variables that are free, the variable itself
    or some indices of the variable.
    For example,
        (x_1, ..., x_n) -> x_1 + ... + x_n + x_{n+1}
    x and n are both free.  And in
        (x_1, ..., x_n) -> x_1 + ... + x_k + x_{k+1} + ... + x_{n}
    n, and k are free assuming 1 <= k <= n.
    What actually gets reported depends upon the "err_inclusively"
    flag.  If "err_inclusively" is True, the latter example
    will report x, n, and k because it is not clear that
    x is completely bound without assumptions on k.  If
    "err_inclusively" is False, the first example will just report
    n because it requires some extra work to determine that x
    is not comletely bound.
    '''
    if err_inclusively:
        return {var for var in expr._possibly_free_var_ranges().keys()}
    else:
        return _entirely_unbound_vars(expr)


def _entirely_unbound_vars(expr):
    '''
    Returns the set of variables for that are entirely unbound in
    the given expression.
    For example, given
        (x_1, ..., x_n) -> x_1 + ... + x_n + x_{n+1}
    n is entirely unbound.  Even though there is an index for which
    x is unbound, it is partially bound and therefore not returned.
    Axioms and theorems must not have any variables that are
    entirely unbound.  They should not have any partially unbound
    variables either, but Prove-It does not check for this since
    the check would be more involved and it isn't so critical.
    '''
    from proveit._core_.expression.label.var import Variable
    from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
    if isinstance(expr, Variable):
        return {expr}
    ubound_vars = set()
    for sub_expr in expr._sub_expressions:
        ubound_vars.update(_entirely_unbound_vars(sub_expr))
    if isinstance(expr, Lambda):
        return ubound_vars.difference(expr.parameter_vars)
    return ubound_vars


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


class _NoExpandedIteration(Exception):
    '''
    Used internally for _expandingIterRanges.
    '''

    def __init__(self):
        pass

"""
This is the expression module.
"""

from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.context import Context
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_._unique_data import meaningData, styleData
import sys
import re
import os
import urllib.request, urllib.parse, urllib.error
from base64 import encodebytes

class ExprType(type):
    '''
    By overriding the Expression type, we can make Operation-type
    expressions automatically populate the Operation.operationClassOfOperator
    when any Expression class is provided with an '_operator_' class attribute.
    '''
    
    # These attributes should not be overridden by classes outside
    # of the core.
    protected = ('_generic_version', '_setContext', 
                 'substituted', 'relabeled',
                 '_make', '_check_make', '_used_vars',
                 '_free_vars', '_free_var_const_index_shifts',
                 '_check_param_occurrences',
                 '_repr_html_', '_coreInfo',
                 '_subExpressions', '_genericExpr', 
                 '_meaningData', '_meaning_id',
                 '_styleData', '_style_id')
    
    def __new__(meta, name, bases, attrs):
        # Tip from
        # https://stackoverflow.com/questions/3948873
        #             /prevent-function-overriding-in-python
        core_package = 'proveit._core_'
        if attrs['__module__'][:len(core_package)] != core_package:
            for attribute in attrs:
                if attribute in ExprType.protected:
                    raise AttributeError('Overriding of attribute "%s" '
                                         'not allowed.'%attribute)
        return super().__new__(meta, name, bases, attrs)
    
    def __init__(cls, *args, **kwargs):
        type.__init__(cls, *args, **kwargs)
        if hasattr(cls, '_operator_'):
            from proveit._core_.expression.operation import Operation
            if issubclass(cls, Operation):
                Operation.operationClassOfOperator[cls._operator_] = cls

class Expression(metaclass=ExprType):
    # set of (style-id, Expression) tuples
    displayed_expression_styles = set() 
    
    # map expression style ids to contexts (for expressions that "belong" to a Context)
    contexts = dict() 
    
    # (expression, assumption) pairs for which conclude is in progress, tracked to prevent infinite
    # recursion in the `prove` method.
    in_progress_to_conclude = set()

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        Expression.displayed_expression_styles.clear()
        Expression.contexts.clear()
        assert len(Expression.in_progress_to_conclude)==0, "Unexpected remnant 'in_progress_to_conclude' items (should have been temporary)"
                        
    def __init__(self, coreInfo, subExpressions=tuple(), styles=None):
        '''
        Initialize an expression with the given coreInfo (information relevant 
        at the core Expression-type level) which should be a list (or tuple) of
        strings, and a list (or tuple) of subExpressions.  "styles" is a 
        dictionary used to indicate how the Expression should be formatted
        when there are different possibilities (e.g. division with '/' or as a 
        fraction).  The meaning of the expression is independent of its styles 
        signature.
        '''
        if styles is None: styles = dict()
        for coreInfoElem in coreInfo:
            if not isinstance(coreInfoElem, str):
                raise TypeError('Expecting coreInfo elements to be of string type')
        for subExpression in subExpressions:
            if not isinstance(subExpression, Expression):
                raise TypeError('Expecting subExpression elements to be of Expression type')
                
        # note: these contained expressions are subject to style changes on an Expression instance basis
        self._subExpressions = tuple(subExpressions)
        
        # check for illegal characters in core-info or styles
        if any(',' in info for info in coreInfo):
            raise ValueError("coreInfo is not allowed to contain a comma.")
        if styles is not None:
            for style in styles.values():
               if not {',', ':', ';'}.isdisjoint(style):
                   raise ValueError("Styles are not allowed to contain a ',', ':', or ';'.  Just use spaces.") 
        
        # Set and initialize the "meaning data".
        # The meaning data is shared among Expressions with the same 
        # structure disregarding style or chosen lambda paramterization.
        if hasattr(self, '_genericExpr') and self._genericExpr is not self:
            # The _genericExpr attribute was already set
            # -- must be a Lambda Expression.
            self._meaningData = self._genericExpr._meaningData
        else:
            object_rep_fn = lambda expr : hex(expr._meaning_id)
            self._meaningData = meaningData(self._generate_unique_rep(object_rep_fn, 
                                                                      coreInfo))
            if not hasattr(self._meaningData, '_coreInfo'):
                # initialize the data of self._meaningData
                self._meaningData._coreInfo = tuple(coreInfo)
        '''
        if not hasattr(self, '_genericExpr'):
            self._genericExpr = self._generic_version()
        if self._genericExpr is self:
            # Create the meaning data.
            object_rep_fn = lambda expr : hex(expr._meaning_id)
            self._meaningData = meaningData(self._generate_unique_rep(object_rep_fn, 
                                                                      coreInfo))
            if not hasattr(self._meaningData, '_coreInfo'):
                # initialize the data of self._meaningData
                self._meaningData._coreInfo = tuple(coreInfo)            
        else:
            self._meaningData = self._genericExpr._meaningData
        '''
        
        # The style data is shared among Expressions with the same structure and style -- this will contain the 'png' generated on demand.
        self._styleData = styleData(self._generate_unique_rep(lambda expr : hex(expr._style_id), coreInfo, styles))
        # initialize the style options
        self._styleData.styles = dict(styles) # formatting style options that don't affect the meaning of the expression

        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaningData._unique_id
        self._coreInfo = self._meaningData._coreInfo
        
        self._style_id = self._styleData._unique_id
        
        """
        self._styles = dict(styles) # formatting style options that don't affect the meaning of the expression
        # meaning representations and unique ids are independent of style
        self._meaning_rep = 
        self._meaning_id = makeUniqueId(self._meaning_rep)
        # style representations and style ids are dependent of style
        self._style_rep = self._generate_unique_rep(lambda expr : hex(expr._style_id), includeStyle=True)
        self._style_id = makeUniqueId(self._style_rep)
        """
        for subExpression in subExpressions: # update Expression.parent_expr_map
            self._styleData.addChild(self, subExpression)
        
        if not hasattr(self, '_max_in_scope_bound_vars'):
            # The '_max_inscope_bound_vars' attribute is used to make 
            # unique variable assignments for Lambda parameters in the
            # "generic version" which is invarian under 
            # alpha-conversion.  For a Lambda, this attribute is
            # set ahead of time.
            if len(self._subExpressions)==0:
                self._max_in_scope_bound_vars = 0
            else:
                self._max_in_scope_bound_vars = \
                    max(subexpr._max_in_scope_bound_vars for subexpr 
                        in self._subExpressions)
            
    
    def _generic_version(self):
        '''
        Retrieve (and create if necessary) the generic version of this 
        expression in which deterministic 'dummy' variables are used as 
        Lambda parameters, determines the 'meaning' of the expression.
        '''
        if hasattr(self, '_genericExpr'):
            return self._genericExpr
        # Get the generic versions of the sub-expressions.
        generic_sub_expressions = tuple(sub_expr._generic_version() 
                                        for sub_expr in self._subExpressions)
        # Get the styles of the sub expressions.
        sub_expression_styles = tuple(sub_expr._styleData 
                                      for sub_expr in self._subExpressions)
        # Get the styles of the generic versions of the sub-expressions.
        generic_sub_expression_styles = \
            tuple(generic_sub_expr._styleData 
                  for generic_sub_expr in generic_sub_expressions)
        
        if sub_expression_styles == generic_sub_expression_styles:
            # This is the generic version.
            self._genericExpr = self
            return self
        
        # The 'generic' sub-expressions are different than the sub-expressions,
        # so that propagates to this Expression's generic version.
        self._genericExpr = self.__class__._checked_make(
                self._meaningData._coreInfo, dict(self._styleData.styles), 
                generic_sub_expressions)
        return self._genericExpr
        
    
    def _setContext(self, context):
        '''
        Assign a Context to this expression.
        '''
        self.context = context
        Expression.contexts[self._style_id] = context
        """
        # Commenting this out because this make a strange first-come, first-serve
        # context assignment that might keep changing expression representations around;
        # that can be a nuisance for version controlling the Prove-It notebooks.
        for sub_expr in self._subExpressions:
            if sub_expr._style_id not in Expression.contexts:
                sub_expr._setContext(context)
        """
    
    def _generate_unique_rep(self, objectRepFn, coreInfo=None, styles=None):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        from proveit._core_.expression.lambda_expr import Lambda
        if coreInfo is None: coreInfo = self._coreInfo
        if styles is None and hasattr(self, '_styleData'):
            styles = self._styleData.styles
        if styles is not None:
            style_str = ','.join(style_name + ':' + styles[style_name]
                                 for style_name in sorted(styles.keys()))
        else: style_str = ''
        sub_expr_info = ','.join(objectRepFn(expr) for expr in self._subExpressions)
        # All Lambda expressions are embued with a "generic version" (which may
        # be itself) which we will store with the unique representation info.
        if isinstance(self, Lambda):
            if self._genericExpr is self:
                generic_ref = '.' # Denote that it is "generic" itself.
            else:
                generic_ref = objectRepFn(self._genericExpr)
        else:
            # Only retain the reference to the generic version for Lambda
            # expressions.  Other expressions may set a _genericExpr for
            # convenience during runtime, but since these are generated on an
            # as-needed basis, it shouldn't be included as part of the
            # unique representation and there is no good reason to store it.
            generic_ref = ''
        # Note: putting the sub-expressions at the front makes it convenient
        # to just grab that piece which is used when adding or removing
        # references to stored information.
        return '%s;%s;%s;%s;%s'%(generic_ref, sub_expr_info, self._class_path(), 
                                 ','.join(coreInfo), style_str)
    #self._class_path() + '[' + ','.join(coreInfo) + ']' + style_str + ';[' +  + ']'
    
    def _class_path(self):
        ExprClass = self.__class__
        class_module = sys.modules[ExprClass.__module__]
        if hasattr(class_module, '__file__'):
            context = Context(class_module.__file__)
        else:
            context = Context() # use the current directory if using the main module
        # get the full class path relative to the root context where the class is defined
        class_path = context.name + '.' + ExprClass.__module__.split('.')[-1] + '.' + ExprClass.__name__
        return class_path

    @staticmethod
    def _parse_unique_rep(unique_rep):
        generic_ref, sub_expr_info, expr_class_str, core_info_str, style_str = \
            unique_rep.split(';')
        core_info = [_ for _ in core_info_str.split(',') if _ != '']
        style_pairs = [_ for _ in style_str.split(',') if _ != '']
        style_dict = dict(style_pair.split(':') for style_pair in style_pairs)
        sub_expr_refs = [_ for _ in sub_expr_info.split(',') if _ != '']
        return expr_class_str, core_info, style_dict, sub_expr_refs, generic_ref
        
    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        # The generic reference and sub expressions come respectfully at the 
        # beginning of unique_rep.
        generic_ref_end = unique_rep.find(';')
        sub_expr_end = unique_rep.find(';', generic_ref_end+1)
        ref_info = unique_rep[:sub_expr_end]
        # Split by ',' or ';' to get the individual reference ids.
        return [_ for _ in re.split(',|;', ref_info) if _ not in ('', '.')]
    
    def __setattr__(self, attr, value):
        '''
        Expressions should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).
        '''
        if attr[0] != '_' and attr in self.__dict__:
            raise Exception("Attempting to alter read-only value '%s'"%attr)
        self.__dict__[attr] = value
    
    def __repr__(self):
        return str(self) # just use the string representation
    
    def __eq__(self, other):
        if isinstance(other, Expression):
            return self._meaning_id == other._meaning_id 
        else: return False # other must be an Expression to be equal to self
    
    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._meaning_id 
    
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
        raise NotImplementedError("'string' method not implemented for " + str(self.__class__))

    def latex(self, **kwargs):
        '''
        Return a latex-formatted representation of the Expression.  The kwargs can contain formatting
        directives (such as 'fence' used to indicate when a sub-expression should be wrapped in
        parentheses if there can be ambiguity in the order of operations).
        '''
        raise NotImplementedError("'latex' method not implemented for " + str(self.__class__))
    
    def formatted(self, formatType, **kwargs):
        '''
        Returns a formatted version of the expression for the given formatType
        ('string' or 'latex').  In the keyword arguments, fence=True indicates
        that parenthesis around the sub-expression may be necessary to avoid 
        ambiguity.
        '''
        if formatType == 'string': return self.string(**kwargs)
        if formatType == 'latex': return self.latex(**kwargs)
    
    @classmethod
    def _make(cls, coreInfo, styles, subExpressions, genericExpr=None):
        '''
        Should make the Expression object for the specific Expression sub-class
        based upon the coreInfo and subExpressions.  Must be implemented for 
        each core Expression sub-class that can be instantiated.
        '''
        raise MakeNotImplemented(cls)

    @classmethod
    def _checked_make(cls, coreInfo, styles, subExpressions, genericExpr=None):
        '''
        Check that '_make' is done appropriately since it is not 
        entirely within the control of the core.
        '''
        coreInfo = tuple(coreInfo)
        subExpressions = tuple(subExpressions)
        if genericExpr is not None:
            made = cls._make(coreInfo, styles, subExpressions, genericExpr)
        else:
            made = cls._make(coreInfo, styles, subExpressions)
        assert made._coreInfo == coreInfo, (
                "%s vs %s"%(made._coreInfo, coreInfo))
        assert made._subExpressions == subExpressions, (
                "%s vs %s"%(made._subExpressions, subExpressions))
        return made
    
    def coreInfo(self):
        '''
        Copy out the core information.
        '''
        return tuple(self._coreInfo)
    
    def subExpr(self, idx):
        return self._subExpressions[idx]
        
    def subExprIter(self):
        '''
        Iterator over the sub-expressions of this expression.
        '''
        return iter(self._subExpressions)
        
    def numSubExpr(self):
        '''
        Return the number of sub-expressions of this expression.
        '''
        return len(self._subExpressions)
    
    def innerExpr(self):
        '''
        Return an InnerExpr object to wrap the expression and
        access any inner sub-expression for the purpose of replacing
        the inner expression, or change its styles, or relabeling its
        variables.
        '''
        from .inner_expr import InnerExpr
        return InnerExpr(self)
        
    def styleOptions(self):
        '''
        Return a StyleOptions object that indicates the possible
        styles and values that is available to determine how
        this Expression may be presented.
        '''
        return StyleOptions(self) # the default is empty
    
    def withStyles(self, **kwargs):
        '''
        Alter the styles of this expression, and anything containing this
        particular expression object, according to kwargs.
        '''
        styles = dict(self._styleData.styles)
        # update the _styles, _style_rep, and _style_id
        styles.update(kwargs)
        if styles == self._styleData.styles:
            return self # no change in styles, so just use the original
        self._styleData.updateStyles(self, styles)
        return self
    
    def withMatchingStyle(self, expr_with_different_style):
        '''
        Alter the styles of this expression to match that of the
        given "expr_with_different_style".
        '''
        if self != expr_with_different_style:
            raise ValueError("'withMatchingStyle' must be given an expression with the same meaning")
        return self._withMatchingStyle(expr_with_different_style)
    
    def _withMatchingStyle(self, expr_with_different_style):
        '''
        Helper function for 'withMatchingStyle.
        '''
        if self._style_id == expr_with_different_style._style_id:
            return # no difference in style actually; do nothing
        for my_sub_expr, other_sub_expr in zip(self.subExprIter(), expr_with_different_style.subExprIter()):
            my_sub_expr._withMatchingStyle(other_sub_expr)
        self.withStyles(**expr_with_different_style.getStyles())
        return self
    
    def styleNames(self):
        '''
        Return the name of the styles that may be set.
        '''
        return list(self._styleData.styles.keys())
    
    def getStyle(self, styleName, default=None):
        '''
        Return the current style setting for the given style name.
        '''
        if default is None:
            return self._styleData.styles[styleName]
        else:
            return self._styleData.styles.get(styleName, default)
    
    def getStyles(self):
        '''
        Return a copy of the internally maintained styles dictionary.
        '''
        return dict(self._styleData.styles)
         
    def remakeConstructor(self):
        '''
        Method to call to reconstruct this Expression.  The default is the class name
        itself to use the __init__ method, but sometimes a different method is more
        appropriate for setting the proper style (e.g. the Frac method in 
        proveit.number.division.divide which constructs a Div object with a different
        style).  This constructor method must be in the same module as the class.
        '''
        return self.__class__.__name__
    
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Expression.
        '''
        raise NotImplementedError("remakeArguments method should be implemented for all ProveIt core Expression sub-classes.")
            
    def remakeWithStyleCalls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a 
        tuple of strings with the calls to make.  For example,
        ["withWrappingAt(3)", "withJustification('right')"].
        '''
        return tuple()
    
    def prove(self, assumptions=USE_DEFAULTS, automation=USE_DEFAULTS):
        '''
        Attempt to prove this expression automatically under the
        given assumptions (if None, uses defaults.assumptions).  First
        it tries to find an existing KnownTruth, then it tries a simple
        proof by assumption (if self is contained in the assumptions),
        then it attempts to call the 'conclude' method.  If successful,
        the KnownTruth is returned, otherwise an exception is raised.
        Cyclic attempts to `conclude` the same expression under the
        same set of assumptions will be blocked, so `conclude` methods are
        free make attempts that may be cyclic.
        '''
        from proveit import KnownTruth, ProofFailure
        from proveit.logic import Not
        assumptions = defaults.checkedAssumptions(assumptions)
        assumptionsSet = set(assumptions)
        if automation is USE_DEFAULTS:
            automation = defaults.automation
                
        foundTruth = KnownTruth.findKnownTruth(self, assumptionsSet)
        if foundTruth is not None: 
            foundTruth.withMatchingStyles(self, assumptions) # give it the appropriate style
            return foundTruth # found an existing KnownTruth that does the job!
                
        if self in assumptionsSet:
            # prove by assumption if self is in the list of assumptions.
            from proveit._core_.proof import Assumption
            return Assumption.makeAssumption(self, assumptions).provenTruth
        
        if not automation:
            raise ProofFailure(self, assumptions, "No pre-existing proof")
                                                
        # Use Expression.in_progress_to_conclude set to prevent an infinite recursion
        in_progress_key = (self, tuple(sorted(assumptions, key=lambda expr:hash(expr))))
        if in_progress_key in Expression.in_progress_to_conclude:
            raise ProofFailure(self, assumptions, "Infinite 'conclude' recursion blocked.")
        Expression.in_progress_to_conclude.add(in_progress_key)        
        
        try:
            concludedTruth = None
            if isinstance(self, Not):
                # if it is a Not expression, try concludeNegation on the operand
                try:
                    concludedTruth = self.operands[0].concludeNegation(assumptions=assumptions)
                except NotImplementedError:
                    pass # that didn't work, try conclude on the Not expression itself
            if concludedTruth is None:
                try:
                    # first attempt to prove via implication
                    concludedTruth = self.concludeViaImplication(assumptions)
                except ProofFailure:
                    # try the 'conclude' method of the specific Expression class
                    concludedTruth = self.conclude(assumptions)
            if concludedTruth is None:
                raise ProofFailure(self, assumptions, "Failure to automatically 'conclude'")
            if not isinstance(concludedTruth, KnownTruth):
                raise ValueError("'conclude' method should return a KnownTruth (or raise an exception)")
            if concludedTruth.expr != self:
                raise ValueError("'conclude' method should return a KnownTruth for this Expression object: " + str(concludedTruth.expr) + " does not match " + str(self))
            if not concludedTruth.assumptionsSet.issubset(assumptionsSet):
                raise ValueError("While proving " + str(self) + ", 'conclude' method returned a KnownTruth with extra assumptions: " + str(set(concludedTruth.assumptions) - assumptionsSet))
            if concludedTruth.expr._style_id == self._style_id:
                return concludedTruth # concludedTruth with the same style as self.
            return concludedTruth.withMatchingStyles(self, assumptions) # give it the appropriate style
        except NotImplementedError:
            raise ProofFailure(self, assumptions, "'conclude' method not implemented for proof automation")
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
        If successful, the KnownTruth is returned, otherwise an exception
        is raised.  By default, this simply calls prove on the negated
        expression. Override `concludeNegation` for automation specific to
        the type of expression being negated.      
        '''
        from proveit.logic import Not
        return Not(self).prove(assumptions=assumptions, automation=automation)
                        
    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude this expression under the given assumptions, 
        using automation specific to this type of expression.
        Return the KnownTruth if successful, or raise an exception.
        This is called by the `prove` method when no existing proof was found 
        and it cannot be proven trivially via assumption or defaultConclude.
        The `prove` method has a mechanism to prevent infinite recursion, 
        so there are no worries regarding cyclic attempts to conclude an expression.
        '''
        raise NotImplementedError("'conclude' not implemented for " + str(self.__class__))

    def concludeViaImplication(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude this expression via applying
        modus ponens of known implications.
        '''
        from proveit.logic import concludeViaImplication
        return concludeViaImplication(self, assumptions)
        
    def concludeNegation(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude the negation of this expression under the given
        assumptions, using automation specific to the type of expression being negated.
        Return the KnownTruth if successful, or raise an exception.
        This is called by the `prove` method of the negated expression
        when no existing proof for the negation was found.
        The `prove` method has a mechanism to prevent infinite recursion, 
        so there are no worries regarding cyclic attempts to conclude an expression.
        '''
        raise NotImplementedError("'concludeNegation' not implemented for " + str(self.__class__))
        
    def sideEffects(self, knownTruth):
        '''
        Yield methods to attempt as side-effects when this expression
        is proven as a known truth.  These should each accept an
        'assumptions' parameter.
        These should be obvious and useful consequences, trivial and limited.
        There is no need to call this manually; it is called automatically when
        the corresponding KnownTruth is created.
        It also may be desirable to store the knownTruth for future automation.
        '''
        return iter(())
    
    def substituted(self, repl_map, allow_relabeling=False,
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary 
        which maps Expressions to Expressions.  When used for 
        instantiation, this should specifically map variables,
        indexed variables, or ranges of indexed variables to
        Expressions.
        
        If allow_relabeling is True then internal Lambda parameters
        may be replaced when it is a valid replacement of parameter(s) 
        (i.e., Variable's, IndexedVar's, or an ExprRange of 
        IndexedVar's, and unique parameter variables).
        Otherwise, the Lambda parameter variables will be masked
        within its scope.  Partial masked of a range of indexed
        varaibles is not allowed and will cause an error.
        For example, we cannot replace (x_1, ..., x_{n+1}) within 
        (x_1, ..., x_n) -> f(x_1, ..., x_n).
        
        'assumptions' and 'requirements' are used when an operator is
        substituted by a Lambda map that has a range of parameters 
        (e.g., x_1, ..., x_n) such that the length of the parameters 
        and operands must be proven to be equal.  For more details, 
        see Operation.substituted, Lambda.apply, and Iter.substituted 
        (which is the sequence of calls involved).
        '''
        if len(repl_map)>0 and (self in repl_map):
            substituted = repl_map[self]
        else:
            subbed_sub_exprs = \
                tuple(sub_expr.substituted(repl_map, allow_relabeling,
                                           assumptions, requirements)
                      for sub_expr in self._subExpressions)
            substituted = self.__class__._checked_make(
                    self._coreInfo, dict(self._styleData.styles),
                    subbed_sub_exprs)
        return substituted
    
    def relabeled(self, relabel_map):
        '''
        Return a new expression in which all instances of the
        variables as keys in the 'relabel_map' dictionary are replaced 
        by the corresponding values.  The replacements must be
        Variable objects, or a TypeError will be raised.
        '''
        from proveit import Variable, IndexedVar
        for key, val in relabel_map.items():
            if (not isinstance(val, Variable) 
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel %s"%val)
            if (not isinstance(val, Variable) 
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel to %s"%key)
        return self.substituted(relabel_map, allow_relabeling=True)
    
    
    def copy(self):
        '''
        Make a copy of the Expression with the same styles.
        '''
        # vacuous substitution makes a copy
        expr_copy = self.substituted(expr_repl_map=dict()) 
        return expr_copy
    
    def _used_vars(self):
        '''
        Return all of the used Variables of this Expression,
        included those in sub-expressions.
        Call externally via the used_vars method in expr.py.
        '''
        return set().union(*[expr._used_vars() for 
                             expr in self._subExpressions])
        
    def _free_vars(self, exclusions=frozenset()):
        '''
        Return all of the free Variables of this Expression,
        included those in sub-expressions but excluding those with 
        internal bindings within Lambda expressions.  If this Expression
        is in the exclusions set, skip over it.
        Call externally via the free_vars method in expr.py.
        '''
        if self in exclusions: 
            return set() # this is excluded
        return set().union(*[expr._free_vars(exclusions=exclusions) 
                             for expr in self._subExpressions])

    def _free_var_indices(self):
        '''
        Returns a dictionary that maps indexed variables to
        a tuple with (start_base, start_shifts, end_base, end_shifts)
        indicating the indices for which an indexed variable is free.
        The start_shifts and end_shifts are constant integers.
        The included indices are each start_base + start_shift,
        each end_base + end_shift plus the range going from
        start_base + max(start_shifts) .. end_base + min(end_shifts).
        '''
        results = dict()
        for expr in self._subExpressions:
            sub_expr_results = expr._free_var_indices()
            print('expr', expr, 'sub_expr_results', sub_expr_results)
            for var, (start_base, start_shifts, end_base, end_shifts) \
                    in sub_expr_results.items():
                if var in results:
                    (prev_start_base, prev_start_shifts, 
                     prev_end_base, prev_end_shifts) = results[var]
                    new_start_base, new_start_shifts = None, set()
                    new_end_base, new_end_shifts = None, set()
                    if start_base == prev_start_base:
                        # Matching start bases; union the shifts.
                        new_start_base = start_base
                        new_start_shifts = \
                            prev_start_shifts.union(start_shifts)
                    if end_base == prev_end_base:
                        # Matching end bases; union the shifts
                        new_end_base = end_base
                        new_end_shifts = \
                            prev_end_shifts.union(end_shifts)                    
                    if new_start_base is None and new_end_base is None:
                        raise DisallowedIndexing(
                                var, 'join', prev_start_base, prev_end_base, 
                                start_base, end_base)
                    elif new_start_base is None or new_end_base is None:
                        # Only one side matches (start or end).
                        # This is only allowed if one of them has a
                        # start and end with the same base.
                        if start_base == end_base:
                            # The new range is the one with the same
                            # base, so the previous one determines the 
                            # unknown endpoint.
                            if new_start_base is None: 
                                new_start_base = prev_start_base
                                new_start_shifts = prev_start_shifts
                            if new_end_base is None: 
                                new_end_base = prev_end_base
                                new_end_shifts = prev_end_shifts
                        elif prev_start_base == prev_end_base:
                            # The previous range is the one with the 
                            # same base, so the previous one determines 
                            # the unknown endpoint.
                            if new_start_base is None: 
                                new_start_base = start_base
                                new_start_shifts = start_shifts
                            if new_end_base is None: 
                                new_end_base = end_base
                                new_end_shifts = end_shifts
                        else:
                            raise DisallowedIndexing(
                                    var, 'join', prev_start_base, 
                                    prev_end_base, start_base, end_base)
                    if new_start_base != new_end_base:
                        # Remove unnecessary shifts that are covered
                        # in new_start_base + max(new_start_shifts) .. 
                        #    new_end_base + min(new_end_shifts)
                        # (assuming none of the starts come after the
                        # ends which is reasonable to assume for these
                        # purposes; if not, the error will come when
                        # trying to do an instantiation).
                        while max(new_start_shifts)-1 in new_start_shifts:
                            new_start_shifts.remove(max(new_start_shifts))
                        while min(new_end_shifts)+1 in new_end_shifts:
                            new_end_shifts.remove(max(new_end_shifts))
                    results[var] = (new_start_base, new_start_shifts, 
                                    new_end_base, new_end_shifts)
                else:
                    results[var] = (start_base, start_shifts, 
                                    end_base, end_shifts)
        print('new Expression results', results)
        return results
    
    def _free_indexed_vars(self, range_param):
        '''
        Return all of the free IndexedVars of this Expression with an
        index that is the range_param with a possible constant shift.
        '''
        return set().union(*[expr._free_indexed_vars(range_param) 
                             for expr in self._subExpressions])

    def _var_index_shifts_in_ranges(self, var, shifts):
        '''
        Given a 'var' (e.g., 'x'), pass back, via the set 'shifts', 
        all of the constant index shifts to the ExprRange parameter
        that occur within ExprRanges (e.g., 'x_{1+1}, ..., x_{n+1}' 
        would have presumably have a shift of 1).
        '''
        for sub_expr in self._subExpressions:
            sub_expr._var_index_shifts_in_ranges(var, shifts)

    def _indexed_var_shifts(self, var, range_param, shifts):
        '''
        Given a 'var' (e.g., 'x') and 'range_param' (e.g., 'k'), pass 
        back, via the set 'shifts', all of the constant integer shifts
        to the 'range_param' of the index on the 'var' (e.g., 
        'x_{k+1}' would have a shift of 1).  This is a helper method
        for Expression._var_index_shifts_in_ranges.
        '''
        for sub_expr in self._subExpressions:
            sub_expr._var_index_shifts_in_ranges(var, shifts)
    
    def _check_param_occurrences(self, param_var, allowed_forms):
        '''
        When a Lambda expression introduces a variable in a new scope
        with a parameter entry that is an IndexedVar or a range
        of IndexedVars, its occurrences must all match that
        index or range exactly.  Raise a ValueError if the check fails.
        This restriction intended to strike a 
        balance between simplicity and versatility.
        '''
        if self in allowed_forms:
            # This branch is okay if it matches a valid occurence.
            return 
        for sub_expr in self._subExpressions:
            sub_expr._check_param_occurrences(param_var, allowed_forms)

    def safeDummyVar(self):
        from proveit._core_.expression.label.var import safeDummyVar
        return safeDummyVar(self)

    def safeDummyVars(self, n):
        from proveit._core_.expression.label.var import safeDummyVars
        return safeDummyVars(n, self)
            
    def evaluation(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        If possible, return a KnownTruth of this expression equal to its
        irreducible value.  Checks for an existing evaluation.  If it
        doesn't exist, try some default strategies including a reduction.
        Attempt the Expression-class-specific "doReducedEvaluation"
        when necessary.
        '''
        from proveit.logic import (Equals, defaultSimplification, 
                                   SimplificationError, EvaluationError)
        from proveit import KnownTruth
        from proveit.logic.irreducible_value import isIrreducibleValue

        assumptions = defaults.checkedAssumptions(assumptions)
        
        method_called = None
        try:
            # First try the default tricks. If a reduction succesfully occurs,
            # evaluation will be called on that reduction.
            evaluation = defaultSimplification(self.innerExpr(), mustEvaluate=True, 
                                               assumptions=assumptions,
                                               automation=automation)
            method_called = defaultSimplification
        except SimplificationError as e:
            if automation is False:
                raise e # Nothing else we can try when automation is off.
            # The default failed, let's try the Expression-class specific version.
            try:
                evaluation = self.doReducedEvaluation(assumptions)
                method_called = self.doReducedEvaluation
            except NotImplementedError:
                # We have nothing but the default evaluation strategy to try,
                # and that failed.
                raise EvaluationError(self, assumptions)
        
        if not isinstance(evaluation, KnownTruth) or not isinstance(evaluation.expr, Equals):
            msg = ("%s must return an KnownTruth, "
                   "not %s for %s assuming %s"
                   %(method_called, evaluation, self, assumptions))
            raise ValueError(msg)
        if evaluation.lhs != self:
            msg = ("%s must return an KnownTruth "
                   "equality with self on the left side, "
                   "not %s for %s assuming %s"
                   %(method_called, evaluation, self, assumptions))
            raise ValueError(msg)
        if not isIrreducibleValue(evaluation.rhs):
            msg = ("%s must return an KnownTruth "
                   "equality with an irreducible value on the right side, "
                   "not %s for %s assuming %s"
                   %(method_called, evaluation, self, assumptions))
            raise ValueError(msg)
        # Note: No need to store in Equals.evaluations or Equals.simplifications; this
        # is done automatically as a side-effect for proven equalities with irreducible
        # right sides.

        return evaluation
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate 'self', which should be a reduced
        expression with operands already evaluated.
        Return the evaluation as a KnownTruth equality 
        with 'self' on the left side.
        Must be overridden for class-specific evaluation.
        Raise a SimplificationError if the evaluation
        cannot be done.
        '''
        raise NotImplementedError("'doReducedEvaluation' not implemented for %s class"%str(self.__class__))       

    """
    # Generated automatically via InnerExpr.register_equivalence_method.
    def evaluated(self, assumptions=USE_DEFAULTS):
        '''
        Return the right side of an evaluation.
        '''
        return self.evaluation(assumptions=assumptions).rhs
   """ 
        
    def simplification(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        If possible, return a KnownTruth of this expression equal to a
        canonically simplified form. Checks for an existing simplifcation.
        If it doesn't exist and automation is True, try some default strategies
        including a reduction.  Attempt the Expression-class-specific 
        "doReducedSimplication" when necessary.
        '''
        from proveit import KnownTruth, ProofFailure
        from proveit.logic import (Equals, defaultSimplification, 
                                   SimplificationError, EvaluationError)
        
        assumptions = defaults.checkedAssumptions(assumptions)
        
        method_called = None
        try:
            # First try the default tricks. If a reduction succesfully occurs,
            # simplification will be called on that reduction.
            simplification = defaultSimplification(self.innerExpr(), 
                                                   assumptions=assumptions,
                                                   automation=automation)
            method_called = defaultSimplification
        except SimplificationError:
            if automation is False:
                # When automation is False, we raise an exception if there
                # is not a known simplification.
                raise SimplificationError("Unknown simplification of %s under "
                                          "assumptions %s"%(self, assumptions))
            # The default did nothing, let's try the Expression-class specific 
            # versions of evaluation and simplification.
            try:
                # first try evaluation.  that is as simple as it gets.
                simplification = self.doReducedEvaluation(assumptions)
                method_called = self.doReducedEvaluation
            except (NotImplementedError, EvaluationError):
                try:
                    simplification = self.doReducedSimplification(assumptions)
                    method_called = self.doReducedSimplification
                except (NotImplementedError, SimplificationError, ProofFailure):
                    # Simplification did not work.  Just use self-equality.
                    self_eq = Equals(self, self)
                    simplification = self_eq.prove()
                    method_called = self_eq.prove
            
        if not isinstance(simplification, KnownTruth) or not isinstance(simplification.expr, Equals):
            msg = ("%s must return a KnownTruth "
                   "equality, not %s for %s assuming %s"
                   %(method_called, simplification, self, assumptions))
            raise ValueError(msg)
        if simplification.lhs != self:
            msg = ("%s must return a KnownTruth "
                   "equality with 'self' on the left side, not %s for %s "
                   "assuming %s"%(method_called, simplification, self, assumptions))
            raise ValueError(msg)
        # Remember this simplification for next time:
        Equals.simplifications.setdefault(self, set()).add(simplification)
             
        return simplification
    
    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to simplify 'self', which should be a reduced
        expression with operands already simplified.
        Return the evaluation as a KnownTruth equality 
        with 'self' on the left side.
        Must be overridden for class-specific simplification.
        Raise a SimplificationError if the simplification
        cannot be done.
        '''
        raise NotImplementedError("'doReducedSimplification' not implemented for %s class"%str(self.__class__))             
    
    def deduceEquality(self, equality, assumptions=USE_DEFAULTS, 
                       minimal_automation=False):
        '''
        Under the given assumptions, attempt to prove the given 
        'equality' where the left-side is 'self', returning the
        proven KnownTruth.  If minimal_automation is True, don't do
        anything "fancy" to attempt to prove this.  If
        minimal_automation is False, this default version attempts
        to deduce equality by simplifying both sides and proving
        that the simplified forms are equal.
        '''
        from proveit.logic import Equals
        assert isinstance(equality, Equals) and equality.lhs == self
        if minimal_automation:
            return equality.prove(assumptions, automation=False)

        # Try to prove equality via simplifying both sides.
        lhs_simplification = equality.lhs.simplification(assumptions)
        rhs_simplification = equality.rhs.simplification(assumptions)
        simplified_lhs = lhs_simplification.rhs
        simplified_rhs = rhs_simplification.rhs
        if simplified_lhs != equality.lhs or simplified_rhs != equality.rhs:
            simplified_eq = Equals(simplified_lhs, simplified_rhs).prove(assumptions)
            return Equals.applyTransitivities(
                    [lhs_simplification, simplified_eq, rhs_simplification],
                    assumptions)
    
    """
    # Generated automatically via InnerExpr.register_equivalence_method.
    def simplified(self, assumptions=USE_DEFAULTS):
        '''
        Return the right side of a simplification.
        '''
        return self.simplification(assumptions=assumptions).rhs
    """
    
    def orderOfAppearance(self, subExpressions):
        '''
        Yields the given sub-Expressions in the order in which they
        appear in this Expression.  There may be repeats.
        '''
        if self in subExpressions:
            yield self
        for subExpr in self._subExpressions:
            for expr in subExpr.orderOfAppearance(subExpressions):
                yield expr
    
    def _repr_html_(self, context=None, unofficialNameKindContext=None):
        '''
        Generate html to show a png compiled from the latex (that may be recalled
        from memory or storage if it was generated previously) with a link to
        an expr.ipynb notebook for displaying the expression information.
        If 'context' is provided, find the stored expression information in
        that context; otherwise, use the default, current directory Context.
        If 'unofficialNameKindContext' is provided, it should be the 
        (name, kind, context) for a special expression that is not-yet-official
        (%end_[common/axioms/theorems] has not been called yet in the special 
        expressions notebook).
        '''
        if not defaults.display_latex:
            return None # No LaTeX display at this time.
        if context is None:
            context = Context()
        if not hasattr(self._styleData,'png'):
            self._styleData.png, png_url = context._stored_png(self, self.latex(), self._config_latex_tool)
            self._styleData.png_url = png_url
        if self._styleData.png_url is not None:
            expr_notebook_rel_url = context.expressionNotebook(self, unofficialNameKindContext)
            html = '<a class="ProveItLink" href="' + expr_notebook_rel_url + '">'
            encoded_png = encodebytes(self._styleData.png).decode("utf-8") 
            html += '<img src="data:image/png;base64,' + encoded_png + r'" style="display:inline;vertical-align:middle;" />'
            html += '</a>'
        # record as a "displayed" (style-specific) expression
        Expression.displayed_expression_styles.add((self._style_id, self)) 
        return html
        
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        for sub_expr in self._subExpressions:
            sub_expr._config_latex_tool(lt)

    def exprInfo(self, details=False):
        from proveit._core_.expression.expr_info import ExpressionInfo
        return ExpressionInfo(self, details)
        
def used_vars(expr):
    '''
    Return all of the used Variables of this Expression,
    included those in sub-expressions.
    '''
    return expr._used_vars(expr)

def free_vars(expr, exclusions=frozenset()):
    '''
    Return all of the free Variables of this Expression,
    included those in sub-expressions but excluding those with internal
    bindings within Lambda expressions.  If this Expression
    is in the exclusions set, skip over it.
    '''
    return expr._free_vars(exclusions=exclusions)

def expressionDepth(expr):
    '''
    Returns the depth of the expression tree for the given expression.
    '''
    subDepths = [expressionDepth(subExpr) for subExpr in expr.subExprIter()]
    if len(subDepths)==0: 
        return 1 # no sub-expressions
    return max(subDepths)+1 # add 1 to the maximum of the sub-expression depths

class MakeNotImplemented(NotImplementedError):
    def __init__(self, exprSubClass):
        self.exprSubClass = exprSubClass
    def __str__(self):
        return "make method not implemented for " + str(self.exprSubClass)

class ImproperSubstitution(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class DisallowedIndexing(Exception):
    def __init__(self, var, action, start1_base, end1_base, 
                 start2_base=None, end2_base=None,
                 range_parameter=None):
        self.var = var
        self.action = action
        self.start1_base = start1_base
        self.end1_base = end1_base
        self.start2_base = start2_base
        self.end2_base = end2_base
        self.range_parameter=None
    def __str__(self):
        if self.action=='join':
            preposition = 'with'
        elif self.action=='eliminate':
            preposition = 'from'
        elif self.action=='range':
            return ("To keep the ranges of indices of IndexedVar's clear "
                    "and simple, IndexedVar's within am ExprRange that "
                    "are parameterized by the range parameter must use "
                    "simple constant shifts relative to the range parameter."
                    "For %s, this is violated for indices around %s..%s "
                    "over the range parameter %s."
                    %(self.var, self.action, self.start1_base, self.end1_base, 
                      self.range_parameter))
        else:
            raise ValueError("Not a valid action: %s"%self.action)
        return ("To keep the ranges of indices of IndexedVar's clear "
                "and simple, different ranges may only have constant "
                "shifts with respect to each other.  For %s, this is "
                "violated when attempting to %s a range around %s..%s "
                "%s a range around %s..%s"
                %(self.var, self.action, self.start1_base, self.end1_base, 
                  preposition, self.start2_base, self.end2_base))

class _NoExpandedIteration(Exception):
    '''
    Used internally for _expandingIterRanges.
    '''
    def __init__(self):
        pass
    

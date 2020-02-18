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
                        
    def __init__(self, coreInfo, subExpressions=tuple(), styles=None, requirements=tuple()):
        '''
        Initialize an expression with the given coreInfo (information relevant at the core Expression-type
        level) which should be a list (or tuple) of strings, and a list (or tuple) of subExpressions.
        "styles" is a dictionary used to indicate how the Expression should be formatted
        when there are different possibilities (e.g. division with '/' or as a fraction).  The meaning
        of the expression is independent of its styles signature.
        The "requirements" are expressions that must be proven to be true in order for the Expression
        to make sense.
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
                # combine requirements from all sub-expressions
                requirements = sum([subExpression.getRequirements() for subExpression 
                                    in subExpressions], tuple()) + requirements
                # Expression requirements are essentially assumptions that need
                # to be proven for the expression to be valid.  Calling 
                # "checkAssumptions" will remove repeats and generate proof by 
                # assumption for each (which may not be necessary, but does not
                # hurt).   
                self._meaningData._requirements = \
                    defaults.checkedAssumptions(requirements)
        
        # The style data is shared among Expressions with the same structure and style -- this will contain the 'png' generated on demand.
        self._styleData = styleData(self._generate_unique_rep(lambda expr : hex(expr._style_id), coreInfo, styles))
        # initialize the style options
        self._styleData.styles = dict(styles) # formatting style options that don't affect the meaning of the expression

        # reference this unchanging data of the unique 'meaning' data
        self._meaning_id = self._meaningData._unique_id
        self._coreInfo = self._meaningData._coreInfo
        self._requirements = self._meaningData._requirements
        
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
    
    def _generic_version(self):
        '''
        Retrieve (and create if necessary) the generic version of this 
        expression in which deterministic 'dummy' variables are used as Lambda
        parameters, determines the 'meaning' of the expression.
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
        self._genericExpr = self.__class__._make(self._meaningData._coreInfo, 
                                                 dict(self._styleData.styles), 
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
    def _make(subClass, coreInfo, styles, subExpressions):
        '''
        Should make the Expression object for the specific Expression sub-class based upon the coreInfo
        and subExpressions.  Must be implemented for each core Expression sub-class that can be instantiated.
        '''
        raise MakeNotImplemented(subClass)
                    
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
        access any inner sub-expression for the purpose of creating
        a lambda expression to replace the inner expression within
        this one or change its styles.
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
        return self._styleData.styles.get(styleName, default)
    
    def getStyles(self):
        '''
        Return a copy of the internally maintained styles dictionary.
        '''
        return dict(self._styleData.styles)
    
    def getRequirements(self):
        '''
        Return a copy of the requirements.
        '''
        return tuple(self._requirements)
     
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
                
        # Note: exclude WILDCARD_ASSUMPTIONS when looking for an existing proof.
        #   (may not matter, but just in case).
        foundTruth = KnownTruth.findKnownTruth(self, (assumptionsSet - {'*'}))
        if foundTruth is not None: 
            foundTruth.withMatchingStyles(self, assumptions) # give it the appropriate style
            return foundTruth # found an existing KnownTruth that does the job!
                
        if self in assumptionsSet or '*' in assumptionsSet:
            # prove by assumption if self is in the list of assumptions or
            # WILDCARD_ASSUMPTIONS is in the list of assumptions.
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
    
    def substituted(self, exprMap, relabelMap=None, reservedVars=None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with the expressions substituted 
        according to the exprMap dictionary (mapping Expressions to Expressions --
        for specialize, this may only map Variables to Expressions).
        If supplied, reservedVars is a dictionary that maps reserved Variable's
        to relabeling exceptions.  You cannot substitute with an expression that
        uses a restricted variable and you can only relabel the exception to the
        restricted variable.  This is used to protect an Lambda function's "scope".
        
        For certain Expression classes in proveit._core_.expression.composite,
        intermediate proofs may be required.  This is why assumptions may be
        needed.  If a list is passed into requirements, KnownTruth's for these
        intermediate proofs will be appended to it -- these are requirements
        for the substitution to be valid.
        '''
        self._checkRelabelMap(relabelMap)
        if len(exprMap)>0 and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return self
    
    def relabeled(self, relabelMap, reservedVars=None):
        '''
        A watered down version of substituted in which only variable labels are
        changed.
        '''
        return self.substituted(exprMap=dict(), relabelMap=relabelMap, reservedVars=reservedVars)
    
    def _checkRelabelMap(self, relabelMap):
        '''
        Make sure that all of the relabelMap keys are Variable objects
        '''
        from proveit import Variable
        if relabelMap is None: return
        for key in relabelMap:
            if not isinstance(key, Variable):
                raise TypeError("relabelMap keys must be Variables")
    
    def copy(self):
        '''
        Make a copy of the Expression with the same styles.
        '''
        expr_copy = self.substituted(exprMap=dict()) # vacuous substitution makes a copy
        return expr_copy

    def _iterSubParamVals(self, axis, iterParam, startArg, endArg, exprMap, 
                          relabelMap=None, reservedVars=None, 
                          assumptions=USE_DEFAULTS, requirements=None):
        '''
        Consider a substitution over a containing iteration (Iter) defined via exprMap, 
        relabelMap, etc, and expand the iteration by substituting the 
        "iteration parameter" over the range from the "starting argument" to the 
        "ending argument" (both inclusive).
        
        This default version merge-sorts the results from all
        sub-expressions or raises a _NoExpandedIteration exception\
        if none of the sub-expressions yield anything to indicate
        that any containing Indexed variable is being expanded.
        '''                
        from proveit.number import LessEq       
        from proveit._core_.expression.expr import _NoExpandedIteration
        from proveit._core_.expression.composite.composite import _generateCoordOrderAssumptions
        # Collect the iteration substitution parameter values for all 
        # of the operators and operands and merge them together.
        val_lists = []
        extended_assumptions = list(assumptions)
        if requirements is None: requirements = []
        for sub_expr in self._subExpressions:
            try:
                vals = sub_expr._iterSubParamVals(axis, iterParam, startArg, 
                                                  endArg, exprMap, relabelMap, 
                                                  reservedVars, assumptions, 
                                                  requirements)
                extended_assumptions.extend(_generateCoordOrderAssumptions(vals))
                val_lists.append(vals)
            except _NoExpandedIteration:
                pass
        if len(val_lists) == 0:
            raise _NoExpandedIteration()
        
        # We won't add the requirements for the sorting here.  Instead, we will make
        # sure differences are in naturals numbers at the Iter.substitution level.
        param_vals = LessEq.mergesorted_items(val_lists, assumptions=extended_assumptions,
                                              skip_exact_reps=True, skip_equiv_reps=True)
        return list(param_vals)
        
    def _validateRelabelMap(self, relabelMap):
        if len(relabelMap) != len(set(relabelMap.values())):
            raise ImproperRelabeling("Cannot relabel different Variables to the same Variable.")
    
    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.subExprIter()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.subExprIter()])

    def freeMultiVars(self):
        """
        Returns the used multi-variables that are not bound as an instance variable
        or wrapped in a Bundle (see multiExpression.py).
        """
        return set()    

    def safeDummyVar(self):
        from proveit._core_.expression.label.var import safeDummyVar
        return safeDummyVar(self)

    def safeDummyVars(self, n):
        from proveit._core_.expression.label.var import safeDummyVars
        return safeDummyVars(n, self)
            
    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        If possible, return a KnownTruth of this expression equal to its
        irreducible value.  Checks for an existing evaluation.  If it
        doesn't exist, try some default strategies including a reduction.
        Attempt the Expression-class-specific "doReducedEvaluation"
        when necessary.
        '''
        from proveit.logic import Equals, defaultSimplification, SimplificationError
        from proveit import KnownTruth, ProofFailure
        from proveit.logic.irreducible_value import isIrreducibleValue
        
        method_called = None
        try:
            # First try the default tricks. If a reduction succesfully occurs,
            # evaluation will be called on that reduction.
            evaluation = defaultSimplification(self.innerExpr(), mustEvaluate=True, assumptions=assumptions)
            method_called = defaultSimplification
        except SimplificationError as e:
            # The default failed, let's try the Expression-class specific version.
            try:
                evaluation = self.doReducedEvaluation(assumptions)
                method_called = self.doReducedEvaluation
            except NotImplementedError:
                # We have nothing but the default evaluation strategy to try, and that failed.
                raise e 
        
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
                   %(method_name, evaluation, self, assumptions))
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
        
    def simplification(self, assumptions=USE_DEFAULTS):
        '''
        If possible, return a KnownTruth of this expression equal to a
        canonically simplified form. Checks for an existing simplifcation.
        If it doesn't exist, try some default strategies including a reduction.
        Attempt the Expression-class-specific "doReducedSimplication"
        when necessary.
        '''
        from proveit.logic import Equals, defaultSimplification, SimplificationError
        from proveit import KnownTruth, ProofFailure
        
        method_called = None
        try:
            # First try the default tricks. If a reduction succesfully occurs,
            # simplification will be called on that reduction.
            simplification = defaultSimplification(self.innerExpr(), assumptions=assumptions)
            method_called = defaultSimplification
        except SimplificationError as e:
            # The default did nothing, let's try the Expression-class specific versions of
            # evaluation and simplification.
            try:
                # first try evaluation.  that is as simple as it gets.
                simplification = self.doReducedEvaluation(assumptions)
                method_called = self.doReducedEvaluation
            except (NotImplementedError, SimplificationError):
                try:
                    simplification = self.doReducedSimplification(assumptions)
                    method_called = self.doReducedSimplification
                except (NotImplementedError, SimplificationError):
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
        
    def _restrictionChecked(self, reservedVars):
        '''
        Check that a substituted expression (self) does not use any 
        reserved variables (parameters of a Lambda function Expression).
        '''
        if reservedVars is not None \
                and not self.freeVars().isdisjoint(reservedVars.keys()):
            intersection = self.freeVars().intersection(reservedVars.keys())
            msg = ("Must not make substitution with reserved variables "
                   "(i.e., parameters of a Lambda function).\n"
                   "These variables are in violation: %s"%str(intersection))
            raise ScopingViolation(msg)
        return self

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

class ImproperRelabeling(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class ScopingViolation(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

class _NoExpandedIteration(Exception):
    '''
    Used internally for _expandingIterRanges.
    '''
    def __init__(self):
        pass
    

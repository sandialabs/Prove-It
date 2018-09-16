"""
This is the expression module.
"""

from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.context import Context
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_._proveit_object_utils import makeUniqueId, addParent, updateStyles
import re
import os

class ExprType(type):
    '''
    By overriding the Expression type, we can make Operation-type
    expressions automatically populate the Operation.operationClassOfOperator
    dictionary as long as the relevent '_operator_' class attribute is 
    accessed at least once.
    '''
    
    def __getattribute__(cls, name):
        from proveit._core_.expression.operation import Operation
        value = type.__getattribute__(cls, name)
        if issubclass(cls, Operation) and name == '_operator_':
            Operation.operationClassOfOperator[value] = cls
        return value

class Expression:
    __metaclass__ = ExprType
    
    # set of expression (style_id, Expression) pairs for which __repr_html__ has been called this session:
    displayed_expression_styles = set() 
    
    # map expression to contexts (for expressions that "belong" to a Context)
    contexts = dict() 
    
    # (expression, assumption) pairs for which conclude is in progress, tracked to prevent infinite
    # recursion in the `prove` method.
    in_progress_to_conclude = set() 
            
    def __init__(self, coreInfo, subExpressions=tuple(), styles=dict(), requirements=tuple()):
        '''
        Initialize an expression with the given coreInfo (information relevant at the core Expression-type
        level) which should be a list (or tuple) of strings, and a list (or tuple) of subExpressions.
        "styles" is a dictionary used to indicate how the Expression should be formatted
        when there are different possibilities (e.g. division with '/' or as a fraction).  The meaning
        of the expression is independent of its styles signature.
        The "requirements" are expressions that must be proven to be true in order for the Expression
        to make sense.
        '''
        for coreInfoElem in coreInfo:
            if not isinstance(coreInfoElem, str):
                raise TypeError('Expecting coreInfo elements to be of string type')
        for subExpression in subExpressions:
            if not isinstance(subExpression, Expression):
                raise TypeError('Expecting subExpression elements to be of Expression type')
        # unique_rep is a unique representation based upon the coreInfo and unique_id's of sub-Expressions
        self._coreInfo, self._subExpressions = tuple(coreInfo), subExpressions
        self._styles = dict(styles) # formatting style options that don't affect the meaning of the expression
        # meaning representations and unique ids are independent of style
        self._meaning_rep = self._generate_unique_rep(lambda expr : hex(expr._meaning_id))
        self._meaning_id = makeUniqueId(self._meaning_rep)
        # style representations and unique ids are dependent of style
        self._style_rep = self._generate_unique_rep(lambda expr : hex(expr._style_id), includeStyle=True)
        self._style_id = makeUniqueId(self._style_rep)
        for subExpression in subExpressions: # update Expression.parent_expr_map
            addParent(subExpression, self)
        # combine requirements from all sub-expressions
        requirements = sum([tuple(subExpression.requirements) for subExpression in subExpressions], tuple()) + requirements
        # Expression requirements are essentially assumptions that need to be proven for the expression to
        # be valid.  Calling "checkAssumptions" will remove repeats and generate proof by assumption for each
        # (which may not be necessary, but does not hurt).   
        self.requirements = defaults.checkedAssumptions(requirements)
    
    def _generate_unique_rep(self, objectRepFn, includeStyle=False):
        '''
        Generate a unique representation string using the given function to obtain representations of other referenced Prove-It objects.
        '''
        import sys
        context = Context(sys.modules[self.__class__.__module__].__file__)
        # get the full class path relative to the root context where the class is defined
        class_path = context.name + '.' + self.__class__.__module__.split('.')[-1] + '.' + self.__class__.__name__
        style_str = ''
        if includeStyle:
            style_str = ';[' + ','.join(style_name + ':' + self.getStyle(style_name) for style_name in sorted(self.styleNames())) + ']'
        return class_path + '[' + ','.join(self._coreInfo) + ']' + style_str + ';[' + ','.join(objectRepFn(expr) for expr in self._subExpressions) + ']'

    @staticmethod
    def _extractExprClass(unique_rep):
        '''
        Return the class of the Expression with the given unique representation.
        '''
        return unique_rep[:unique_rep.find('[')]

    @staticmethod
    def _extractCoreInfo(unique_rep):
        '''
        Return the core information of the given unique representation.
        '''
        return re.split(',', unique_rep[unique_rep.find('[')+1:unique_rep.find(']')])
    
    @staticmethod
    def _extractStyle(unique_rep):
        '''
        Return the style information of the given unique representation assuming the style was included.
        '''
        style_str = unique_rep.split(';')[1]
        style_pairs = re.split("\[|,|\]",style_str) 
        return dict(style_pair.split(':') for style_pair in style_pairs if len(style_pair)>0)
        
    @staticmethod
    def _extractReferencedObjIds(unique_rep):
        '''
        Given a unique representation string, returns the list of representations
        of Prove-It objects that are referenced.
        '''
        # After the ';' comes the list of sub-Expressions.
        subExprs = unique_rep.split(';')[-1]
        objIds = re.split("\[|,|\]",subExprs) 
        return [objId for objId in objIds if len(objId) > 0]  
        
    def __setattr__(self, attr, value):
        '''
        Expressions should be read-only objects.  Attributes may be added, however; for example,
        the 'png' attribute which will be added whenever it is generated).
        '''
        if hasattr(self, attr):
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
        Alter the styles of this expression according to kwargs.
        '''
        orig_styles = dict(self._styles)
        # update the _styles, _style_rep, and _style_id
        self._styles.update(kwargs)
        if self._styles == orig_styles:
            return self # no change in styles, so just use the original
        updateStyles(self)
        return self
    
    def styleNames(self):
        '''
        Return the name of the styles that may be set.
        '''
        return self._styles.keys()
    
    def getStyle(self, styleName):
        '''
        Return the current style setting for the given style name.
        '''
        return self._styles[styleName]
    
    def getStyles(self):
        '''
        Return a copy of the internally maintained styles dictionary.
        '''
        return dict(self._styles)
    
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
            return foundTruth # found an existing KnownTruth that does the job!
                
        if self in assumptionsSet or '*' in assumptionsSet:
            # prove by assumption if self is in the list of assumptions or
            # WILDCARD_ASSUMPTIONS is in the list of assumptions.
            from proveit._core_.proof import Assumption
            return Assumption(self, assumptions).provenTruth
        
        if not automation:
            raise ProofFailure(self, assumptions, "No pre-existing proof")
                                                
        # Use Expression.in_progress_to_conclude set to prevent an infinite recursion
        in_progress_key = (self, tuple(sorted(assumptions)))
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
                except:
                    # try the 'conclude' method of the specific Expression class
                    concludedTruth = self.conclude(assumptions)
            if concludedTruth is None:
                raise ProofFailure(self, assumptions, "Failure to automatically 'conclude'")
            if not isinstance(concludedTruth, KnownTruth):
                raise ValueError("'conclude' method should return a KnownTruth (or raise an exception)")
            if concludedTruth.expr != self:
                raise ValueError("'conclude' method should return a KnownTruth for this Expression object.")
            if not concludedTruth.assumptionsSet.issubset(assumptionsSet):
                raise ValueError("While proving " + str(self) + ", 'conclude' method returned a KnownTruth with extra assumptions: " + str(set(concludedTruth.assumptions) - assumptionsSet))
            return concludedTruth
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
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return self
    
    def relabeled(self, relabelMap, reservedVars=None):
        '''
        A watered down version of substituted in which only variable labels are
        changed.
        '''
        return self.substituted(exprMap=dict(), relabelMap=relabelMap, reservedVars=reservedVars)
    
    def copy(self):
        '''
        Make a copy of the Expression with the same styles.
        '''
        expr_copy = self.substituted(exprMap=dict()) # vacuous substitution makes a copy
        return expr_copy

    def _expandingIterRanges(self, iterParams, startArgs, endArgs, exprMap, relabelMap = None, reservedVars = None, assumptions=USE_DEFAULTS, requirements=None):
        '''
        # empty by default.
        # Overridden by proveit._core_.expression.composite.indexed.Indexed.
        '''
        return iter(())
        
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
        from proveit._core_.expression.label.var import safeDummyVar
        dummyVars = []
        for _ in range (n):
            dummyVars.append(safeDummyVar(*([self] + dummyVars)))
        return dummyVars
            
    def evaluation(self, assumptions=USE_DEFAULTS):
        '''
        If possible, return a KnownTruth of this expression equal to its
        irreducible value.  Override for other appropriate functionality.
        '''
        from proveit.logic import defaultSimplification
        return defaultSimplification(self.innerExpr(), inPlace=False, mustEvaluate=True, assumptions=assumptions)

    def simplification(self, assumptions=USE_DEFAULTS):
        '''
        If possible, return a KnownTruth of this expression equal to its
        irreducible value.  Override for other appropriate functionality.
        '''
        from proveit.logic import defaultSimplification
        return defaultSimplification(self.innerExpr(), inPlace=False, assumptions=assumptions)        
    
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
        Check that a substituted expression (self) does not use any reserved variables
        (parameters of a Lambda function Expression).
        '''
        if not reservedVars is None and not self.freeVars().isdisjoint(reservedVars.keys()):
            raise ScopingViolation("Must not make substitution with reserved variables  (i.e., parameters of a Lambda function)")
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
        if not hasattr(self,'png'):
            self.png, png_path = context._stored_png(self, self.latex(), self._config_latex_tool)
            self.png_path = os.path.relpath(png_path)
        if self.png_path is not None:
            exprNotebookPath = context.expressionNotebook(self, unofficialNameKindContext)
            html = '<a class="ProveItLink" href="' + os.path.relpath(exprNotebookPath) + '">'
            html += '<img src="' + self.png_path + r'" style="display:inline;vertical-align:middle;" />'
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


    

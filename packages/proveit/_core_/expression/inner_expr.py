from .expr import Expression
from .operation import Function
from .lambda_expr import Lambda
from .composite import ExprList, Composite, NamedExprs, compositeExpression
from proveit._core_.defaults import USE_DEFAULTS
import inspect

class InnerExpr:
    '''
    Represents an "inner" sub-expression of a particular "topLevel" 
    expression.  The innerExpr method of the Expression class 
    will start an InnerExpr with that particular expression as 
    the top-level.  This acts as an expression wrapper, 
    starting at the top-level expression but can "descend" to
    any sub-expression via accessing sub-expression attributes.
    This will allow us to manipute the inner expression in the
    context of the containing expression.  One can change the
    style of the inner expression or replace it with an 
    equivalent form.
    
    Equivalence methods may be registered via 
    InnerExpr.register_equivalence_method(...).
    Registering an equivalence method allows one to directly
    replace the inner expression with a form that is produced
    by calling the equivalence method.  Examples are:
        evaluation, simplification, commutation, association, etc.
    When registering such a method, a noun form (as above), a
    past tense form, and an action form are to be simplied
    (e.g., 'evaluation', 'evaluated', and 'evaluate').  Calling
    the first version (e.g., 'evaluation') will produce a proven 
    equality between the original top-level expression and a form 
    in which the inner expression is replaced with its new form.
    Calling the second version (e.g., 'evaluated') will prove
    the equality as before but simply return the right side (the
    new form of the top-level, with the inner expression replaced).
    The last version (e.g., 'evaluate') is to be applied to
    proven (or easilty provable) top-level expressions and will
    yield the proven top-level expression (under given assumptions)
    with the inner expression replaced by its equivalent form.
    
    For example, let "expr = [((a - 1) + b + (a - 1)/d) < e]", and let
    "inner_expr = expr.innterExpr().lhs.terms[2].numerator".  Then
    
    1. inner_expr.replMap() will return _x_ -> [(a + b + _x_/d) < e],
       replacing the particular innerexpr.
       (note that the second "a - 1" is singled out, distinct from
       the first "a*1" because the subexpr object tracks the
       sub-expression by "location").
    2. inner_expr.withSubtractionAt([]) will return an
       expression that is the same but with an altered style for the
       inner exrpession part:
           [((a - 1) + b + (a + (-1))/d) < e]
       The InnerExpr class looks specifically for attributes of the
       inner expression class that start with 'with' and assumes
       they function to alter the style.
    3. inner_expr.commutation(0, 1) would return: 
           |- [((a - 1) + b + (a - 1)/d) < e] = [((a - 1) + b + (-1 + a)/d) < e]
       assuming 'a' is known to be a number.
    4. inner_expr.commuted(0, 1) would return: 
           [((a - 1) + b + (-1 + a)/d) < e]
       assuming 'a' is known to be a number.  It will prove #3 along the way.
    5. inner_expr.commute(0, 1) would return
           |-  ((a - 1) + b + (-1 + a)/d) < e
       assuming the original expr may be proven via automation and
       'a' is known to be a number.
    
    In addition, the InnerExpr class has 'simplifyOperands' and
    'evaluateOperands' methods for effecting 'simplify' or 'evaluate'
    (respectively) on all of the operands of the inner expression.
    '''
    
    def __init__(self, topLevelExpr, innerExprPath=tuple()):
        '''
        Create an InnerExpr with the given top-level Expression.
        Optionally, subExprPath is a sequence of sub-Expression indices
        starting from the topLevel expression as the root to produce
        a map for replacing the corresponding sub-Expression.  A new
        SubExprRepl is generated appropriately, extending the 
        sub-Expression path, when getting an item or attribute
        that corresponds with an item/attribute of the currently
        mapped sub-Expression.
        '''
        from proveit import KnownTruth
        if isinstance(topLevelExpr, KnownTruth):
            topLevelExpr = topLevelExpr.expr
        self.innerExprPath = tuple(innerExprPath)
        self.exprHierarchy = [topLevelExpr]
        # list all of the lambda expression parameters encountered
        # along the way from the top-level expression to the inner expression.
        self.parameters = []
        expr = self.exprHierarchy[0]
        for idx in self.innerExprPath:
            if isinstance(expr, Lambda) and idx==expr.numSubExpr()-1:
                # while descending into a lambda expression body, we
                # pick up the lambda parameters.
                self.parameters.extend(expr.parameters)
            expr = expr.subExpr(idx)
            self.exprHierarchy.append(expr)
    
    def __eq__(self, other):
        return self.innerExprPath==other.innerExprPath and self.exprHierarchy==other.exprHierarchy
    
    def __getitem__(self, key):
        '''
        If the currently mapped sub-Expression of the SubExprRepl
        is a Composite, accessing an item corresponding to an item
        of this Composite will return the SubExprRepl with the extended 
        path to this item.
        '''
        curInnerExpr = self.exprHierarchy[-1]
        if isinstance(curInnerExpr, ExprList):
            # For an ExprList, the item key is simply the index of the sub-Expression
            if key < 0: key = len(curInnerExpr)+key
            return InnerExpr(self.exprHierarchy[0], self.innerExprPath + (key,))
        elif isinstance(curInnerExpr, Composite):
            # For any other Composite (ExprTensor or NamedExprs), the key is the key of the Composite dictionary.
            # The sub-Expressions are in the order that the keys are sorted.
            sortedKeys = sorted(curInnerExpr.keys())
            return InnerExpr(self.exprHierarchy[0], self.innerExprPath + [sortedKeys.index(key)])
        raise KeyError("The current sub-Expression is not a Composite.")
    
    def _getAttrAsInnerExpr(self, cur_depth, attr, attr_expr):
        '''
        Try to find a deeper inner expression that corresponds with the
        attribute (attr) of the expression at the given current depth (cur_depth)
        along the self InnerExpr.  It will perform a recursive breadth-first
        search until it finds a match, making sure the deeper inner expression 
        corresponds with that specific attribute (not just happening to be the
        same sub-expression that could occur multiple places).
        '''
        top_level_expr = self.exprHierarchy[0]
        cur_inner_expr = self.exprHierarchy[-1]
        inner_subs = list(cur_inner_expr.subExprIter())
        for i, inner_sub in enumerate(inner_subs):
            # See if any off the sub-expressions
            if inner_sub == attr_expr:
                deeper_inner_expr = InnerExpr(top_level_expr, self.innerExprPath + (i,))       
                repl_map = deeper_inner_expr.replMap()
                sub_expr = repl_map.body
                for j in self.innerExprPath[:cur_depth]:
                    sub_expr = sub_expr.subExpr(j)
                if repl_map.parameterVarSet.issubset(compositeExpression(getattr(sub_expr, attr)).freeVars()):
                    return deeper_inner_expr
        # No match found at this depth -- let's continue to the next depth
        for i, inner_sub in enumerate(inner_subs):
            inner_expr = InnerExpr(self.exprHierarchy[0], self.innerExprPath + (i,))._getAttrAsInnerExpr(cur_depth,  attr, attr_expr)
            if inner_expr is not None:
                return inner_expr
        return None # no match found down to the maximum depth
        
        
    def __getattr__(self, attr):
        '''
        See if the attribute is accessing a deeper inner expression of the 
        represented inner expression.  If so, return the InnerExpr with the 
        extended path to the sub-expression.
        For methods of the inner expression that beginn as 'with', generate a
        method that returns a new version of the top-level expression with the 
        inner expression changed according to its 'with' method.   
        '''
        cur_inner_expr = self.exprHierarchy[-1]
        
        if hasattr(cur_inner_expr.__class__, '_equiv_method_%s_'%attr):
            equiv_method_type, equiv_method_name = \
                getattr(cur_inner_expr.__class__, '_equiv_method_%s_'%attr)
            equiv_method = getattr(cur_inner_expr, equiv_method_name)
            # Find out which argument is the 'assumptions' argument:
            try:
                argspec = inspect.getfullargspec(equiv_method)
                assumptions_index = argspec.args.index('assumptions')-1
            except ValueError:
                raise Exception("Expecting method, %s, to have 'assumptions' argument."%str(equiv_method))
            repl_map = self.replMap()
            def inner_equiv(*args, **kwargs):
                if 'assumptions' in kwargs:
                    assumptions = kwargs['assumptions']
                elif len(args) > assumptions_index:
                    assumptions = args[assumptions_index]
                else:
                    assumptions = USE_DEFAULTS
                equivalence = equiv_method(*args, **kwargs)
                if equiv_method_type == 'equiv':
                    return equivalence.substitution(repl_map, assumptions)
                elif equiv_method_type == 'rhs':
                    return equivalence.substitution(repl_map, assumptions).rhs
                elif equiv_method_type == 'action':
                    return equivalence.subRightSideInto(repl_map, assumptions)
            if equiv_method_type == 'equiv':
                inner_equiv.__doc__ = "Generate an equivalence of the top-level expression with a new form by replacing the inner expression via '%s'."%equiv_method_name
            elif equiv_method_type == 'rhs':
                inner_equiv.__doc__ = "Return an equivalent form of the top-level known truth by replacing the inner expression via '%s'."%equiv_method_name                         
            elif equiv_method_type == 'action':
                inner_equiv.__doc__ = "Derive an equivalent form of the top-level known truth by replacing the inner expression via '%s'."%equiv_method_name             
            else:
                raise ValueError("Unexpected 'equivalence method' type: %s."%equiv_method_type)
            inner_equiv.__name__ = attr
            return inner_equiv
                
        if not hasattr(cur_inner_expr, attr):
            raise AttributeError("No attribute '%s' in '%s' or '%s'"%(attr, self.__class__, cur_inner_expr.__class__))
        
        inner_attr_val = getattr(cur_inner_expr, attr)
        if isinstance(inner_attr_val, Expression):
            # The attribute is addressing a sub-Expression of the current inner Expression
            # and may be a sub-sub-Expression (or a member of sub-sub-Expression composite);
            # if so, return the SubExprRepl extended to the sub-sub-Expression.
            inner_expr = self._getAttrAsInnerExpr(len(self.innerExprPath), attr, inner_attr_val)
            if inner_expr is not None:
                return inner_expr
        elif attr[:4] == 'with':
            def reviseInnerExpr(*args, **kwargs):
                cur_sub_expr = self.exprHierarchy[-1]
                # call the 'with...' method on the inner expression:
                getattr(cur_sub_expr, attr)(*args, **kwargs)  # this will also revise the styles of all parents recursively 
                return self.exprHierarchy[0] # return the top-level expression
            return reviseInnerExpr
                
        return getattr(cur_inner_expr, attr) # not a sub-expression, so just return the attribute for the actual Expression object of the sub-expression
    
    @staticmethod
    def register_equivalence_method(expr_class, equiv_method, past_tense_name, action_name):
        '''
        Register a method of an expression class that is used to derive and return (as a KnownTruth)
        the equivalence of that expression on the left side with a new form on the right side.
        (e.g., 'simplification', 'evaluation', 'commutation', 'association').
        In addition to the expression class and the method (as a name or function object), also
        provide the "past-tense" form of the name for deriving the equivalence and returning
        the right side, and provide the "action" form of the name that may be used to make
        the replacement directly within a KnownTruth to produce a revised KnownTruth.
        The "past-tense" version will be added automatically as a method to the given expression
        class with an appropriate doc string.
        '''
        if not isinstance(equiv_method, str):
            # can be a string or a function:
            equiv_method = equiv_method.__name__
        if not hasattr(expr_class, equiv_method):
            raise Exception("Must have '%s' method defined in class '%s' in order to register it as an equivalence method in InnerExpr."%(equiv_method, str(expr_class)))
        
        # Store information in the Expression class that will enable calling
        # InnerExpr methods when an expression of that type
        # is the inner expression for generating equivalences or performing
        # in-place replacements.
        setattr(expr_class, '_equiv_method_%s_'%equiv_method, ('equiv', equiv_method))
        setattr(expr_class, '_equiv_method_%s_'%past_tense_name, ('rhs', equiv_method))
        setattr(expr_class, '_equiv_method_%s_'%action_name, ('action', equiv_method))
        
        # Automatically create the "paste-tense" equivalence method for the
        # expression class which returns the right side.
        if hasattr(expr_class, past_tense_name):
            raise Exception("Should not manually define '%s' in class '%s'.  This 'past-tense' equivalence method will be generated automatically by registering it in InnerExpr."%(past_tense_name, str(expr_class)))
        def equiv_rhs(expr, *args, **kwargs):
            return getattr(expr_class, equiv_method)(expr, *args, **kwargs).rhs
        equiv_rhs.__name__ = past_tense_name
        equiv_rhs.__doc__ = "Return an equivalent form of this expression derived via '%s'."%equiv_method
        setattr(expr_class, past_tense_name, equiv_rhs)
    
    def replMap(self):
        '''
        Returns the lambda function/map that would replace this particular inner
        expression within the top-level expression.
        '''
        # build the lambda expression, starting with the lambda parameter and
        # working up the hierarchy.
        top_level_expr = self.exprHierarchy[0]
        cur_sub_expr = self.exprHierarchy[-1]
        
        if isinstance(cur_sub_expr, Composite):
            dummy_vars = top_level_expr.safeDummyVars(len(cur_sub_expr))
            lambda_params = dummy_vars
            if len(self.parameters)==0:
                lambda_body = cur_sub_expr.__class__._make(cur_sub_expr.coreInfo(), cur_sub_expr.getStyles(), dummy_vars)
            else:
                # The replacements should be a function of the parameters encountered
                # between the top-level expression and the inner expression.
                lambda_body = cur_sub_expr.__class__._make(cur_sub_expr.coreInfo(), cur_sub_expr.getStyles(), [Function(dummy_var, self.parameters) for dummy_var in dummy_vars])                
        else:
            lambda_params = [top_level_expr.safeDummyVar()]
            if len(self.parameters)==0:
                lambda_body = lambda_params[0]
            else:
                # The replacements should be a function of the parameters encountered
                # between the top-level expression and the inner expression.
                lambda_body = Function(lambda_params[0], self.parameters)
        for expr, idx in reversed(list(zip(self.exprHierarchy, self.innerExprPath))):
            expr_subs = list(expr.subExprIter())
            lambda_body = expr.__class__._make(expr.coreInfo(), expr.getStyles(), expr_subs[:idx] + [lambda_body] + expr_subs[idx+1:])
        return Lambda(lambda_params, lambda_body)
    
    def _expr_rep(self):
        '''
        Representation as NamedExprs that indicates not only the lambda function
        but the sub-Expressions that may be accessed more deeply.
        '''
        repl_map = self.replMap()
        lambda_params = repl_map.parameters
        cur_sub_expr = self.exprHierarchy[-1]
        if isinstance(cur_sub_expr, Composite):
            sub_exprs = list(cur_sub_expr.subExprIter())
        else:
            sub_exprs = [cur_sub_expr]
        named_expr_dict = [('lambda',repl_map)]
        if len(self.parameters)==0:
            named_expr_dict += [(str(lambda_param), sub_expr) for lambda_param, sub_expr in zip(lambda_params, sub_exprs)]
        else:
            named_expr_dict += [(str(Function(lambda_param, self.parameters)), sub_expr) for lambda_param, sub_expr in zip(lambda_params, sub_exprs)]            
        return NamedExprs(named_expr_dict)
        
    def simplifyOperands(self, assumptions=USE_DEFAULTS):
        from proveit.logic import defaultSimplification
        return defaultSimplification(self, inPlace=True, operandsOnly=True, assumptions=assumptions)                

    def evaluateOperands(self, assumptions=USE_DEFAULTS):
        from proveit.logic import defaultSimplification
        return defaultSimplification(self, inPlace=True, mustEvaluate=True, operandsOnly=True, assumptions=assumptions)                
        
    def _repr_html_(self):
        return self._expr_rep()._repr_html_()

    def __repr__(self):
        return self._expr_rep().__repr__()

# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(Expression, 'simplification', 'simplified', 'simplify')
InnerExpr.register_equivalence_method(Expression, 'evaluation', 'evaluated', 'evaluate')

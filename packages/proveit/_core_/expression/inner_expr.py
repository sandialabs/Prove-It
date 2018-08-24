from .expr import Expression
from .operation import Function
from .lambda_expr import Lambda
from .composite import ExprList, Composite, NamedExprs, compositeExpression

class InnerExpr:
    '''
    Represents an "inner" sub-expression of a particular "master" 
    expression.  The innerExpr method of the Expression class 
    will start an InnerExpr with that particular expression as 
    the master.  This acts as an expression wrapper, 
    starting at the master expression but can "descend" to
    any sub-expression via accessing sub-expression attributes.
    
    For example, let "expr = (a + b + a/d)", and let
    "inner_expr = expr.innterExpr().terms[2].numerator".  Then
    
    1. inner_expr.replMap() will return _x_ -> (a + b + _x_/d),
       replacing the particular innerexpr.
       (note that the second "a" is singled out, distinct from
       the first "a" because the subexpr object tracks the
       sub-expression by "location").
    2. inner_expr.withStyles(somestyle='something') will return an
       expression that is the same as expr but with a style
       change for the second "a".  Works more generally for any
       "with..." method.
    3. inner_expr.expr() will return "a" as an Expression object.
    '''
    
    def __init__(self, masterExpr, innerExprPath=tuple()):
        '''
        Create an InnerExpr with the given master Expression.
        Optionally, subExprPath is a sequence of sub-Expression indices
        starting from the master expression as the root to produce
        a map for replacing the corresponding sub-Expression.  A new
        SubExprRepl is generated appropriately, extending the 
        sub-Expression path, when getting an item or attribute
        that corresponds with an item/attribute of the currently
        mapped sub-Expression.
        '''
        self.innerExprPath = tuple(innerExprPath)
        self.exprHierarchy = [masterExpr]
        # list all of the lambda expression parameters encountered
        # along the way from the master expression to the inner expression.
        self.parameters = []
        expr = self.exprHierarchy[0]
        for idx in self.innerExprPath:
            if isinstance(expr, Lambda) and idx==expr.numSubExpr()-1:
                # while descending into a lambda expression body, we
                # pick up the lambda parameters.
                self.parameters.extend(expr.parameters)
            expr = expr.subExpr(idx)
            self.exprHierarchy.append(expr)
            
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
        master_expr = self.exprHierarchy[0]
        cur_inner_expr = self.exprHierarchy[-1]
        inner_subs = list(cur_inner_expr.subExprIter())
        for i, inner_sub in enumerate(inner_subs):
            # See if any off the sub-expressions
            if inner_sub == attr_expr:
                deeper_inner_expr = InnerExpr(master_expr, self.innerExprPath + (i,))       
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
        For methods of the inner expression that beginn as 'with', generate a method 
        that returns a new version of the master expression with the inner expression
        changed according to its 'with' method.   
        '''
        cur_inner_expr = self.exprHierarchy[-1]
        
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
                return self.exprHierarchy[0] # return the master expression
            return reviseInnerExpr
                
        return getattr(cur_inner_expr, attr) # not a sub-expression, so just return the attribute for the actual Expression object of the sub-expression
        
    def replMap(self):
        '''
        Returns the lambda function/map that would replace this particular inner
        expression within the master expression.
        '''
        # build the lambda expression, starting with the lambda parameter and
        # working up the hierarchy.
        master_expr = self.exprHierarchy[0]
        cur_sub_expr = self.exprHierarchy[-1]
        
        if isinstance(cur_sub_expr, Composite):
            dummy_vars = master_expr.safeDummyVars(len(cur_sub_expr))
            lambda_params = dummy_vars
            if len(self.parameters)==0:
                lambda_body = cur_sub_expr.__class__._make(cur_sub_expr.coreInfo(), cur_sub_expr.getStyles(), dummy_vars)
            else:
                # The replacements should be a function of the parameters encountered
                # between the master expression and the inner expression.
                lambda_body = cur_sub_expr.__class__._make(cur_sub_expr.coreInfo(), cur_sub_expr.getStyles(), [Function(dummy_var, self.parameters) for dummy_var in dummy_vars])                
        else:
            lambda_params = [master_expr.safeDummyVar()]
            if len(self.parameters)==0:
                lambda_body = lambda_params[0]
            else:
                # The replacements should be a function of the parameters encountered
                # between the master expression and the inner expression.
                lambda_body = Function(lambda_params[0], self.parameters)
        for expr, idx in reversed(zip(self.exprHierarchy, self.innerExprPath)):
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
    
    def _repr_html_(self):
        return self._expr_rep()._repr_html_()

    def _repr_(self):
        return self._expr_rep()._repr_()

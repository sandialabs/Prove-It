from proveit import Expression, Lambda, ExpressionList, Composite, NamedExpressions

class SubExprRepl:
    '''
    Conveniently generates lambda map for replacing sub-expressions.  
    Simply create a SubExprRepl with a master Expression and then access 
    sub-Expression attributes/items to obtain a map to the sub-Expression.
    For example, given an Expression `expr = (a + b + a/d)`, do
    `SubExprRepl(expr).operands[2].numerator` to obtain the SubExprRepl
    that produces `_X_ -> (a + b + _X_/d)`.  This approach to generating
    the lambda map avoids ambiguity with respect to multiple
    sub-Expressions that are identical (in our example, the multiple `a`
    references).
    '''
    
    def __init__(self, masterExpr, subExprPath=tuple()):
        '''
        Create an SubExprRepl with the given master Expression.
        Optionally, subExprPath is a sequence of sub-Expression indices
        starting from the master expression as the root to produce
        a map for replacing the corresponding sub-Expression.  A new
        SubExprRepl is generated appropriately, extending the 
        sub-Expression path, when getting an item or attribute
        that corresponds with an item/attribute of the currently
        mapped sub-Expression.
        '''
        self.subExprPath = tuple(subExprPath)
        self.exprHierarchy = [masterExpr]
        expr = self.exprHierarchy[0]
        for idx in self.subExprPath:
            expr = expr.subExpr(idx)
            self.exprHierarchy.append(expr)
            
    def __getitem__(self, key):
        '''
        If the currently mapped sub-Expression of the SubExprRepl
        is a Composite, accessing an item corresponding to an item
        of this Composite will return the SubExprRepl with the extended 
        path to this item.
        '''
        curSubExpr = self.exprHierarchy[-1]
        if isinstance(curSubExpr, ExpressionList):
            # For an ExpressionList, the item key is simply the index of the sub-Expression
            return SubExprRepl(self.exprHierarchy[0], self.subExprPath + (key,))
        elif isinstance(curSubExpr, Composite):
            # For any other Composite (ExpressionTensor or NamedExpressions), the key is the key of the Composite dictionary.
            # The sub-Expressions are in the order that the keys are sorted.
            sortedKeys = sorted(curSubExpr.keys())
            return SubExprRepl(self.exprHierarchy[0], self.subExprPath + [sortedKeys.index(key)])
        raise KeyError("The current sub-Expression is not a Composite.")
        
    def __getattr__(self, name):
        '''
        See if the attribute is accessing a sub-expression.  If so,
        return the SubExprRepl with the extended path to the sub-expression.
        '''
        masterExpr = self.exprHierarchy[0]
        curSubExpr = self.exprHierarchy[-1]
        subSubs = list(curSubExpr.subExprIter())
        
        if name not in curSubExpr.__dict__:
            raise AttributeError("No attribute '%s' in '%s' or '%s'"%(name, self.__class__, curSubExpr.__class__))
        if not isinstance(curSubExpr.__dict__[name], Expression):        
            raise AttributeError("No attribute '%s%' in '%s' and not a sub-Expression of '%s'"%(name, self.__class__, curSubExpr.__class__))
        
        if isinstance(curSubExpr.__dict__[name], Expression):
            # The attribute is addressing an Expression of the current sub-Expression
            # and may be a sub-sub-Expression (or a member of sub-sub-Expression composite);
            # if so, return the SubExprRepl extended to the sub-sub-Expression.
            expr = curSubExpr.__dict__[name]
            for i, subSub in enumerate(subSubs):
                if subSub == expr:
                    # Possibly a match, but we need to make sure it is the right one;
                    # there may be multple sub-expressions that are equivalent, but we
                    # want the one the corresponds with the attribute being addressed.
                    if isinstance(expr, Composite):
                        # deal with a Composite by using multiple dummy variables -- one for each index/key
                        dummyVars = masterExpr.safeDummyVars(len(expr))
                        compositeWithDummyVars = expr.__class__.make(expr.coreInfo(), dummyVars)
                        withDummyVars = curSubExpr.__class__.make(curSubExpr.coreInfo(), subSubs[:i] + [compositeWithDummyVars] + subSubs[i+1:])
                        if withDummyVars.__dict__[name] == compositeWithDummyVars:
                            # Checks out -- this is the right sub-sub-Expression, which is a Composite.
                            return SubExprRepl(self.exprHierarchy[0], self.subExprPath + (i,))                    
                    else:
                        dummyVar = masterExpr.safeDummyVar()
                        withDummyVar = curSubExpr.__class__.make(curSubExpr.coreInfo(), subSubs[:i] + [dummyVar] + subSubs[i+1:])
                        if withDummyVar.__dict__[name] == dummyVars:
                            # Checks out -- this is the right sub-sub-Expression.
                            return SubExprRepl(self.exprHierarchy[0], self.subExprPath + (i,))
                elif isinstance(subSub, ExpressionList):
                    # An ExpressionList sub-Expression.  See if any of the elements are a match.
                    dummyVar = masterExpr.safeDummyVar()
                    for j, subSubSub in enumerate(subSub):
                        if subSubSub == expr:
                            # Again, possibly a match, but we need to make sure
                            listWithDummyVar = subSub[:j] + [dummyVar] + subSub[j+1:]
                            withDummyVar = curSubExpr.__class__.make(curSubExpr.coreInfo(), subSubs[:i] + [listWithDummyVar] + subSubs[i+1:])
                            if withDummyVar.__dict__[name] == dummyVar:
                                return SubExprRepl(self.exprHierarchy[0], self.subExprPath + (i, j))
                elif isinstance(subSub, Composite):
                    # if the Composite isn't a list, then it is a dictionary (ExpressionTensor or NamedExpressions).
                    # See if any of the elements are a match.
                    dummyVar = masterExpr.safeDummyVar()
                    for key, subSubSub in subSub.iteritems():
                        if subSubSub == expr:
                            # Again, possibly a match, but we need to make sure
                            dictWithDummyVar = {k:subSubSub if k==key else v for k,v in subSub.iteritems()}
                            withDummyVar = curSubExpr.__class__.make(curSubExpr.coreInfo(), subSubs[:i] + [dictWithDummyVar] + subSubs[i+1:])
                            if withDummyVar.__dict__[name] == dummyVar:
                                return SubExprRepl(self.exprHierarchy[0], self.subExprPath + (i, j))                            
            raise AttributeError("No attribute '%s' in '%s' and not a sub-Expression of '%s'"%(name, self.__class__, curSubExpr.__class__))
                    
    def lambdaMap(self):
        '''
        Returns the lambda function/map that the SubExprRepl is currently
        producing.
        '''
        # build the lambda expression, starting with the lambda argument and
        # working up the hierarchy.
        masterExpr = self.exprHierarchy[0]
        curSubExpr = self.exprHierarchy[-1]
        if isinstance(curSubExpr, Composite):
            dummyVars = masterExpr.safeDummyVars(len(curSubExpr))
            lambdaArgs = dummyVars
            lambdaExpr = curSubExpr.__class__.make(curSubExpr.coreInfo(), dummyVars)
        else:
            lambdaExpr = masterExpr.safeDummyVar()
            lambdaArgs = [lambdaExpr]
        for expr, idx in reversed(zip(self.exprHierarchy, self.subExprPath)):
            exprSubs = list(expr.subExprIter())
            lambdaExpr = expr.__class__.make(expr.coreInfo(), exprSubs[:idx] + [lambdaExpr] + exprSubs[idx+1:])
        return Lambda(lambdaArgs, lambdaExpr)
    
    def _expr_rep(self):
        '''
        Representation as NamedExpressions that indicates not only the lambda function
        but the sub-Expressions that may be accessed more deeply.
        '''
        lambdaMap = self.lambdaMap()
        lambdaArgs = lambdaMap.arguments
        curSubExpr = self.exprHierarchy[-1]
        if isinstance(curSubExpr, Composite):
            subExprs = list(curSubExpr.subExprIter())
        else:
            subExprs = [curSubExpr]
        namedExprDict = {'lambda':lambdaMap}
        namedExprDict.update({str(lambdaArg):subExpr for lambdaArg, subExpr in zip(lambdaArgs, subExprs)})
        return NamedExpressions(namedExprDict)        
    
    def _repr_png_(self):
        return self._expr_rep()._repr_png_()

    def _repr_(self):
        return self._expr_rep()._repr_()
        
class SubExprException:
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

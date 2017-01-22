from proveit import Lambda

def globalRepl(masterExpr, subExpr):
    '''
    Returns the Lambda map for replacing the given sub-Expression
    everywhere that it occurs in the master Expression.
    '''
    lambdaParam = masterExpr.safeDummyVar()
    return Lambda(lambdaParam, masterExpr.substituted({subExpr:lambdaParam}))

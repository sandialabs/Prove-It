from proveit import Lambda

def globalRepl(masterExpr, subExpr):
    '''
    Returns the Lambda map for replacing the given sub-Expression
    everywhere that it occurs in the master Expression.
    '''
    lambdaArg = masterExpr.safeDummyVar()
    return Lambda(lambdaArg, masterExpr.substituted({subExpr:lambdaArg}))

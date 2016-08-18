from proveit import Lambda

def compose(lambda1, lambda2):
    '''
    Given some x -> f(x) for lambda1 and y -> g(y) for lambda2,
    return x -> f(g(x)).  Also works with multiple arguments:
    x1, x2, ..., xn -> f(x1, x2, ..., xn)  for lambda 1 and  
    y1, y2, ..., yn -> g1(y1, y2, ..., yn), 
    y1, y2, ..., yn -> g2(y1, y2, ..., yn), 
    ...
    y1, y2, ..., yn -> gn(y1, y2, ..., yn) for lambda2 returns
    x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
    '''
    if len(lambda1.arguments) == 1:
        if len(lambda2.arguments) != 1:
            raise TypeError("lambda2 may only take 1 argument if lambda1 takes only 1 argument")
        # g(x)
        relabeledExpr2 = lambda2.expression.relabeled({lambda2.arguments[0]:lambda1.arguments[0]})
        # x -> f(g(x))
        return Lambda(lambda1.arguments[0], lambda1.expression.substituted({lambda1.arguments[0]:relabeledExpr2}))
    else:
        if len(lambda2) != len(lambda1.arguments):
            raise TypeError("Must supply a list of lambda2s with the same length as the number of lambda1 arguments")
        relabeledExpr2s = []
        for lambda2elem in lambda2:
            if len(lambda2elem.arguments) != len(lambda1.arguments):
                raise TypeError("Each lambda2 must have the same number of arguments as lambda1")
            # gi(x1, x2, ..., xn)
            argReplMap = {arg2:arg1 for arg1, arg2 in zip(lambda1.arguments, lambda2elem.arguments)}
            relabeledExpr2s.append(lambda2elem.expression.substituted(argReplMap))
        # x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
        lambda1ExprSubMap = {arg1:relabeledExpr2 for arg1, relabeledExpr2 in zip(lambda1.arguments, relabeledExpr2s)}
        return Lambda(lambda1.arguments, lambda1.expression.substituted(lambda1ExprSubMap))
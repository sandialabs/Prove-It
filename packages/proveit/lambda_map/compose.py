from proveit import Lambda

def compose(lambda1, lambda2):
    '''
    Given some x -> f(x) for lambda1 and y -> g(y) for lambda2,
    return x -> f(g(x)).  Also works with multiple parameters:
    x1, x2, ..., xn -> f(x1, x2, ..., xn)  for lambda 1 and  
    y1, y2, ..., yn -> g1(y1, y2, ..., yn), 
    y1, y2, ..., yn -> g2(y1, y2, ..., yn), 
    ...
    y1, y2, ..., yn -> gn(y1, y2, ..., yn) for lambda2 returns
    x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
    '''
    if len(lambda1.parameters) == 1:
        if len(lambda2.parameters) != 1:
            raise TypeError("lambda2 may only take 1 parameter if lambda1 takes only 1 parameter")
        # g(x)
        relabeledExpr2 = lambda2.expression.relabeled({lambda2.parameters[0]:lambda1.parameters[0]})
        # x -> f(g(x))
        return Lambda(lambda1.parameters[0], lambda1.expression.substituted({lambda1.parameters[0]:relabeledExpr2}))
    else:
        if len(lambda2) != len(lambda1.parameters):
            raise TypeError("Must supply a list of lambda2s with the same length as the number of lambda1 parameters")
        relabeledExpr2s = []
        for lambda2elem in lambda2:
            if len(lambda2elem.parameters) != len(lambda1.parameters):
                raise TypeError("Each lambda2 must have the same number of parameters as lambda1")
            # gi(x1, x2, ..., xn)
            paramReplMap = {param2:param1 for param1, param2 in zip(lambda1.parameters, lambda2elem.parameters)}
            relabeledExpr2s.append(lambda2elem.expression.substituted(paramReplMap))
        # x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
        lambda1ExprSubMap = {param1:relabeledExpr2 for param1, relabeledExpr2 in zip(lambda1.parameters, relabeledExpr2s)}
        return Lambda(lambda1.parameters, lambda1.expression.substituted(lambda1ExprSubMap))
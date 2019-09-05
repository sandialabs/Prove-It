import proveit
from proveit.logic.equality._axioms_ import substitution
from proveit._common_ import a, b, c, d, x, y, z, fx # we'll use these later
from proveit.logic import Not, Equals
from proveit import Lambda
from proveit.number import Add, Frac, Exp

def test():
        substitution.specialize({fx:Not(x), x:a, y:b}, assumptions=[Equals(a, b)])
        expr = Equals(a, Add(b, Frac(c, d), Exp(c, d)))
        gRepl = Lambda.globalRepl(expr, d)
        d_eq_y = Equals(d, y)
        d_eq_y.substitution(gRepl, assumptions=[d_eq_y])
        d_eq_y.substitution(expr, assumptions=[d_eq_y])
        d_eq_y.substitution(expr, assumptions=[d_eq_y]).proof()
        innerExpr = expr.innerExpr()
        innerExpr = innerExpr.rhs
        innerExpr = innerExpr.operands[1]
        innerExpr = innerExpr.denominator
        d_eq_y.substitution(innerExpr, assumptions=[d_eq_y])
        d_eq_y.substitution(expr.innerExpr().rhs.operands[2].exponent, assumptions=[d_eq_y])
        d_eq_y.subRightSideInto(gRepl, assumptions=[d_eq_y,expr])
        d_eq_y.subRightSideInto(expr, assumptions=[d_eq_y,expr])
        y_eq_d = Equals(y, d)
        y_eq_d.subLeftSideInto(gRepl, assumptions=[y_eq_d,expr])
        y_eq_d.subLeftSideInto(expr, assumptions=[y_eq_d,expr])
        y_eq_d.subLeftSideInto(expr, assumptions=[y_eq_d,expr]).proof()
        
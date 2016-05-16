from expr import Expression

class ExpressionTree:
    def __init__(self, expr):
        self.expr = expr
    
    def latex(self):
        from composite.named_exprs import NamedExpressions
        from operation import Operation
        from lambda_expr import Lambda
        visitedExpressions = set()
        nextExpressions = [self.expr]
        enumeratedExpressions = []
        while len(nextExpressions) > 0:
            nextExpr = nextExpressions.pop(0)
            if nextExpr in visitedExpressions: continue # already showed that one
            visitedExpressions.add(nextExpr)
            enumeratedExpressions.append(nextExpr)
            nextExpressions += nextExpr._subExpressions
        exprNumMap = {expr:k for k, expr in enumerate(enumeratedExpressions)}
        outStr = r'\begin{tabular}{rl|l|l}'
        outStr += r' & \textbf{expression} & \textbf{core type} & \textbf{sub-expressions} \\'
        for k, expr in enumerate(enumeratedExpressions):
            outStr += r'\hline'
            outStr += str(k) + '. & ' + repr(expr) + ' & ' + expr._coreInfo[0] + ' & '
            if isinstance(expr, NamedExpressions):
                outStr += r'$\begin{array}{l}'
                for key in sorted(expr.keys()):
                    outStr += r'\rm{' + key.replace('_', r'\_') + '}: ' + str(exprNumMap[expr[key]]) + r'\\'
                outStr += r'\end{array}$ \\'
            elif isinstance(expr, Operation):
                outStr += r'$\begin{array}{l}'
                outStr += r'\rm{operator}: ' + str(exprNumMap[expr.operator]) + r' \\'
                outStr += r'\rm{operands}: ' + str(exprNumMap[expr.operands]) + r' \\'
                outStr += r'\end{array}$ \\'
            elif isinstance(expr, Lambda):
                outStr += r'$\begin{array}{l}'
                outStr += r'\rm{arguments}: ' + str(exprNumMap[expr.arguments]) + r' \\'
                outStr += r'\rm{expression}: ' + str(exprNumMap[expr.expression]) + r' \\'
                outStr += r'\end{array}$ \\'
            else:
                outStr += ', '.join(str(exprNumMap[subExpr]) for subExpr in expr._subExpressions) + r'\\'
        outStr += r'\hline'
        outStr += r'\end{tabular}'
        return outStr

    def _repr_png_(self):
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        if not hasattr(self,'png') or self.png is None:
            LaTeXTool.clear_instance()
            lt = LaTeXTool.instance()
            lt.use_breqn = False
            self._config_latex_tool(lt)
            self.png = latex_to_png(self.latex(), backend='dvipng', wrap=True)
        return self.png
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
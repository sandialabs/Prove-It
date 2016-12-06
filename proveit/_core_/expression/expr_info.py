'''
ExpressionInfo is an Expression wrapper for displaying the information
of an Expression as a directed acyclic graph.  It is obtained by calling
the exprInfo() method of an Expression object.
'''

import re
from proveit._core_.storage import storage, tex_escape

class ExpressionInfo:
    def __init__(self, expr, show_details):
        '''
        Create an ExpressionInfo for the given expr object.  If show_details
        is True, extra detailed information will be provided.
        '''
        self.expr = expr
        self.show_details = show_details
    
    def _getEnumeratedExpressions(self):
        visitedExpressions = set()
        nextExpressions = [self.expr]
        enumeratedExpressions = []
        while len(nextExpressions) > 0:
            nextExpr = nextExpressions.pop(0)
            if nextExpr in visitedExpressions: continue # already showed that one
            visitedExpressions.add(nextExpr)
            enumeratedExpressions.append(nextExpr)
            nextExpressions += nextExpr._subExpressions
        return enumeratedExpressions

    def string(self):
        from composite.named_exprs import NamedExpressions
        from operation import Operation
        from lambda_expr import Lambda
        from label import Label, Literal
        enumeratedExpressions = self._getEnumeratedExpressions()
        exprNumMap = {expr:k for k, expr in enumerate(enumeratedExpressions)}
        outStr = ''
        for k, expr in enumerate(enumeratedExpressions):
            outStr += str(k) + '. ' + str(expr) + '\n'
            indent = ' ' * (len(str(k)) + 2)
            outStr += indent + 'core type: ' + expr._coreInfo[0] + '\n'
            if self.show_details:
                if isinstance(expr, Label):
                    outStr += indent + 'latexFormat: ' + expr.latexFormat + '\n'
                if isinstance(expr, Literal):
                    outStr += indent + 'context: ' + expr.context + '\n'
                outStr += indent + 'class: ' + str(expr.__class__) + '\n'
            if isinstance(expr, NamedExpressions):
                for key in sorted(expr.keys()):
                    outStr += indent + key + ': ' + str(exprNumMap[expr[key]]) + '\n'
            elif isinstance(expr, Operation):
                outStr += indent + r'operator: ' + str(exprNumMap[expr.operator]) + '\n'
                outStr += indent + r'operands: ' + str(exprNumMap[expr.operands]) + '\n'
            elif isinstance(expr, Lambda):
                outStr += indent + r'arguments: ' + str(exprNumMap[expr.arguments]) + '\n'
                outStr += indent + r'expression: ' + str(exprNumMap[expr.expression]) + '\n'
            else:
                outStr += indent + r'sub-expressions: ' + ', '.join(str(exprNumMap[subExpr]) for subExpr in expr._subExpressions) + '\n'
        return outStr
    
    def __str__(self):
        return self.string()
    
    def latex(self):
        from composite.named_exprs import NamedExpressions
        from operation import Operation
        from lambda_expr import Lambda
        from label import Label, Literal
        enumeratedExpressions = self._getEnumeratedExpressions()
        exprNumMap = {expr:k for k, expr in enumerate(enumeratedExpressions)}
        outStr = r'\begin{tabular}{rl|l|l}' + '\n'
        outStr += r' & \textbf{expression} & \textbf{core type} & \textbf{sub-expressions} \\' + '\n'
        for k, expr in enumerate(enumeratedExpressions):
            outStr += r'\hline' + '\n'
            outStr += str(k) + '. & $' + expr.latex() + '$ & ' + expr._coreInfo[0] + ' & ' + '\n'
            if isinstance(expr, NamedExpressions):
                outStr += r'$\begin{array}{l}' + '\n'
                for key in sorted(expr.keys()):
                    outStr += r'\rm{' + key.replace('_', r'\_') + '}: ' + str(exprNumMap[expr[key]]) + r'\\'  + '\n'
                outStr += r'\end{array}$ \\' + '\n'
            elif isinstance(expr, Operation):
                outStr += r'$\begin{array}{l}' + '\n'
                outStr += r'\rm{operator}: ' + str(exprNumMap[expr.operator]) + r' \\' + '\n'
                outStr += r'\rm{operands}: ' + str(exprNumMap[expr.operands]) + r' \\' + '\n'
                outStr += r'\end{array}$ \\' + '\n'
            elif isinstance(expr, Lambda):
                outStr += r'$\begin{array}{l}' + '\n'
                outStr += r'\rm{arguments}: ' + str(exprNumMap[expr.arguments]) + r' \\' + '\n'
                outStr += r'\rm{expression}: ' + str(exprNumMap[expr.expression]) + r' \\' + '\n'
                outStr += r'\end{array}$ \\' + '\n'
            else:
                outStr += ', '.join(str(exprNumMap[subExpr]) for subExpr in expr._subExpressions) + r'\\' + '\n'
            if self.show_details:
                if isinstance(expr, Label):
                    outStr += r' & \texttt{\textless stringFormat ' + tex_escape(expr.stringFormat) + r'\textgreater } & & \\' + '\n'
                if isinstance(expr, Literal):
                    outStr += r' & \texttt{\textless context ' + tex_escape(expr.context) + r'\textgreater } & & \\' + '\n'
                outStr += r' & \texttt{' + tex_escape(repr(expr.__class__)) + r'} & & \\' + '\n'
        outStr += r'\hline' + '\n'
        outStr += r'\end{tabular}' + '\n'
        return outStr

    def _repr_png_(self):
        if (not hasattr(self,'png') or self.png is None):
            distinction = 'details' if self.show_details else 'info'
            self.png = storage._retrieve_png(self.expr, self.latex(), self._config_latex_tool, distinction=distinction)
        return self.png # previous stored or generated
        
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
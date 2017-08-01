'''
ExpressionInfo is an Expression wrapper for displaying the information
of an Expression as a directed acyclic graph.  It is obtained by calling
the exprInfo() method of an Expression object.
'''

import re

class ExpressionInfo:
    def __init__(self, expr, show_details):
        '''
        Create an ExpressionInfo for the given expr object.  If show_details
        is True, extra detailed information will be provided.
        '''
        self.expr = expr
        self.show_details = show_details

    def _getEnumeratedExpressions(self):
        '''
        Returns a list of Expression objects that includes self and
        all of its direct and indirect sub-Expressions.  Duplicates
        will not be included, but they will be presented in an
        order which makes it clear that the dependencies are
        acyclic by making sure sub-Expressions always come later.
        Overriding the default parameter values can change the top-level
        expression or the function used to obtain sub-expressions.
        '''
        from proveit._core_._dependency_graph import orderedDependencyNodes
        return orderedDependencyNodes(self.expr, lambda expr : expr._subExpressions)

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
                outStr += indent + r'parameters: ' + ', '.join(str(exprNumMap[parameter]) for parameter in expr.parameters) + '\n'
                outStr += indent + r'body: ' + str(exprNumMap[expr.body]) + '\n'
            else:
                outStr += indent + r'sub-expressions: ' + ', '.join(str(exprNumMap[subExpr]) for subExpr in expr._subExpressions) + '\n'
        return outStr
    
    def __str__(self):
        return self.string()
    
    def _repr_html_(self):
        from composite.named_exprs import NamedExpressions
        from operation import Operation
        from lambda_expr import Lambda
        
        # get the enumerated sub-expressions; parents come before children.
        enumerated_expressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumerated_expressions)}
        
        # map each sub-Expression to an appropriate Context
        expr_context_map = dict() 
        for expr in enumerated_expressions:
            if hasattr(expr, 'context') and expr.context is not None:
                expr_context_map[expr] = expr.context
            if expr in expr_context_map:
                for sub_expr in expr.subExprIter(): # propagate the context to its sub-expressions
                    expr_context_map[sub_expr] = expr_context_map[expr]
        
        # generate the html as a table with the enumerated expressions on the rows.
        html = '<table><tr><th colspan=2>expression</th><th>core type</th><th>sub-expressions</th></tr>\n'
        for k, expr in enumerate(enumerated_expressions):
            sub_expressions = ''
            if isinstance(expr, NamedExpressions):
                for key in sorted(expr.keys()):
                    sub_expressions += '%s: %d<br>'%(key, expr_num_map[expr[key]])
            elif isinstance(expr, Operation):
                sub_expressions = 'operator: %d<br>'%(expr_num_map[expr.operator])
                sub_expressions += 'operands: %d<br>'%(expr_num_map[expr.operands])
            elif isinstance(expr, Lambda):
                sub_expressions = 'parameters: %s<br>'%(', '.join(str(expr_num_map[parameter]) for parameter in expr.parameters))
                sub_expressions += 'body: %d<br>'%(expr_num_map[expr.body])
            else:
                sub_expressions = ', '.join(str(expr_num_map[subExpr]) for subExpr in expr._subExpressions)
            context = expr_context_map[expr] if expr in expr_context_map else None
            html += '<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td>\n'%(k, expr._repr_html_(context=context), expr._coreInfo[0], sub_expressions)
        html += '</table>\n'
        return html
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
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
        from .composite import NamedExprs, Indexed, Iter
        from .operation import Operation
        from .lambda_expr import Lambda
        from .label import Label, Literal
        enumeratedExpressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumeratedExpressions)}
        outStr = ''
        for k, expr in enumerate(enumeratedExpressions):
            outStr += str(k) + '. ' + str(expr) + '\n'
            indent = ' ' * (len(str(k)) + 2)
            outStr += indent + 'core type: ' + expr._coreInfo[0] + '\n'
            if self.show_details:
                if isinstance(expr, Label):
                    outStr += indent + 'latexFormat: ' + expr.latexFormat + '\n'
                if len(expr._coreInfo)>4:
                    outStr += indent + 'extraCoreInfo: ' + str(expr._coreInfo[4:]) + '\n'                    
                if isinstance(expr, Literal):
                    outStr += indent + 'context: ' + expr.context.name + '\n'
                outStr += indent + 'class: ' + str(expr.__class__) + '\n'
            if isinstance(expr, NamedExprs):
                for key in expr.keys():
                    outStr += indent + key + ': ' + str(expr_num_map[expr[key]]) + '\n'
            elif isinstance(expr, Operation):
                if hasattr(expr, 'operator'): # has a single operator
                    outStr += indent + r'operator: ' + str(expr_num_map[expr.operator]) + '\n'
                else: # has multiple operators
                    outStr += indent + r'operators: ' + str(expr_num_map[expr.operators]) + '\n'
                if hasattr(expr, 'operand'): # has a single operand
                    outStr += indent + r'operand: ' + str(expr_num_map[expr.operand]) + '\n'
                else: # has multiple operands
                    outStr += indent + r'operands: ' + str(expr_num_map[expr.operands]) + '\n'                    
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter'): # has a single parameter
                    outStr += indent + 'parameter: %s\n'%(expr_num_map[expr.parameter])
                else:        
                    outStr += indent + r'parameters: ' + ', '.join(str(expr_num_map[parameter]) for parameter in expr.parameters) + '\n'
                outStr += indent + r'body: ' + str(expr_num_map[expr.body]) + '\n'
            elif isinstance(expr, Indexed):
                outStr += indent + 'var: %d\n'%(expr_num_map[expr.var])
                if hasattr(expr, 'index'):
                    outStr += indent +'index: %d\n'%(expr_num_map[expr.index])
                else:
                    outStr += indent +'indices: %d\n'%(expr_num_map[expr.indices])
                outStr += indent +'base: "%d"\n'%expr.base        
            elif isinstance(expr, Iter):
                outStr += indent + 'lambda_map: %d\n'%(expr_num_map[expr.lambda_map])
                if hasattr(expr, 'start_index'): # single index
                    outStr += indent + 'start_index: %d\n'%(expr_num_map[expr.start_index])
                else: # multiple indices
                    outStr += indent + 'start_indices: %d\n'%(expr_num_map[expr.start_indices])
                if hasattr(expr, 'end_index'): # single index
                    outStr += indent + 'end_index: %d\n'%(expr_num_map[expr.end_index])
                else: # multiple indices
                    outStr += indent + 'end_indices: %d\n'%(expr_num_map[expr.end_indices])
            else:
                outStr += indent + r'sub-expressions: ' + ', '.join(str(expr_num_map[subExpr]) for subExpr in expr._subExpressions) + '\n'
        return outStr
    
    def __str__(self):
        return self.string()
    
    def _repr_html_(self):
        from .composite import NamedExprs, Indexed, Iter
        from .operation import Operation
        from .lambda_expr import Lambda
        from .label import Literal
        from .expr import Expression
        
        # get the enumerated sub-expressions; parents come before children.
        enumerated_expressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumerated_expressions)}
        
        # map each sub-Expression to an appropriate Context
        expr_context_map = dict() 
        for expr in enumerated_expressions:
            if expr in Expression.contexts:
                expr_context_map[expr] = Expression.contexts[expr]
            if expr in expr_context_map:
                for sub_expr in expr.subExprIter(): # propagate the context to its sub-expressions
                    expr_context_map[sub_expr] = expr_context_map[expr]
        
        # generate the html as a table with the enumerated expressions on the rows.
        html = '<table><tr><th>&nbsp;</th><th>core type</th><th>sub-expressions</th><th>expression</th></tr>\n'
        for k, expr in enumerate(enumerated_expressions):
            sub_expressions = ''
            if isinstance(expr, NamedExprs):
                for key in expr.keys():
                    sub_expressions += '%s: %d<br>'%(key, expr_num_map[expr[key]])
            elif isinstance(expr, Operation):
                if hasattr(expr, 'operator'): # has a single operator
                    sub_expressions = 'operator:&nbsp;%d<br>'%(expr_num_map[expr.operator])
                else: # has multiple operators
                    sub_expressions = 'operators:&nbsp;%d<br>'%(expr_num_map[expr.operators])                    
                if hasattr(expr, 'operand'): # has a single operand
                    sub_expressions += 'operand:&nbsp;%d<br>'%(expr_num_map[expr.operand])
                else: # has multiple operands
                    sub_expressions += 'operands:&nbsp;%d<br>'%(expr_num_map[expr.operands])
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter'): # has a single parameter
                    sub_expressions = 'parameter:&nbsp;%s<br>'%(expr_num_map[expr.parameter])
                else:                        
                    sub_expressions = 'parameters:&nbsp;%s<br>'%(', '.join(str(expr_num_map[parameter]) for parameter in expr.parameters))
                sub_expressions += 'body:&nbsp;%d<br>'%(expr_num_map[expr.body])
            elif isinstance(expr, Indexed):
                sub_expressions += 'var:&nbsp;%d<br>'%(expr_num_map[expr.var])
                if hasattr(expr, 'index'):
                    sub_expressions += 'index:&nbsp;%d<br>'%(expr_num_map[expr.index])
                else:
                    sub_expressions += 'indices:&nbsp;%d<br>'%(expr_num_map[expr.indices])
                sub_expressions += 'base:&nbsp;"%d"<br>'%expr.base
            elif isinstance(expr, Iter):
                sub_expressions += 'lambda_map:&nbsp;%d<br>'%(expr_num_map[expr.lambda_map])
                if hasattr(expr, 'start_index'): # single index
                    sub_expressions += 'start_index:&nbsp;%d<br>'%(expr_num_map[expr.start_index])
                else: # multiple indices
                    sub_expressions += 'start_indices:&nbsp;%d<br>'%(expr_num_map[expr.start_indices])
                if hasattr(expr, 'end_index'): # single index
                    sub_expressions += 'end_index:&nbsp;%d<br>'%(expr_num_map[expr.end_index])
                else: # multiple indices
                    sub_expressions += 'end_indices:&nbsp;%d<br>'%(expr_num_map[expr.end_indices])
            elif isinstance(expr, Literal) and self.show_details:
                sub_expressions += "<strong>'Literal' details</strong><br>"
                sub_expressions += 'context:&nbsp;"%s"<br>'% expr.context.name 
                if len(expr._coreInfo)>4:                
                    sub_expressions += 'extraCoreInfo:&nbsp;"%s"<br>'%str(expr._coreInfo[4:])    
            else:
                sub_expressions = ', '.join(str(expr_num_map[subExpr]) for subExpr in expr._subExpressions)
            context = expr_context_map[expr] if expr in expr_context_map else None
            html += '<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td>\n'%(k, expr._coreInfo[0], sub_expressions, expr._repr_html_(context=context))
        html += '</table>\n'
        return html
    
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
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

    def __repr__(self):
        from .composite import NamedExprs, Iter
        from .operation import Operation, IndexedVar
        from .lambda_expr import Lambda
        from .label import Label, Literal
        from .conditional import Conditional
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
                for key in list(expr.keys()):
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
            elif isinstance(expr, Conditional):
                if len(expr.conditions) == 1:
                    outStr += indent + r'value: ' + str(expr_num_map[expr.value]) + '\n'
                    outStr += indent + r'condition: ' + str(expr_num_map[expr.condition]) + '\n'
                else:
                    outStr += indent + r'values: ' + str(expr_num_map[expr.values]) + '\n'
                    outStr += indent + r'conditions: ' + str(expr_num_map[expr.conditions]) + '\n'                    
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter'): # has a single parameter
                    outStr += indent + 'parameter: %s\n'%(expr_num_map[expr.parameter])
                else:        
                    outStr += indent + r'parameters: %s\n'%(expr_num_map[expr.parameters])
                outStr += indent + r'body: ' + str(expr_num_map[expr.body]) + '\n'
            elif isinstance(expr, IndexedVar):
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
        return repr(self)
    
    def _repr_html_(self):
        from .composite import ExprTuple, ExprArray, NamedExprs, Iter
        from .operation import Operation, IndexedVar
        from .conditional import Conditional
        from .lambda_expr import Lambda
        from .label import Variable, Literal
        from .expr import Expression
        
        # get the enumerated sub-expressions; parents come before children.
        enumerated_expressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumerated_expressions)}
        
        # map each sub-Expression to an appropriate Context
        expr_context_map = {expr : Expression.contexts.get(expr._style_id, None) for expr in enumerated_expressions}
        
        # generate the html as a table with the enumerated expressions on the rows.
        html = '<table><tr><th>&nbsp;</th><th>core type</th><th>sub-expressions</th><th>expression</th></tr>\n'
        for k, expr in enumerate(enumerated_expressions):
            sub_expressions = ''
            if isinstance(expr, NamedExprs):
                for key in list(expr.keys()):
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
            elif isinstance(expr, Conditional):
                if len(expr.conditions) == 1:
                    sub_expressions = 'value:&nbsp;%s<br>'%expr_num_map[expr.value]
                    sub_expressions += 'condition:&nbsp;%s<br>'%expr_num_map[expr.condition]
                else:
                    sub_expressions = 'values:&nbsp;%s<br>'%expr_num_map[expr.values]
                    sub_expressions += 'conditions:&nbsp;%s<br>'%expr_num_map[expr.conditions]
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter'): # has a single parameter
                    sub_expressions = 'parameter:&nbsp;%s<br>'%(expr_num_map[expr.parameter])
                else:                        
                    sub_expressions = 'parameters:&nbsp;%s<br>'%(expr_num_map[expr.parameters])
                sub_expressions += 'body:&nbsp;%d<br>'%(expr_num_map[expr.body])
            elif isinstance(expr, IndexedVar):
                sub_expressions += 'var:&nbsp;%d<br>'%(expr_num_map[expr.var])
                if hasattr(expr, 'index'):
                    sub_expressions += 'index:&nbsp;%d<br>'%(expr_num_map[expr.index])
                else:
                    sub_expressions += 'indices:&nbsp;%d<br>'%(expr_num_map[expr.indices])
                sub_expressions += 'base:&nbsp;"%d"<br>'%expr.base
            elif isinstance(expr, Iter):
                sub_expressions += 'lambda_map:&nbsp;%d<br>'%(expr_num_map[expr.lambda_map])
                '''
                if hasattr(expr, 'start_index'): # single index
                    sub_expressions += 'start_index:&nbsp;%d<br>'%(expr_num_map[expr.start_index])
                else: # multiple indices
                    sub_expressions += 'start_indices:&nbsp;%d<br>'%(expr_num_map[expr.start_indices])
                if hasattr(expr, 'end_index'): # single index
                    sub_expressions += 'end_index:&nbsp;%d<br>'%(expr_num_map[expr.end_index])
                else: # multiple indices
                    sub_expressions += 'end_indices:&nbsp;%d<br>'%(expr_num_map[expr.end_indices])
                '''
            else:
                sub_expressions = ', '.join(str(expr_num_map[subExpr]) for subExpr in expr._subExpressions)
            context = expr_context_map[expr]
            html += '<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td></tr>\n'%(k, expr._coreInfo[0], sub_expressions, expr._repr_html_(context=context))
            if self.show_details and expr.__class__ not in (Variable, Literal, Operation, Lambda, IndexedVar, NamedExprs, ExprTuple, ExprArray, Iter):
                # not a core expression so show the actual class when showing the details
                html += '<tr><td colspan=4 style="text-align:left"><strong>class:</strong> %s</td></tr>\n'%expr._class_path()
            if self.show_details and isinstance(expr, Literal):
                html += '<tr><td colspan=4 style="text-align:left"><strong>context:</strong> %s</td></tr>\n'%expr.context.name
                if len(expr._coreInfo)>4:
                    html += '<tr><td colspan=4 style="text-align:left"><strong>extraCoreInfo:</strong> %s</td></tr>\n'%str(expr._coreInfo[4:])
        html += '</table>\n'
        return html
                
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
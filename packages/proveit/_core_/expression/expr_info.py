'''
ExpressionInfo is an Expression wrapper for displaying the information
of an Expression as a directed acyclic graph.  It is obtained by calling
the expr_info() method of an Expression object.
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
        from proveit._core_._dependency_graph import ordered_dependency_nodes
        return ordered_dependency_nodes(self.expr, lambda expr : expr._sub_expressions)

    def __repr__(self):
        from .composite import NamedExprs, ExprRange
        from .operation import Operation, IndexedVar
        from .lambda_expr import Lambda
        from .label import Label, Literal
        from .conditional import Conditional
        enumerated_expressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumerated_expressions)}
        out_str = ''
        for k, expr in enumerate(enumerated_expressions):
            out_str += str(k) + '. ' + str(expr) + '\n'
            indent = ' ' * (len(str(k)) + 2)
            out_str += indent + 'core type: ' + expr._core_info[0] + '\n'
            if self.show_details:
                if isinstance(expr, Label):
                    out_str += indent + 'latex_format: ' + expr.latex_format + '\n'
                if len(expr._core_info)>4:
                    out_str += indent + 'extra_core_info: ' + str(expr._core_info[4:]) + '\n'                    
                if isinstance(expr, Literal):
                    out_str += indent + 'theory: ' + expr.theory.name + '\n'
                out_str += indent + 'class: ' + str(expr.__class__) + '\n'
            if isinstance(expr, NamedExprs):
                for key in list(expr.keys()):
                    out_str += indent + key + ': ' + str(expr_num_map[expr[key]]) + '\n'
            elif isinstance(expr, IndexedVar):
                out_str +=  r'variable: ' + str(expr_num_map[expr.var]) + '\n'
                if hasattr(expr, 'index'):
                    out_str +=  r'index: ' + str(expr_num_map[expr.index])   + '\n'        
                else:
                    out_str +=  r'indices: ' + str(expr_num_map[expr.indices])   + '\n'                            
            elif isinstance(expr, Operation):
                if hasattr(expr, 'operator'): # has a single operator
                    out_str += indent + r'operator: ' + str(expr_num_map[expr.operator]) + '\n'
                else: # has multiple operators
                    out_str += indent + r'operators: ' + str(expr_num_map[expr.operators]) + '\n'
                if hasattr(expr, 'operand'): # has a single operand
                    out_str += indent + r'operand: ' + str(expr_num_map[expr.operand]) + '\n'
                else: # has multiple operands
                    out_str += indent + r'operands: ' + str(expr_num_map[expr.operands]) + '\n'                    
            elif isinstance(expr, Conditional):
                out_str += indent + r'value: ' + str(expr_num_map[expr.value]) + '\n'
                out_str += indent + r'condition: ' + str(expr_num_map[expr.condition]) + '\n'
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter'): # has a single parameter
                    out_str += indent + 'parameter: %s\n'%(expr_num_map[expr.parameter])
                else:        
                    out_str += indent + r'parameters: %s\n'%(expr_num_map[expr.parameters])
                out_str += indent + r'body: ' + str(expr_num_map[expr.body]) + '\n'
            elif isinstance(expr, ExprRange):
                out_str += indent + 'lambda_map: %d\n'%(expr_num_map[expr.lambda_map])
                out_str += indent + 'start_index: %d\n'%(expr_num_map[expr.start_index])
                out_str += indent + 'end_index: %d\n'%(expr_num_map[expr.end_index])
            else:
                out_str += indent + r'sub-expressions: ' + ', '.join(str(expr_num_map[sub_expr]) for sub_expr in expr._sub_expressions) + '\n'
        return out_str
    
    def __str__(self):
        return repr(self)
    
    def _repr_html_(self):
        from .composite import ExprTuple, ExprArray, NamedExprs, ExprRange
        from .operation import Operation, IndexedVar
        from .conditional import Conditional
        from .lambda_expr import Lambda
        from .label import Variable, Literal
        
        # get the enumerated sub-expressions; parents come before children.
        enumerated_expressions = self._getEnumeratedExpressions()
        expr_num_map = {expr:k for k, expr in enumerate(enumerated_expressions)}
        
        # generate the html as a table with the enumerated expressions on the rows.
        html = '<table><tr><th>&nbsp;</th><th>core type</th><th>sub-expressions</th><th>expression</th></tr>\n'
        for k, expr in enumerate(enumerated_expressions):
            sub_expressions = ''
            if isinstance(expr, NamedExprs):
                for key in list(expr.keys()):
                    sub_expressions += '%s: %d<br>'%(key, expr_num_map[expr[key]])
            elif isinstance(expr, IndexedVar):
                sub_expressions = 'variable:&nbsp;%d<br>'%(expr_num_map[expr.var])
                if hasattr(expr, 'index'):
                    sub_expressions += 'index:&nbsp;%d<br>'%(expr_num_map[expr.index])
                else:
                    sub_expressions += 'indices:&nbsp;%d<br>'%(expr_num_map[expr.indices])                    
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
                sub_expressions = 'value:&nbsp;%s<br>'%expr_num_map[expr.value]
                sub_expressions += 'condition:&nbsp;%s<br>'%expr_num_map[expr.condition]
            elif isinstance(expr, Lambda):
                if hasattr(expr, 'parameter') and not isinstance(expr.parameter, ExprRange): # has a single parameter
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
            elif isinstance(expr, ExprRange):
                sub_expressions += 'lambda_map:&nbsp;%d<br>'%(expr_num_map[expr.lambda_map])
                sub_expressions += 'start_index:&nbsp;%d<br>'%(expr_num_map[expr.start_index])
                sub_expressions += 'end_index:&nbsp;%d<br>'%(expr_num_map[expr.end_index])
            else:
                sub_expressions = ', '.join(str(expr_num_map[sub_expr]) for sub_expr in expr._sub_expressions)
            html += '<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td></tr>\n'%(k, expr._core_info[0], sub_expressions, expr._repr_html_())
            if self.show_details and expr.__class__ not in \
                    (Variable, Literal, Operation, Lambda, IndexedVar, 
                     NamedExprs, ExprTuple, ExprArray, ExprRange):
                # not a core expression so show the actual class when showing the details
                html += '<tr><td colspan=4 style="text-align:left"><strong>class:</strong> %s</td></tr>\n'%expr._class_path()
            if self.show_details and isinstance(expr, Literal):
                html += '<tr><td colspan=4 style="text-align:left"><strong>theory:</strong> %s</td></tr>\n'%expr.theory.name
                if len(expr._core_info)>4:
                    html += '<tr><td colspan=4 style="text-align:left"><strong>extra_core_info:</strong> %s</td></tr>\n'%str(expr._core_info[4:])
        html += '</table>\n'
        return html
                
    def _config_latex_tool(self, lt):
        '''
        Configure the LaTeXTool from IPython.lib.latextools as required by all
        sub-expressions.
        '''
        self.expr._config_latex_tool(lt)
                
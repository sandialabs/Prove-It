
class StyleOptions:
    '''
    An Object for displaying the valid style options of an Expression.
    See the 'style_options' and with_styles' methods of the Expression class.
    '''
    
    def __init__(self, expr):
        self.expr = expr
        self.options = []
    
    def add_option(self, name, description):
        self.options.append((name, description))
    
    def __repr__(self):
        if len(self.options)==0:
            return 'no style options'
        s = ''
        s += 'name\tdescription\tcurrent value'
        for name, description in self.options:
            s += '\t'.join((name, description, self.expr.get_style(name))) + '\n'
        return s

    def _repr_html_(self):
        if len(self.options)==0:
            return 'no style options'
        s = '<table>\n'
        s += '<tr><th>name</th><th>description</th><th>current value</th></tr>'
        for name, description in self.options:
            s += '<tr>' + ''.join('<td>' + x + '</td>' for x in (name, description, self.expr.get_style(name))) + '</tr>\n'
        s += '</table>\n'
        return s

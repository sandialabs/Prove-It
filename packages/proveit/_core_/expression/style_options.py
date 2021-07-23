class StyleOptions:
    '''
    An Object for displaying the valid style options of an Expression.
    See the 'style_options' and with_styles' methods of the Expression class.
    '''

    def __init__(self, expr):
        self.expr = expr
        self.options = []

    def add_option(self, name, description, default, related_methods):
        '''
        Add a Style option with the given name, description,
        default value, and related methods.  These may be specific
        to the expression and not just the expression type, though
        typically only the 'default' is specific to the expression.
        '''
        self.options.append((name, description, default, related_methods))
    
    def option_names(self):
        '''
        Return the list of active style option names.
        '''
        return [option[0] for option in self.options]

    def standardized_styles(self, styles, ignore_inapplicable_styles=False):
        '''
        Create a proper styles dictionary using defaults
        as appropriate and checking to make sure that unknown
        styles aren't used.
        '''
        styles = dict(styles)
        known_style_names = set()
        for name, _, default, _ in self.options:
            if name in styles:
                known_style_names.add(name)
            elif default is not None:
                # Use the default of the StyleOptions.
                styles[name] = default
                known_style_names.add(name)
        if len(styles) > len(known_style_names):
            for style_name in list(styles.keys()):                    
                if style_name not in known_style_names:
                    if ignore_inapplicable_styles:
                        styles.pop(style_name)
                    else:
                        raise StyleError(
                                "%s is not a known style option for this %s "
                                "expression with the following "
                                "sub-expressions: %s"%
                                (style_name, self.expr.__class__,
                                 self.expr._sub_expressions))
        return styles
    
    def canonical_styles(self):
        '''
        Return the styles that should be used for canonical
        expressions by choosing the defaults of the options.
        '''
        return {name:default for name, _, default, _ in self.options
                if default is not None}

    def __repr__(self):
        if len(self.options) == 0:
            return 'no style options'
        s = ''
        for name, description, default, related_methods in self.options:            
            s += 'style name: %s\n'%name
            s += 'description: %s\n'%description
            s += 'default: %s\n'%default
            s += 'current value: %s\n'%self.expr.get_style(name, 'None/False')
            s += 'related methods: %s\n'%str(related_methods)
        return s

    def _repr_html_(self):
        if len(self.options) == 0:
            return 'no style options'
        s = '<table>\n'
        s += '<tr><th>name</th><th>description</th><th>default</th><th>current value</th><th>related methods</th></tr>'
        for name, description, default, related_methods in self.options:
            related_methods_str = ('' if len(related_methods) == 0 
                                   else str(related_methods))
            s += '<tr>'
            s += ''.join('<td>%s</td>'%x for x in (
                    name, description, default, 
                    self.expr.get_style(name, 'None/False'),
                    related_methods_str)) 
            s += '</tr>\n'
        s += '</table>\n'
        return s

class StyleError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message

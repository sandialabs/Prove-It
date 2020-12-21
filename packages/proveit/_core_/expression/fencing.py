def maybe_fenced_string(inner_str, **kwargs):
    '''
    Return inner_str, wrapped in parentheses iff kwargs['fence']==True.
    '''
    if 'fence' in kwargs and kwargs['fence']==True:
        return '(' + inner_str + ')'
    return inner_str

def maybe_fenced_latex(inner_latex, **kwargs):
    '''
    Return inner_latex, wrapped in parentheses iff kwargs['fence']==True.
    '''
    if 'fence' in kwargs and kwargs['fence']==True:
        return r'\left(' + inner_latex + r'\right)'
    return inner_latex

def maybe_fenced(format_type, inner_formatted, **kwargs):
    '''
    Return the inner_formatted string/latex iff kwargs['fence']=True.  If format_type=='string'
    use normal string formatting.  If format_type=='latex', use latex formatting.
    '''
    if format_type == 'string':
        return maybe_fenced_string(inner_formatted, **kwargs)
    elif format_type == 'latex':
        return maybe_fenced_latex(inner_formatted, **kwargs)

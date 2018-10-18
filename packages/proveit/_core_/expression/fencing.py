def maybeFencedString(innerStr, **kwargs):
    '''
    Return innerStr, wrapped in parentheses iff kwargs['fence']==True.
    '''
    if 'fence' in kwargs and kwargs['fence']==True:
        return '(' + innerStr + ')'
    return innerStr

def maybeFencedLatex(innerLatex, **kwargs):
    '''
    Return innerLatex, wrapped in parentheses iff kwargs['fence']==True.
    '''
    if 'fence' in kwargs and kwargs['fence']==True:
        return r'\left(' + innerLatex + r'\right)'
    return innerLatex

def maybeFenced(formatType, innerFormatted, **kwargs):
    '''
    Return the innerFormatted string/latex iff kwargs['fence']=True.  If formatType=='string'
    use normal string formatting.  If formatType=='latex', use latex formatting.
    '''
    if formatType == 'string':
        return maybeFencedString(innerFormatted, **kwargs)
    elif formatType == 'latex':
        return maybeFencedLatex(innerFormatted, **kwargs)

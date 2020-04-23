from .composite import Composite, singleOrCompositeExpression
from proveit._core_.expression.expr import Expression, MakeNotImplemented
#import re

class NamedExprs(Composite, Expression):
    """
    An NamedExprs is a composite expr that maps strings to Expressions.
    """
    def __init__(self, items, styles=None):
        '''
        Create a NamedExprs Expression object from a list (iterable) of
        (keyword, Expression) pairs, where each keyword is a string.
        '''
        from proveit._core_ import KnownTruth
        keywords = []
        elems = dict()
        for key, val in items:
            keywords.append(key)
            if ':' in key:
                raise ValueError("':' not allowed in NamedExprs string")
            if not isinstance(key, str): 
                raise TypeError("Keywords of an expression dictionary may only be strings")
            #if not re.match('[A-Za-z0-9_]+', key):
            #    raise ValueError('A NamedExprs key may only include alphanumeric or underscore chararcters.')
            if isinstance(val, KnownTruth):
                val = val.expr # extract the Expression from the KnownTruth
            try:
                val = singleOrCompositeExpression(val)
            except TypeError:
                raise TypeError("Values of NamedExprs must be Expressions")
            assert isinstance(val, Expression)
            elems[key] = val
        self.keywords, self.elems = keywords, elems
        # ',' isn't allowed in the core info and ':' is not allowed
        # in NamedExprs keys, so swap one with the other to encode.
        core_info_enc_keywords = [key.replace(',', ':') for key in keywords]        
        Expression.__init__(self, ['NamedExprs'] + core_info_enc_keywords, 
                            [self[key] for key in list(self.keys())], 
                            styles=styles)

    def __getitem__(self, key):
        return self.elems[key]

    def __contains__(self, key):
        return key in self.elems
                        
    def __len__(self):
        return len(self.elems)
        
    def __iter__(self):
        return iter(self.elems)
        
    def items(self):
        for key in self.keywords:
            yield key, self.elems[key]
    
    def keys(self):
        return self.keywords

    def values(self):
        return self.elems.values()

    def remakeArguments(self):
        '''
        Yield the argument (name, value) pairs that could be used to 
        recreate the NamedExprs.  Wrap the names in quotation marks
        '''
        for name, expr in self.items():
            yield ('"' + str(name) + '"', expr)
            
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != NamedExprs: 
            MakeNotImplemented(subClass) 
        if coreInfo[0] != 'NamedExprs':
            raise ValueError("Expecting NamedExprs coreInfo[0] to be 'NamedExprs'")
        keys = [key.replace(':', ',') for key in coreInfo[1:]]
        if len(subExpressions) != len(keys):
            raise ValueError("The number of sub-expressions, " + str(len(subExpressions)), ", expected to match the number of the NamedExprs' keys, ", str(len(keys)))
        return NamedExprs([(key,subExpression) for key, subExpression in zip(keys, subExpressions)]).withStyles(**styles)   
        
    def string(self, **kwargs):
        return '{' + ', '.join(key + ':' + self[key].string(fence=True) for key in list(self.keys())) + '}'

    def latex(self, **kwargs):
        outStr = r'\left\{ \begin{array}{l}' + '\n'
        for key in list(self.keys()):
            if key[0] == '$':
                # format as latex
                formatted_key = key[1:-1]
            else:
                formatted_key = r'{\rm ' + key.replace('_', r'\_') + r'}'
            outStr += formatted_key + ': ' + self[key].latex(fence=True) + r'\\' + '\n'
        outStr += r'\end{array} \right\}' + '\n'
        return outStr            

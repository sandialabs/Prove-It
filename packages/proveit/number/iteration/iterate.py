'''
An Iter operation represents an iteration of a function
over a range of natural numbers which is to be embedded
into an ExprList, generally of the form f(1), ..., f(n).
The Iter operation operates on the Lambda mapping, e.g.
_X_ |-> f(_X_), and the endpoint expressions, e.g. 1 and n.

Use the iterate method to create an Iter Expression
by providing the firat and last instances, e.g.,
f(1) and f(n).  The lambda map and endpoints will be 
inferred from these.
'''

from proveit import Operation, Literal, Lambda
from proveit._generic_ import maybeFenced

def iterate(first_instance, last_instance):
    pass

class Iter(Operation):
    # The operator of the And operation
    _operator_ = Literal(stringFormat='...', latexFormat=r'...', context=__file__)
        
    def __init__(self, lambda_map, start_index, end_index):
        if not isinstance(lambda_map, Lambda):
            raise TypeError('When creating an Iter Expression, the lambda_map argument must be a Lambda expression')
        if len(lambda_map.parameters) != 1:
            raise ValueError('When creating an Iter Expression, the lambda_map argument should have exactly one parameter')            
        Operation.__init__(self, Iter._operator_, [lambda_map, start_index, end_index])
        self.lambda_map = lambda_map
        self.start_index = start_index
        self.end_index = end_index
    
    
    def first(self):
        '''
        Return the first instance of the iteration.
        '''
        return self.lambda_map.body.substituted({self.lambda_map.parameters[0]:self.start_index})

    def last(self):
        '''
        Return the last instance of the iteration.
        '''
        return self.lambda_map.body.substituted({self.lambda_map.parameters[0]:self.end_index})
        
    def string(self, **kwargs):
        # fence by default (unless it is within an Embed
        fence =  kwargs['fence'] if 'fence' in kwargs else True 
        innerStr = self.first().string() + ', ..., ' + self.last().string()
        return maybeFenced('string', innerStr, fence=fence)

    def latex(self, **kwargs):
        # fence by default (unless it is within an Embed
        fence =  kwargs['fence'] if 'fence' in kwargs else True
        innerStr = self.first().latex() + ', \ldots, ' + self.last().latex()
        return maybeFenced('latex', innerStr, fence=fence)

"""
        spc = '~' if formatType == 'latex' else ' ' 
        if formattedOperator is None:
            formattedOperator = ','
        formattedSubExpressions = [] 
        for subExpr in self:
            if isinstance(subExpr, Etcetera):
                if len(formattedSubExpressions) > 0 and formattedSubExpressions[-1] == '..'+spc:
                    # instead of having "..  .." back-to-back, do ".."
                    formattedSubExpressions[-1] = '...'
                else:
                    formattedSubExpressions.append(spc+'..')
                formattedSubExpressions.append(subExpr.bundledExpr.formatted(formatType, fence=subFence))
                formattedSubExpressions.append('..'+spc)
            else:
"""
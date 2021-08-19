from proveit import Literal
from proveit.abstract_algebra import GroupSum

class VecSum(GroupSum):
    '''
    Denote general summation over a set of elements of any field in 
    analogy to number summation.
    '''
    
    # operator of the Sum operation.
    _operator_ = Literal(string_format='Sum',  latex_format=r'\sum',
                         theory=__file__)
        
    def __init__(self, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, VecSum._operator_, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)

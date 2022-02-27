from proveit.abstract_algebra import GroupSum

class FieldSum(GroupSum):
    '''
    Denote general summation over a set of elements of any field in 
    analogy to number summation.
    '''
    
    def __init__(self, operator, index_or_indices, summand, *,
                 domain=None, domains=None, condition=None,
                 conditions=None, styles=None, _lambda_map=None):
        r'''
        '''
        GroupSum.__init__(self, operator, index_or_indices, summand,
                          domain=domain, domains=domains,
                          condition=condition, conditions=conditions,
                          styles=styles, _lambda_map=_lambda_map)

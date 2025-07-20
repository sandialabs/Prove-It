from proveit import Literal
from proveit.relation import Relation

class NotSubgraph(Relation):
    '''
    Given graph G'(V',E') with vertex set V' and edge set E',
    and given graph G(V,E) with vertex set V and edge set E,
    NotSubgraph(G', G) represents the claim that graph G' is
    NOT a subgraph of graph G. That would mean that V' is NOT
    a subset of V and/or E' is NOT a subset of E.
    '''

    # The operator of the NotSubgraph operation.
    # Following tradition in graph theory, we use the same operator
    # for not subgraph as we use for not subset, relying on the context
    # to distinguish the cases. We modify the string version for clarity.
    _operator_ = Literal(string_format='not_subgraph', 
                         latex_format=r'\nsubseteq',
                         theory=__file__)

    def __init__(self, A, B, *, styles=None):
        '''
        Create the expression for (A not_subgraph B)
        '''
        Relation.__init__(self, NotSubgraph._operator_, A, B,
                           styles=styles)
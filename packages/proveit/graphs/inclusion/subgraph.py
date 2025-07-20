from proveit import Literal
from proveit.logic.sets.inclusion.inclusion_relation import InclusionRelation

class Subgraph(InclusionRelation):
    '''
    Given graph G'(V',E') with vertex set V' and edge set E',
    and given graph G(V,E) with vertex set V and edge set E,
    Subgraph(G', G) represents the claim that graph G' is a
    subgraph of graph G. That would mean that V' is a subset of V,
    and E' is a subset of E.
    '''

    # The operator of the Subgraph operation.
    # Following tradition in graph theory, we use the same operator
    # for subgraph as we use for subset, relying on the context to
    # distinguish the cases. We modify the string version for clarity.
    _operator_ = Literal(string_format='subgraph',
                         latex_format=r'\subseteq',
                         theory=__file__)

    # map left-hand-sides to Subgraph Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Subgraph Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, A, B, *, styles=None):
        '''
        Create the expression for (G' subgraph G)
        '''
        InclusionRelation.__init__(self, Subgraph._operator_, A, B,
                                   styles=styles)
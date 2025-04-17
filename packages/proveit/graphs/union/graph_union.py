from proveit import Literal, Operation, USE_DEFAULTS, relation_prover
from proveit import m, n, A, S, x


class GraphUnion(Operation):
    '''
    GraphUnion(G1, G2, ..., Gn) represents the union of graphs
    G1, G2, ..., Gn. The union of graphs G_{i} = (V_{i}, E_{i})
    with vertex sets V_{i} and edge sets E_{i} gives a graph
    G = (V, E) = (U V_{i}, U E_{i}) with vertex set V consisting
    of the union of the vertex sets V_{i} and an edge set E
    consisting of the union of the edge sets E_{i}.
    For example, the GraphUnion of two graphs G1 = (V1, E1) and
    G2 = (V2, E2) is given by:

        G1 U G2 = (V1 U V2, E1 U E2).

    '''

    # Operator of the GraphUnion operation. We use the same notation
    # as we do for union of sets more generally, relying on context
    # to make clear what type of union operation is occurring.
    _operator_ = Literal(
            string_format='U', latex_format=r'\cup',theory=__file__)

    def __init__(self, *operands, styles=None):
        '''
        The union of any number of graphs: G1 U G2 U ... U Gn
        '''
        Operation.__init__(self, GraphUnion._operator_, operands,
                           styles=styles)

    def membership_object(self, element):
        from .graph_union_membership import GraphUnionMembership
        return GraphUnionMembership(element, self)

    def nonmembership_object(self, element):
        from .graph_union_membership import GraphUnionNonmembership
        return GraphUnionNonmembership(element, self)

    # keeping this here for now; the graph version will need the
    # concept of subgraph (instead of subset).
    # @relation_prover
    # def deduce_superset_eq_relation(self, superset, **defaults_config):
    #     # Check for special case of a union subset
    #     # A_1 union ... union ... A_m \subseteq S
    #     from . import union_inclusion
    #     _A = self.operands
    #     _m = _A.num_elements()
    #     _S = superset
    #     return union_inclusion.instantiate(
    #                 {A:_A, m:_m, S:_S})
            
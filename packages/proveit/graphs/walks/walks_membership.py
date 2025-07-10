from proveit import (i, k, C, G, P, S, T, W, equality_prover, Function,
        prover, relation_prover)
from proveit.logic import (Equals, Forall, InSet, SetMembership,
            SetNonmembership)
from proveit.logic.sets import Functions, Injections, SetOfAll
from proveit.numbers import zero, one, Add, Interval, subtract
from proveit.graphs import (AdjacentVertices, BeginningVertex,
            ClosedWalks, Edges,
            EdgeSequence, EndingVertex, Graph, Vertices, Walks)


class WalksMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k walks in the simple graph G, denoted Walks(k, G).
    See related membership classes further below for Trails and Paths.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'W in Walks(k, G)' for
        k in Natural and G in Graphs.
        '''
        yield self.element_length_derivation

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Walks(k, G)], deduce and return:
        [elem in Walks(G)]
        = elem in {S | Adjacent(S(i), S(i+1))}
        for {S in Functions([0,...,k], Vertices(G))}
        '''
        from . import walks_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return walks_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, W: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Walks(k, G)],
        return the expression (NOT a judgment):
        elem in {S | Adjacent(S(i), S(i+1))}
        for {S in Functions([0,...,k], Vertices(G))}
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element,
               SetOfAll(S, S,
               conditions = [
                   Forall(i,
                   AdjacentVertices(
                           Function(S, i), Function(S, Add(i, one)), _G),
                   domain = Interval(zero, subtract(_k, one)))],
               domain = Functions(Interval(zero, _k), Vertices(_G))))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Walks(k, G)], and knowing self,
        derive and return:
        elem in {S | Adjacent(S(i), S(i+1))}
        for {S in Functions([0,...,k], Vertices(G))}.
        '''
        from . import walks_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return walks_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, W: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [W in Walks(k, G)], derive and return
        self, knowing or assuming at least one of the following:
        (1) W in Functions([0,...,k], Vertices(G)) AND
            forall i in [0,..., k-1][AdjacentVertices(W(i), W(i+1), G)]
        (2) elem in {S | Adjacent(S(i), S(i+1))}
            for {S in Functions([0,...,k], Vertices(G))}
        '''
        _W = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        functions_set = Functions(Interval(zero, _k), Vertices(_G))
        adj_verts = Forall(
            i, AdjacentVertices(Function(_W, i),
                                Function(_W, Add(i, one)), _G),
            domain = Interval(zero, subtract(_k, one)))
        if (InSet(_W, functions_set).proven()
            and adj_verts.proven()):
            from . import walks_membership_folding_components
            return walks_membership_folding_components.instantiate(
                    {G: _G, k: _k, W: _W},
                    auto_simplify=False)
        
        from . import walks_membership_folding
        return walks_membership_folding.instantiate(
            {G: _G, k: _k, W: _W}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import walks_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _W_sub = self.element
        return walks_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, W:_W_sub}, auto_simplify=False)

    @prover
    def element_length_derivation(self, **defaults_config):
        '''
        Can't seem to make this work as an @equality_prover?
        From self = (element in Walks(k, G)) derive and return that
        WalkLength(element) = k.
        '''
        from . import walk_length_from_membership
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _W_sub = self.element
        return walk_length_from_membership.instantiate(
                {G: _G_sub, k: _k_sub, W: _W_sub}, auto_simplify=False)


class ClosedWalksMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k closed walks in the simple graph G, denoted
    ClosedWalks(k, G).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'W in ClosedWalks(k, G)' for
        k in Natural and G in Graphs.
        '''
        yield self.derive_element_in_walks

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in ClosedWalks(k, G)], deduce and return
        the equality:
            [elem in ClosedWalks(k, G)]
             = elem in {S | BeginningVertex(S) = EndingVertex(S)}
             for {S in Walks(k, G)}
        '''
        from . import closed_walks_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return closed_walks_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, W: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in ClosedWalks(k, G)],
        return the expression (NOT a judgment):
            elem in {S | BeginningVertex(S) = EndingVertex(S)}
            for {S in Walks(k, G)}
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element,
               SetOfAll(S, S,
               conditions = [Equals(BeginningVertex(S), EndingVertex(S))],
               domain = Walks(_k, _G)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in ClosedWalks(k, G)], and knowing (or
        (assuming) self, derive and return:
             elem in {S | BeginningVertex(S) = EndingVertex(S)}
             for {S in Walks(k, G)}.
        '''
        from . import closed_walks_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return closed_walks_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, W: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [W in ClosedWalks(k, G)], derive and return
        self, knowing or assuming that:
            W in {S | BeginningVertex(S) = EndingVertex(S)}
            for {S in Walks(k, G)}
        '''
        _W = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        from . import closed_walks_membership_folding
        return closed_walks_membership_folding.instantiate(
            {G: _G, k: _k, W: _W}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import closed_walks_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _W_sub = self.element
        return closed_walks_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, W:_W_sub}, auto_simplify=False)

    @prover
    def derive_element_in_walks(self, **defaults_config):
        from . import closed_walks_within_walks
        _G      = self.domain.graph
        _k      = self.domain.length
        return (closed_walks_within_walks.instantiate(
            {G:_G, k:_k}, auto_simplify=False)
            .derive_superset_membership(self.element, auto_simplify=False))


class TrailsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k trails in the simple graph G, denoted Trails(k, G).
    See related membership classes above and below for Walks and Paths.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'W in Trails(k, G)' for
        k in Natural and G in Graphs.
        '''
        yield self.derive_element_in_walks

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Trails(k, G)], deduce and return:
        [elem in Trails(k, G)]
        = elem in
        {W | EdgeSequence(W) in Injections([0, ..., k-1], Edges(G))}
        for {W in Walks(k, G)}.
        W being in Walks(k, G) takes care of the requirement that 
        consecutive elements of the vertex sequence are adjacent in
        the graph G.
        '''
        from . import trails_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return trails_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, T: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Trails(k, G)],
        return the expression (NOT a judgment):
        elem in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
        for {W in Walks(k, G)}
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element,
               SetOfAll(W, W,
               conditions = [
                   InSet(EdgeSequence(W),
                   Injections(Interval(zero, subtract(_k, one)), Edges(_G)))],
               domain = Walks(_k, _G)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Trails(k, G)], and knowing or assuming
        self, derive and return:
        elem in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
                 for {W in Walks(k, G)}.
        '''
        from . import trails_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return trails_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, T: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [W in Trails(k, G)], derive and return
        self, knowing or assuming at least one of the following:
        (1) W in Walks(k, G) AND
            EdgeSeq(W) in Injections([0,...,k-1], Edges(G))
        (2) W in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
                 for {W in Walks(k, G)}
        '''
        _W = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        injections_set = (
            Injections(Interval(zero, subtract(_k, one)), Edges(_G)))
        if (InSet(EdgeSequence(_W), injections_set).proven()
            and InSet(_W, Walks(_k, _G)).proven()):
            from . import trails_membership_folding_components
            return trails_membership_folding_components.instantiate(
                    {G: _G, k: _k, W: _W},
                    auto_simplify=False)
        
        from . import trails_membership_folding
        return trails_membership_folding.instantiate(
            {G: _G, k: _k, W: _W}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import trails_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _T_sub = self.element
        return trails_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, T:_T_sub}, auto_simplify=False)

    @prover
    def derive_element_in_walks(self, **defaults_config):
        from . import trails_within_walks
        _G      = self.domain.graph
        _k      = self.domain.length
        return (trails_within_walks.instantiate(
            {G:_G, k:_k}, auto_simplify=False)
            .derive_superset_membership(self.element, auto_simplify=False))


class ClosedTrailsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of length-k
    closed trails in the simple graph G, denoted ClosedTrails(k, G).
    See related membership classes above and below for Trails, Walks,
    etc.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'W in ClosedTrails(k, G)' for
        k in Natural and G in Graphs.
        '''
        yield self.derive_element_in_closed_walks

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in ClosedTrails(k, G)], deduce and return:
        [elem in ClosedTrails(k, G)]
        = elem in
        {W | EdgeSequence(W) in Injections([0, ..., k-1], Edges(G))}
        for {W in ClosedWalks(k, G)}.
        W being in ClosedWalks(k, G) takes care of the requirement that 
        consecutive elements of the vertex sequence are adjacent in
        the graph G.
        '''
        from . import closed_trails_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return closed_trails_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, T: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in ClosedTrails(k, G)],
        return the expression (NOT a judgment):
        elem in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
        for {W in ClosedWalks(k, G)}
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element,
               SetOfAll(W, W,
               conditions = [
                   InSet(EdgeSequence(W),
                   Injections(Interval(zero, subtract(_k, one)), Edges(_G)))],
               domain = ClosedWalks(_k, _G)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in ClsoedTrails(k, G)], and knowing or
        assuming self, derive and return:
        elem in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
                 for {W in ClosedWalks(k, G)}.
        '''
        from . import closed_trails_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return closed_trails_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, T: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [W in ClosedTrails(k, G)], derive and return
        self, knowing or assuming at least one of the following:
        (1) W in ClosedWalks(k, G) AND
            EdgeSeq(W) in Injections([0,...,k-1], Edges(G))
        (2) W in {W | EdgeSequence(W) in
                 Injections([0, ..., k-1], Edges(G))}
                 for {W in ClosedWalks(k, G)}
        '''
        _W = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        injections_set = (
            Injections(Interval(zero, subtract(_k, one)), Edges(_G)))
        if (InSet(EdgeSequence(_W), injections_set).proven()
            and InSet(_W, ClosedWalks(_k, _G)).proven()):
            from . import closed_trails_membership_folding_components
            return (closed_trails_membership_folding_components
                    .instantiate({G: _G, k: _k, W: _W},
                    auto_simplify=False))
        
        from . import closed_trails_membership_folding
        return closed_trails_membership_folding.instantiate(
            {G: _G, k: _k, W: _W}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import closed_trails_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _T_sub = self.element
        return closed_trails_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, T:_T_sub}, auto_simplify=False)

    @prover
    def derive_element_in_closed_walks(self, **defaults_config):
        from . import closed_trails_within_closed_walks
        _G      = self.domain.graph
        _k      = self.domain.length
        return (closed_trails_within_closed_walks.instantiate(
            {G:_G, k:_k}, auto_simplify=False)
            .derive_superset_membership(self.element, auto_simplify=False))


class PathsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of length-k
    paths in the simple graph G, denoted Paths(k, G). A path in G is
    a walk in which no vertex (and thus no edge) is repeated.
    See related membership classes above for Walks and Trails.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'W in Paths(k, G)' for
        k in Natural and G in Graphs.
        '''
        yield self.derive_element_in_trails

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Paths(k, G)], deduce and return:
        [elem in Paths(k, G)]
        = elem in {W | W in Injections([0, ..., k], Vertices(G))}
                  for {W in Walks(k, G)}.
        W being in Walks(k, G) takes care of the requirement that 
        consecutive elements of the vertex sequence are adjacent in the
        graph G.
        '''
        from . import paths_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return paths_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, P: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Paths(k, G)],
        return the expression (NOT a judgment):
        elem in {W | W in Injections([0, ..., k], Vertices(G))}
                for {W in Walks(k, G)}.
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element,
               SetOfAll(W, W,
               conditions = [
                   InSet(W,
                   Injections(Interval(zero, _k), Vertices(_G)))],
               domain = Walks(_k, _G)))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Paths(k, G)], and knowing or assuming
        self, derive and return:
        elem in {W | W in Injections([0, ..., k], Vertices(G))}
                for {W in Walks(k, G)}.
        '''
        from . import paths_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return paths_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, P: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [P in Paths(k, G)], derive and return
        self, knowing or assuming at least one of the following:
        (1) P in Walks(k, G) AND
            P in Injections([0,...,k], Vertices(G))
        (2) P in {W | W in Injections([0, ..., k], Vertices(G))}
                 for {W in Walks(k, G)}
        '''
        _W = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        injections_set = Injections(Interval(zero, _k), Vertices(_G))
        if (InSet(_W, injections_set).proven()
            and InSet(_W, Walks(_k, _G)).proven()):
            from . import paths_membership_folding_components
            return paths_membership_folding_components.instantiate(
                    {G: _G, k: _k, W: _W},
                    auto_simplify=False)
        from . import paths_membership_folding
        return paths_membership_folding.instantiate(
            {G: _G, k: _k, W: _W}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import paths_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _P_sub = self.element
        return paths_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, P:_P_sub}, auto_simplify=False)

    @prover
    def derive_element_in_trails(self, **defaults_config):
        from . import paths_within_trails
        _G      = self.domain.graph
        _k      = self.domain.length
        return (paths_within_trails.instantiate(
            {G:_G, k:_k}, auto_simplify=False)
            .derive_superset_membership(self.element, auto_simplify=False))


class CircuitsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of length-k
    circuits in the simple graph G, denoted Circuits(k, G). A circuit
    in G is a closed trail -- i.e., a closed walk in which no edge is
    repeated.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'C in Circuits(k, G)' for
        Natural k >= 3 and G in Graphs.
        '''
        yield self.derive_element_in_closed_trails

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        From self = [elem in Circuits(k, G)], with k >= 3, deduce
        and return:
        [elem in Circuits(k, G)] = elem in ClosedWalks(k, G).
        '''
        from . import circuits_membership_def
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return circuits_membership_def.instantiate(
                {G: _G_sub, k: _k_sub, C: element },auto_simplify=False)

    def as_defined(self):
        '''
        From self = [elem in Circuits(k, G)], return the expression
        (NOT a judgment):
                           elem in ClosedWalks(k, G).
        '''
        element = self.element
        _G      = self.domain.graph
        _k      = self.domain.length
        return InSet(element, ClosedWalks(_k, _G))

    @prover
    def unfold(self, **defaults_config):
        '''
        From self = [elem in Circuits(k, G)], and knowing or assuming
        self and k >= 3, derive and return: elem ClosedWalks(k, G).
        '''
        from . import circuits_membership_unfolding
        element = self.element
        _G_sub  = self.domain.graph
        _k_sub  = self.domain.length
        return circuits_membership_unfolding.instantiate(
            {G: _G_sub, k: _k_sub, C: element}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [C in Circuits(k, G)], derive and return
        self, knowing or assuming BOTH of the following:
        (1) k >= 3
        (2) C in ClosedTrails(k, G)
        '''
        _C = self.element
        _G  = self.domain.graph
        _k  = self.domain.length
        from . import circuits_membership_folding
        return circuits_membership_folding.instantiate(
            {G: _G, k: _k, C: _C}, auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import circuits_membership_is_bool
        _G_sub = self.domain.graph
        _k_sub = self.domain.length
        _C_sub = self.element
        return circuits_membership_is_bool.instantiate(
            {G:_G_sub, k:_k_sub, C:_C_sub}, auto_simplify=False)

    @prover
    def derive_element_in_closed_trails(self, **defaults_config):
        from . import circuits_within_closed_trails
        _G      = self.domain.graph
        _k      = self.domain.length
        return (circuits_within_closed_trails.instantiate(
            {G:_G, k:_k}, auto_simplify=False)
            .derive_superset_membership(self.element, auto_simplify=False))


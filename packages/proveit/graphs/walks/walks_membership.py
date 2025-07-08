from proveit import (i, k, G, P, S, T, W, equality_prover, Function,
        prover, relation_prover)
from proveit.logic import (Equals, Forall, InSet, SetMembership,
            SetNonmembership)
from proveit.logic.sets import Functions, Injections, SetOfAll
from proveit.numbers import zero, one, Add, Interval, subtract
from proveit.graphs import (AdjacentVertices, BeginningVertex, Edges,
            EdgeSequence, EndingVertex, Graph, Vertices, Walks)


class WalksMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k walks in the simple graph G, denoted Walks(k, G).
    See related membership classes further below for Trails and Paths.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

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


class ClosedWalksMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k closed walks in the simple graph G, denoted
    ClosedWalks(k, G).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

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


class TrailsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set
    of length-k trails in the simple graph G, denoted Trails(k, G).
    See related membership classes above and below for Walks and Paths.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

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


class PathsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of length-k
    paths in the simple graph G, denoted Paths(k, G). A path in G is
    a walk in which no vertex (and thus no edge) is repeated.
    See related membership classes above for Walks and Trails.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

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

    @prover # WORKING HERE
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


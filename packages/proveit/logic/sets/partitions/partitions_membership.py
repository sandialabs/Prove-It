from proveit import USE_DEFAULTS, equality_prover, prover
from proveit import S, X
from proveit.logic import SetMembership
# from proveit.numbers import num
# from proveit import m, A, x


class PartitionsMembership(SetMembership):
    '''
    Defines methods that apply to membership in Partitions(S), the
    set of partitions of set S. If set S is finite, Partitions(S)
    is a finite set; if S is infinite, Partitions(S) is infinite.
    A partition P of a set S is a set of non-empty subsets S1,S2,...
    of S such that elements of P are mutually disjoint and
    Union(S1,S2,...) = S.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Main side effect is to unfold the basic definition of
        memberhip in the set of partitions. If P is an element of
        Partitions(S), then P is a set of non-empty subsets of S
        whose union is S.
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        For self = [element in Partitions(S)], deduce and return the
        equality:
            [element in Partitions(S)] = 
            [element in SetOfAll(P, P, conditions)_{P in Pow(Pow(S))}]
        where the conditions are:
            * no element of P is the empty set
            * the elems of P are all mutually disjoint
            * the union of all elems of P is S
        '''
        from . import partitions_membership_def
        _X_sub = self.element
        _S_sub  = self.domain.operand
        return partitions_membership_def.instantiate(
                {S: _S_sub, X: _X_sub}, auto_simplify=False)

    def as_defined(self):
        '''
        For self = [element in Partitions(S)], return the expression
        (NOT a judgment):
            [element in SetOfAll(P, P, conditions)_{P in Pow(Pow(S))}]
        where the conditions are:
            * no element of P is the empty set
            * the elems of P are all mutually disjoint
            * the union of all elems of P is S
        '''
        from proveit import A, B, P
        from proveit.logic import Equals, Forall, InSet, NotEquals
        from proveit.logic.sets import (
                Disjoint, EmptySet, PowerSet, SetOfAll, UnionAll)
        _S = self.domain.operand
        _X = self.element
        return InSet(_X,
               SetOfAll(P, P,
               conditions = [Equals(UnionAll(A, A, domain = P), S),
                             Forall(A, NotEquals(A, EmptySet), domain = P),
                             Forall((A, B), Disjoint(A, B), domain = P)],
               domain = PowerSet(PowerSet(S))))

    @prover
    def unfold(self, **defaults_config):
        '''
        Given self = [element in Partitions(S)] and knowing or
        assuming self is True, derive and return
            [element in SetOfAll(P, P, conditions)_{P in Pow(Pow(S))}]
        where the conditions are:
            * no element of P is the empty set
            * the elems of P are all mutually disjoint
            * the union of all elems of P is S
        '''
        from . import partitions_membership_unfolding
        _S_sub = self.domain.operand
        _X_sub = self.element
        return partitions_membership_unfolding.instantiate(
            {S: _S_sub, X:_X_sub}, auto_simplify=False)

    @prover
    def conclude(self, **defaults_config):
        '''
        Called on self = [elem in Partitions(S)], and knowing or
        assuming that:
            [elem in SetOfAll(P, P, conditions)_{P in Pow(Pow(S))}]
        where the conditions are:
            * no element of P is the empty set
            * the elems of P are all mutually disjoint
            * the union of all elems of P is S,
        derive and return self.
        '''
        from . import partitions_membership_folding
        _S_sub = self.domain.operand
        _X_sub = self.element
        return partitions_membership_folding.instantiate({S: _S_sub, X:_X_sub})

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import partitions_membership_is_bool
        _S_sub = self.domain.operand
        _X_sub = self.element
        return partitions_membership_is_bool.instantiate(
            {S: _S_sub, X:_X_sub})


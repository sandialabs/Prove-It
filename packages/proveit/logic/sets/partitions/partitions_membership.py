from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.logic import SetMembership
from proveit.numbers import num
from proveit import m, A, x


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

    # def side_effects(self, judgment):
    #     '''
    #     Unfold the enumerated set membership as a side-effect.
    #     '''
    #     yield self.unfold

    # @equality_prover('defined', 'define')
    # def definition(self, **defaults_config):
    #     '''
    #     Deduce and return 
    #         [element in (A union B ...)] = 
    #         [(element in A) or (element in B) ...]
    #     where self = (A union B ...).
    #     '''
    #     from . import union_def
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return union_def.instantiate(
    #             {m: _m, x: element, A: _A}, auto_simplify=False)

    # def as_defined(self):
    #     '''
    #     From self=[elem in (A U B U ...)], return
    #     [(element in A) or (element in B) or ...].
    #     '''
    #     from proveit.logic import Or, InSet
    #     element = self.element
    #     return Or(*self.domain.operands.map_elements(
    #             lambda subset : InSet(element, subset)))

    # @prover
    # def unfold(self, **defaults_config):
    #     '''
    #     From [element in (A union B ...)], derive and return
    #     [(element in A) or (element in B) ...],
    #     where self represents [element in (A union B ...)].
    #     '''
    #     from . import membership_unfolding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_unfolding.instantiate(
    #         {m: _m, x: element, A: _A}, auto_simplify=False)

    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     Called on self = [elem in (A U B U ...)], and knowing or
    #     assuming [[elem in A] OR [elem in B] OR ...], derive and
    #     return self.
    #     '''
    #     from . import membership_folding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_folding.instantiate({m: _m, x: element, A: _A})

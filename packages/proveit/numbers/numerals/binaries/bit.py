from proveit import prover
from proveit import b
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership
from proveit.numbers.numerals import zero, one
BITS = [zero, one]

class BitSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(
            self, 'Bits', r'\mathbb{N}^{\leq 1}',
            theory=__file__, styles=styles)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import bits_lower_bound
        return bits_lower_bound.instantiate({b: member})

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import bits_upper_bound
        return bits_upper_bound.instantiate({b: member})

    def membership_object(self, element):
        return BitMembership(element, self)

class BitMembership(NumberMembership):
    '''
        Defines methods that apply to membership of the BitSet
    '''

    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    @prover
    def conclude(self, **defaults_config):
        from proveit import ProofFailure
        from . import b_in_bits
        # if we know the element is 0-1, then we can show it is a bit
        try:
            return NumberMembership.conclude(self)
        except ProofFailure:
            return b_in_bits.instantiate({b:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Digit' for a given n.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_upper_bound

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        return self.domain.deduce_member_lower_bound(self.element)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        return self.domain.deduce_member_upper_bound(self.element)



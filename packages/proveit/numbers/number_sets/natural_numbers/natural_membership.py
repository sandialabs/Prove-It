from proveit import prover
from proveit import a, n, x
from proveit.logic import NotEquals, InSet
from proveit.numbers import greater, greater_eq
from proveit.numbers import (zero, Natural, NaturalPos, Integer)
from proveit.numbers.number_sets.number_set import NumberMembership


class NaturalMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    @prover
    def conclude(self, **defaults_config):
        if (InSet(self.element, Integer).proven() and
                greater_eq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in Natural by proving it is integer
        and non-negative.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from proveit.numbers.number_sets.integers import (
            nonneg_int_is_natural)
        return nonneg_int_is_natural.instantiate({a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Natural' for a given n.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_in_int
        yield self.derive_element_in_rational_nonneg

    @prover
    def deduce_in_bool(self, **defaults_config):
        from proveit.numbers.number_sets.natural_numbers import (
                nat_membership_is_bool)
        return nat_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from proveit.numbers.number_sets.natural_numbers import (
                natural_lower_bound)
        return natural_lower_bound.instantiate(
            {n: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_int(self, **defaults_config):
        from proveit.numbers.number_sets.integers import nat_within_int
        return nat_within_int.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonneg(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                nat_within_rational_nonneg)
        return nat_within_rational_nonneg.derive_superset_membership(
            self.element, auto_simplify=False)


class NaturalPosMembership(NaturalMembership):

    '''
    Defines methods that apply to membership in RationalPos
    '''

    def __init__(self, element):
        NaturalMembership.__init__(self, element, NaturalPos)

    @prover
    def conclude(self, **defaults_config):
        if (InSet(self.element, Integer).proven() and
                greater(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in NaturalPos by proving it is integer
        and positive.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from proveit.numbers.number_sets.integers import (
            pos_int_is_natural_pos)
        return pos_int_is_natural_pos.instantiate({a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in NaturalPos' for a given n.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_in_nat
        yield self.derive_element_in_int
        yield self.derive_element_in_nonzero_int
        yield self.derive_element_nonzero
        yield self.derive_element_in_rational_pos

    @prover
    def deduce_in_bool(self, **defaults_config):
        from proveit.numbers.number_sets.natural_numbers import (
                nat_pos_membership_is_bool)
        from proveit import x
        return nat_pos_membership_is_bool.instantiate({x: self.element},
                                                      auto_simplify=False)

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        from proveit.numbers.number_sets.natural_numbers import (
                natural_pos_lower_bound)
        return natural_pos_lower_bound.instantiate({n: self.element},
                                                   auto_simplify=False)

    @prover
    def derive_element_nonzero(self, **defaults_config):
        from proveit.numbers.number_sets.natural_numbers import (
                nonzero_if_is_nat_pos)
        _n = nonzero_if_is_nat_pos.instance_param
        return nonzero_if_is_nat_pos.instantiate({_n: self.element},
                                                 auto_simplify=False)

    @prover
    def derive_element_in_nat(self, **defaults_config):
        from . import nat_pos_within_nat
        return nat_pos_within_nat.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_int(self, **defaults_config):
        from proveit.numbers.number_sets.integers import nat_pos_within_int
        return nat_pos_within_int.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_nonzero_int(self, **defaults_config):
        from proveit.numbers.number_sets.integers import (
                nat_pos_within_nonzero_int)
        return nat_pos_within_nonzero_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_pos(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                nat_pos_within_rational_pos)
        return nat_pos_within_rational_pos.derive_superset_membership(
            self.element, auto_simplify=False)
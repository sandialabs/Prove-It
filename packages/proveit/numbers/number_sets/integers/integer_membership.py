from proveit import prover, relation_prover
from proveit import a, x
from proveit.logic import NotEquals, InSet
from proveit.numbers import Less, LessEq
from proveit.numbers import (zero, Integer, IntegerNeg,
                             IntegerNonPos, IntegerNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership


class IntegerMembership(NumberMembership):
    '''
    Defines methods that apply to membership in Integer.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, Integer)
    

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Integer' for a given n.
        '''
        yield self.derive_element_in_rational
        # Added but commented the following out while we debate the
        # wisdom of further side-effects
        # yield lambda: self.deduce_member_in_real(member)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import int_membership_is_bool
        from proveit import x
        return int_membership_is_bool.instantiate(
                {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import int_within_rational
        return int_within_rational.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import int_within_real
        return int_within_real.derive_superset_membership(
                self.element, auto_simplify=False)

class IntegerNonZeroMembership(NumberMembership):
    '''
    Defines methods that apply to membership in IntegerNonZero.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNonZero)

    @prover
    def conclude(self, **defaults_config):
        if (InSet(self.element, Integer).proven() and
                NotEquals(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in IntegerNonZero by proving it is integer
        and non-zero.  This is called via NumberMembership.conclude
        if the 'deduce_in_number_set' method of the element raises
        a NotImplementedError.
        '''
        from . import nonzero_int_is_int_nonzero
        return nonzero_int_is_int_nonzero.instantiate({a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in IntegerNonZero' for 
        a given n.
        '''
        yield self.derive_element_not_zero
        yield self.derive_element_in_integer
        yield self.derive_element_in_rational_nonzero

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import nonzero_int_membership_is_bool
        return nonzero_int_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_not_zero(self, **defaults_config):
        from . import nonzero_if_in_nonzero_int
        return nonzero_if_in_nonzero_int.instantiate(
            {a: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import nonzero_int_within_int
        return nonzero_int_within_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonzero(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                nonzero_int_within_rational_nonzero)
        return nonzero_int_within_rational_nonzero.derive_superset_membership(
            self.element, auto_simplify=False)


class IntegerNegMembership(NumberMembership):

    '''
    Defines methods that apply to membership in IntegerNeg.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNeg)
    
    @prover
    def conclude(self, **defaults_config):
        if (InSet(self.element, Integer).proven() and
                Less(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in IntegerNeg by proving it is integer
        and negative.  This is called in NumberMembership.conclude
        as a last resort.
        '''
        from . import neg_int_is_int_neg
        return neg_int_is_int_neg.instantiate({a:self.element})


    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in IntegerNeg' for a given n.
        '''
        yield self.derive_element_upper_bound
        yield self.derive_element_in_integer
        yield self.derive_element_in_integer_non_zero
        yield self.derive_element_in_integer_non_pos
        yield self.derive_element_in_rational_neg

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import neg_int_membership_is_bool
        from proveit import x
        return neg_int_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)
    
    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import negative_if_in_neg_int
        return negative_if_in_neg_int.instantiate(
            {a: self.element}, auto_simplify=False)
    
    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import neg_int_within_int
        return neg_int_within_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_integer_non_zero(self, **defaults_config):
        from . import neg_int_within_nonzero_int
        return neg_int_within_nonzero_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_integer_non_pos(self, **defaults_config):
        from . import neg_int_within_nonpos_int
        return neg_int_within_nonpos_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_neg(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                neg_int_within_rational_neg)
        return neg_int_within_rational_neg.derive_superset_membership(
            self.element, auto_simplify=False)


class IntegerNonPosMembership(NumberMembership):

    '''
    Defines methods that apply to membership in IntegerNonPos.
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerNonPos)

    @prover
    def conclude(self, **defaults_config):
        if (InSet(self.element, Integer).proven() and
                LessEq(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in IntegerNeg by proving it is integer
        and non-positive.  This is called via NumberMembership.conclude
        if the 'deduce_in_number_set' method of the element raises
        a NotImplementedError.
        '''
        from . import nonpos_int_is_int_nonpos
        return nonpos_int_is_int_nonpos.instantiate({a:self.element})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in IntegerNonPos' for
        a given n.
        '''
        yield self.derive_element_upper_bound
        yield self.derive_element_in_integer
        yield self.derive_element_in_rational_nonpos

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import nonpos_int_membership_is_bool
        from proveit import x
        return nonpos_int_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        from . import nonpos_if_in_nonpos_int
        return nonpos_if_in_nonpos_int.instantiate(
            {a: self.element}, auto_simplify=False)    

    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import nonpos_int_within_int
        return nonpos_int_within_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational_nonpos(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                nonpos_int_within_rational_nonpos)
        return nonpos_int_within_rational_nonpos.derive_superset_membership(
            self.element, auto_simplify=False)

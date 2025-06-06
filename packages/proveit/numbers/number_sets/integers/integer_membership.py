from proveit import prover, relation_prover
from proveit import a, x, z
from proveit.logic import Equals, Exists, InSet, NotEquals
from proveit.numbers import Add, Less, LessEq, Mult
from proveit.numbers import (
        zero, one, two, Integer, IntegerEven, IntegerNeg,
        IntegerNonPos, IntegerNonZero, IntegerOdd)
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

    def _readily_provable(self):
        return NumberMembership._readily_provable(self)

    @prover
    def conclude(self, **defaults_config):
        # Use proven, not readily provable here:
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
    
    def _readily_provable(self):
        return NumberMembership._readily_provable(self)

    @prover
    def conclude(self, **defaults_config):
        # Use proven, not readily provable here:
        if (InSet(self.element, Integer).proven() and
                Less(self.element, zero).proven()):
            return self.conclude_as_last_resort()
        if (InSet(self.element, IntegerNonPos).proven() and
                NotEquals(self.element, zero).readily_provable()):
            return self.conclude_via_nonzero()
        return NumberMembership.conclude(self)

    @prover
    def conclude_via_nonzero(self, **defaults_config):
        '''
        Conclude element in IntegerNeg by proving it is a non-positive
        integer and nonzero.
        '''
        from proveit.numbers.number_sets.integers import (
            nonzero_nonpos_int_is_neg_int)
        return nonzero_nonpos_int_is_neg_int.instantiate({a:self.element})

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
        # Use proven, not readily provable here:
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

class IntegerEvenMembership(NumberMembership):
    '''
    Defines methods that apply to membership in IntegerEven (the
    set of even integers, E = {..., -2, 0, 2, 4, ...}).
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerEven)

    def _readily_provable(self):
        return NumberMembership._readily_provable(self)

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude element in IntegerEven using the fact that the
        element can be expressed as 2z for some z in Integer.
        '''
        # Use proven, not readily provable here:
        if Exists(z, Equals(self.element, Mult(two, z)), domain=Integer).proven():
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in IntegerEven using the fact that the
        element can be expressed as 2z for some Integer z.
        This method is called via NumberMembership.conclude()
        if the 'deduce_in_number_set' method of the element raises
        a NotImplementedError.
        '''
        from . import double_int_is_even
        _a_sub = self.element
        return double_int_is_even.instantiate({a:_a_sub})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in IntegerEven' for 
        # a given n:
        (1) An even integer n is an integer;
        (2) An even integer n is a rational number;
        (3) An even integer is a real number;
        (4) An even integer n can be expressed as 2z for some
            integer z.
        '''
        yield self.derive_element_in_integer
        yield self.derive_element_in_rational
        yield self.derive_element_in_real
        yield self.derive_element_as_double_int

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import even_int_membership_is_bool
        return even_int_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import even_int_within_int
        return even_int_within_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                even_int_within_rational)
        return even_int_within_rational.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                even_int_within_real)
        return even_int_within_real.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_as_double_int(self, **defaults_config):
        from . import even_int_is_double_int
        _a_sub = self.element
        return even_int_is_double_int.instantiate({a:_a_sub})

class IntegerOddMembership(NumberMembership):
    '''
    Defines methods that apply to membership in IntegerOdd (the
    set of odd integers, O = {..., -3, -1, 1, 3, ...}).
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, IntegerOdd)

    def _readily_provable(self):
        return NumberMembership._readily_provable(self)

    @prover
    def conclude(self, **defaults_config):
        '''
        Conclude element in IntegerOdd using the fact that the
        element can be expressed as (2z + 1) for some z in Integer.
        '''
        # Use proven, not readily provable here:
        if Exists(z, Equals(self.element, Add(Mult(two, z), one)),
                  domain=Integer).proven():
            return self.conclude_as_last_resort()
        return NumberMembership.conclude(self)

    @prover
    def conclude_as_last_resort(self, **defaults_config):
        '''
        Conclude element in IntegerOdd using the fact that the
        element can be expressed as (2z + 1) for some Integer z.
        This method is called via NumberMembership.conclude()
        if the 'deduce_in_number_set' method of the element raises
        a NotImplementedError.
        '''
        from . import double_int_plus_one_is_odd
        _a_sub = self.element
        return double_int_plus_one_is_odd.instantiate({a:_a_sub})

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in IntegerOdd' for 
        # a given n:
        (1) An odd integer n is an integer;
        (2) An odd integer n is a rational number;
        (3) An odd integer n is a real number;
        (4) An odd integer n can be expressed as 2z+1 for some
            integer z.
        '''
        yield self.derive_element_in_integer
        yield self.derive_element_in_rational
        yield self.derive_element_in_real
        yield self.derive_element_as_double_int_plus_one

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import odd_int_membership_is_bool
        return odd_int_membership_is_bool.instantiate(
            {x: self.element}, auto_simplify=False)

    @prover
    def derive_element_in_integer(self, **defaults_config):
        from . import odd_int_within_int
        return odd_int_within_int.derive_superset_membership(
            self.element, auto_simplify=False)

    @prover
    def derive_element_in_rational(self, **defaults_config):
        from proveit.numbers.number_sets.rational_numbers import (
                odd_int_within_rational)
        return odd_int_within_rational.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_in_real(self, **defaults_config):
        from proveit.numbers.number_sets.real_numbers import (
                odd_int_within_real)
        return odd_int_within_real.derive_superset_membership(
                self.element, auto_simplify=False)

    @prover
    def derive_element_as_double_int_plus_one(self, **defaults_config):
        from . import odd_int_is_double_int_plus_one
        _a_sub = self.element
        return odd_int_is_double_int_plus_one.instantiate({a:_a_sub})

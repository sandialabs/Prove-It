from proveit import (defaults, Literal, Operation, ProofFailure, 
                     relation_prover)
# from proveit.numbers.number_sets import Integer, Real
from proveit import a, b
from proveit.logic import InSet
from proveit.numbers import NumberOperation

class Mod(NumberOperation):
    # operator of the Mod operation.
    _operator_ = Literal(string_format='mod', latex_format=r'~\textup{mod}~',
                         theory=__file__)

    def __init__(self, dividend, divisor, *, styles=None):
        NumberOperation.__init__(self, Mod._operator_, (dividend, divisor),
                                 styles=styles)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    # def deduce_in_interval(self, assumptions=frozenset()):
    #     from . import mod_in_interval, mod_in_interval_c_o
    #     from number_sets import deduce_in_integer, deduce_in_real
    #     try:
    #         # if the operands are integers, then we can deduce that
    #         # a mod b is in 0..(b-1)
    #         deduce_in_integer(self.operands, assumptions)
    #         return mod_in_interval.instantiate(
    #                 {a:self.dividend, b:self.divisor}).checked(assumptions)
    #     except:
    #         # if the operands are reals, then we can deduce that a mod b is in [0, b)
    #         deduce_in_real(self.operands, assumptions)
    # return mod_in_interval_c_o.instantiate({a:self.dividend,
    # b:self.divisor}).checked(assumptions)

    @relation_prover
    def deduce_in_interval(self, **defaults_config):
        '''
        Prove that the "x mod b" is in the interval [0, b).
        '''
        from . import (mod_in_interval, mod_natpos_in_interval,
                       mod_in_interval_c_o)
        from proveit.numbers import Integer, NaturalPos
        # from number_sets import deduce_in_integer, deduce_in_real
        int_dividend = InSet(self.dividend, Integer).proven()
        if (int_dividend and InSet(self.divisor, NaturalPos).proven()):
            return mod_natpos_in_interval.instantiate(
                {a: self.dividend, b: self.divisor})
        elif (int_dividend and InSet(self.divisor, Integer).proven()):
            # if the operands are integers, then we can deduce that
            # a mod b is an integer in the set {0,1,...,(b-1)}
            return mod_in_interval.instantiate(
                {a: self.dividend, b: self.divisor})
        else:
            # if the operands are reals, then we can deduce that
            # a mod b is in half-open real interval [0, b)
            return mod_in_interval_c_o.instantiate(
                {a: self.dividend, b: self.divisor})

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given Mod expression is in that number
        set using the appropriate closure theorem.
        '''
        from proveit.numbers.modular import (
            mod_int_closure, mod_int_to_nat_closure, mod_real_closure)
        from proveit.numbers import (Integer, Natural, Real,
                                     Interval, RealInterval)

        if (isinstance(number_set, Interval) or 
                isinstance(number_set, RealInterval)):
            if isinstance(number_set, Interval):
                # To prove that it is in an integer interval through
                # standard means, we'll need to know that the dividend
                # and divisor are integers.
                InSet(self.dividend, Integer).prove()
                InSet(self.divisor, Integer).prove()
            in_mod_interval = self.deduce_in_interval()
            mod_interval = in_mod_interval.domain
            if mod_interval == number_set:
                return in_mod_interval
            # To prove by standard means, 'mod_interval' must be a
            # subset of 'number_set'.
            set_relation = SubsetEq(mod_interval, number_set).prove()
            return set_relation.derive_superset_membership(self)
            
        if number_set == Integer:
            return mod_int_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        if number_set == Natural:
            return mod_int_to_nat_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        if number_set == Real:
            return mod_real_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        raise NotImplementedError(
            "'Mod.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

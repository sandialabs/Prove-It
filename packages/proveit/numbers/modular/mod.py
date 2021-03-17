from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
# from proveit.numbers.number_sets import Integer, Real
from proveit import a, b
from proveit.numbers import NumberOperation

class Mod(NumberOperation):
    # operator of the Mod operation.
    _operator_ = Literal(string_format='mod ', latex_format=r'~\textup{mod}~',
                         theory=__file__)

    def __init__(self, dividend, divisor):
        Operation.__init__(self, Mod._operator_, (dividend, divisor))
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

    def deduce_in_interval(self, assumptions=USE_DEFAULTS):
        from . import mod_in_interval, mod_in_interval_c_o
        # from number_sets import deduce_in_integer, deduce_in_real
        try:
            # if the operands are integers, then we can deduce that
            # a mod b is an integer in the set {0,1,...,(b-1)}
            return mod_in_interval.instantiate(
                {a: self.dividend, b: self.divisor}, assumptions=assumptions)
        except BaseException:
            # if the operands are reals, then we can deduce that
            # a mod b is in half-open real interval [0, b)
            return mod_in_interval_c_o.instantiate(
                {a: self.dividend, b: self.divisor}, assumptions=assumptions)

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given Mod expression is in that number
        set using the appropriate closure theorem.
        '''
        from proveit.logic import InSet
        from proveit.numbers.modular import (
            mod_int_closure, mod_int_to_nat_closure, mod_real_closure)
        from proveit.numbers import Integer, Natural, Real

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checked_assumptions(assumptions)

        if number_set == Integer:
            return mod_int_closure.instantiate(
                {a: self.dividend, b: self.divisor}, assumptions=assumptions)

        if number_set == Natural:
            return mod_int_to_nat_closure.instantiate(
                {a: self.dividend, b: self.divisor}, assumptions=assumptions)

        if number_set == Real:
            return mod_real_closure.instantiate(
                {a: self.dividend, b: self.divisor}, assumptions=assumptions)

        raise NotImplementedError(
            "'Mod.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

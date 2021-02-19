from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit.numbers.number_sets import Real


class ModAbs(Operation):
    # operator of the ModAbs operation.
    _operator_ = Literal(string_format='ModAbs', theory=__file__)

    def __init__(self, value, divisor):
        Operation.__init__(self, ModAbs._operator_, (value, divisor))
        self.value = value
        self.divisor = divisor

    def string(self, **kwargs):
        return ('|' + self.value.string(fence=False) + '|_{mod ' +
                self.divisor.string(fence=False) + '}')

    def latex(self, **kwargs):
        return (r'\left|' + self.value.latex(fence=False)
                + r'\right|_{\textup{mod}\thinspace '
                  + self.divisor.latex(fence=False) + r'}')

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given ModAbs expression is in that
        number set using the appropriate closure theorem.
        '''
        from proveit import a, b
        from proveit.logic import InSet
        from proveit.numbers.modular import (
            mod_abs_int_closure, mod_abs_real_closure)
        from proveit.numbers import Integer, Real

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checked_assumptions(assumptions)

        if number_set == Integer:
            return mod_abs_int_closure.instantiate(
                {a: self.value, b: self.divisor}, assumptions=assumptions)
        if number_set == Real:
            return mod_abs_real_closure.instantiate(
                {a: self.value, b: self.divisor}, assumptions=assumptions)
        raise NotImplementedError(
            "'ModAbs.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

from proveit import (defaults, Literal, Operation, relation_prover)
from proveit.numbers import deduce_in_number_set, NumberOperation

class ModAbs(NumberOperation):
    # operator of the ModAbs operation.
    _operator_ = Literal(string_format='ModAbs', theory=__file__)

    def __init__(self, value, divisor, *, styles=None):
        Operation.__init__(self, ModAbs._operator_, (value, divisor),
                           styles=styles)
        self.value = value
        self.divisor = divisor

    def string(self, **kwargs):
        return ('|' + self.value.string(fence=False) + '|_{mod ' +
                self.divisor.string(fence=False) + '}')

    def latex(self, **kwargs):
        return (r'\left|' + self.value.latex(fence=False)
                + r'\right|_{\textup{mod}\thinspace '
                  + self.divisor.latex(fence=False) + r'}')

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given ModAbs expression is in that
        number set using the appropriate closure theorem.
        '''
        from proveit import a, b
        from proveit.numbers.modular import (
            mod_abs_int_closure, mod_abs_real_closure)
        from proveit.numbers import Integer, Real

        if number_set == Integer:
            return mod_abs_int_closure.instantiate(
                    {a: self.value, b: self.divisor})
        if number_set == Real:
            return mod_abs_real_closure.instantiate(
                {a: self.value, b: self.divisor})
        raise NotImplementedError(
            "'ModAbs.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most 
        restrictive standard number set we can readily know.
        '''
        operand_ns = deduce_number_set(self.operand).domain
        if operand_ns.includes(Integer):
            return self.deduce_in_number_set(Integer)
        else:
            return self.deduce_in_number_set(Real)

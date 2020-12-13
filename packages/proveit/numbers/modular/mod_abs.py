from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit.numbers.number_sets import Real

class ModAbs(Operation):
    # operator of the ModAbs operation.
    _operator_ = Literal(stringFormat='ModAbs', theory=__file__)

    def __init__(self, value, divisor):
        Operation.__init__(self, ModAbs._operator_, (value, divisor))
        self.value = value
        self.divisor = divisor

    def string(self, **kwargs):
        return ('|'+self.value.string(fence=False)+'|_{mod ' +
                self.divisor.string(fence=False) + '}')

    def latex(self, **kwargs):
        return (  r'\left|'+self.value.latex(fence=False)
                + r'\right|_{\textup{mod}\thinspace '
                + self.divisor.latex(fence=False) + r'}')

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given ModAbs expression is in that
        number set using the appropriate closure theorem.
        '''
        from proveit._common_ import a, b
        from proveit.logic import InSet
        from proveit.numbers.modular._theorems_ import (
                modAbsIntClosure, modAbsRealClosure)
        from proveit.numbers import Integer, Real

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integer:
            return modAbsIntClosure.instantiate(
                    {a:self.value, b:self.divisor}, assumptions=assumptions)

        if number_set == Real:
            return modAbsRealClosure.instantiate(
                    {a:self.value, b:self.divisor}, assumptions=assumptions)

        msg = ("'ModAbs.deduceInNumberSet()' not implemented for "
               "the %s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)

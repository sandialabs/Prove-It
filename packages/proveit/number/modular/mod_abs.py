from proveit import Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit.number.sets import Reals

class ModAbs(Operation):
    # operator of the ModAbs operation.
    _operator_ = Literal(stringFormat='ModAbs', context=__file__)
    
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

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == Reals:
            return _theorems_.modAbsRealClosure

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integers, Reals, etc),
        attempt to prove that the given ModAbs expression is in that
        number set using the appropriate closure theorem.
        Created: 3/25/2020 by wdc, based on the same method in the Add,
                 Exp, and Abs classes.
        Last modified: 3/25/2020 by wdc. Creation
        Once established, these authorship notations can be deleted.
        '''
        from proveit._common_ import a, b
        from proveit.logic import InSet
        from proveit.number.modular._theorems_ import (
                modAbsIntClosure, modAbsRealClosure)
        from proveit.number import Integers, Reals

        if number_set == Integers:
            return modAbsIntClosure.specialize(
                    {a:self.value, b:self.divisor}, assumptions=assumptions)

        if number_set == Reals:
            return modAbsRealClosure.specialize(
                    {a:self.value, b:self.divisor}, assumptions=assumptions)

        msg = ("'ModAbs.deduceInNumberSet()' not implemented for "
               "the %s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)

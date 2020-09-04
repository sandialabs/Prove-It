from proveit import defaults, USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.number import num
from proveit._common_ import n, x, y

class EnumMembership(Membership):
    '''
    Defines methods that apply to membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def sideEffects(self, knownTruth):
        '''
        Unfold the enumerated set membership, and in boolean as
        a side-effect.
        '''
        yield self.unfold


    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [(element=x) or (element=y) or ..], derive and return
        [element in {x, y, ..}].
        '''
        from ._theorems_ import foldSingleton, fold
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return foldSingleton.instantiate(
                {x:self.element, y:enum_elements[0]}, assumptions=assumptions)
        else:
            return fold.instantiate({n:num(len(enum_elements)), x:self.element, y:enum_elements}, assumptions=assumptions)

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        From the EnumMembership object [element in {a, ..., n}],
        deduce and return:
        |– [element in {x, y, ..}] = [(element=a) or ... or (element=a)]
        '''
        from ._axioms_ import enumSetDef
        from ._theorems_ import singletonDef
        enum_elements = self.domain.elements

        if len(enum_elements) == 1:
            return singletonDef.instantiate(
                {x:self.element, y:enum_elements[0]}, assumptions=assumptions)
        else:
            return enumSetDef.instantiate({n:num(len(enum_elements)), x:self.element, y:enum_elements}, assumptions=assumptions)

    def deriveInSingleton(self, expression, assumptions=USE_DEFAULTS):
        # implemented by JML 6/28/19
        from proveit.logic import TRUE, FALSE
        from ._theorems_ import inSingletonEvalFalse, inSingletonEvalTrue
        if expression.rhs == FALSE:
            return inSingletonEvalFalse.instantiate({x:expression.lhs.element, y:expression.lhs.domain.elements[0]}, assumptions=assumptions)
        elif expression.rhs == TRUE:
            return inSingletonEvalTrue.instantiate({x:expression.lhs.element, y:expression.lhs.domain.elements[0]}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in {x, y, ..}], derive and return [(element=x) or (element=y) or ..].
        '''
        from ._theorems_ import unfoldSingleton, unfold
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return unfoldSingleton.instantiate({x:self.element, y:enum_elements[0]},assumptions=assumptions)
        else:
            return unfold.instantiate({n:num(len(enum_elements)), x:self.element, y:enum_elements}, assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import inSingletonIsBool, inEnumSetIsBool
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return inSingletonIsBool.instantiate(
                {x:self.element, y:enum_elements[0]}, assumptions=assumptions)
        else:
            return inEnumSetIsBool.instantiate(
                {n:num(len(enum_elements)), x:self.element, y:enum_elements},
                assumptions=assumptions)

class EnumNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def sideEffects(self, knownTruth):
        '''
        Unfold the enumerated set nonmembership, and ....
        '''
        yield self.unfold

    def equivalence(self):
        '''
        Deduce and return
        |– [element not in {a, ..., n}] =
           [(element != a) and ... and (element != n)]
        where self is the EnumNonmembership object.
        '''
        from ._theorems_ import notInSingletonEquiv, nonmembershipEquiv
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return notInSingletonEquiv.instantiate(
                    {x:self.element, y:enum_elements})
        else:
            return nonmembershipEquiv.instantiate(
                    {n:num(len(enum_elements)), x:self.element,
                    y:enum_elements})

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element != a] AND ... AND [element != n],
        derive and return [element not in {a, b, ..., n}],
        where self is the EnumNonmembership object.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)
        from ._theorems_ import nonmembershipFold
        enum_elements = self.domain.elements
        element = self.element
        operands = self.domain.operands
        return nonmembershipFold.instantiate(
            {n:num(len(enum_elements)), x:self.element, y:enum_elements},
            assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element not-in {a, b, ..., n}], derive and return
        [(element!=a) AND (element!=b) AND ... AND (element!=n)].
        '''
        from ._theorems_ import (
                nonmembershipUnfold, nonmembershipUnfoldSingleton)
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return nonmembershipUnfoldSingleton.instantiate(
                    {x:self.element, y:enum_elements[0]},
                    assumptions=assumptions)
        else:
            return nonmembershipUnfold.instantiate(
                {n:num(len(enum_elements)), x:self.element, y:enum_elements},
                assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import notInSingletonIsBool, notInEnumSetIsBool
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return notInSingletonIsBool.instantiate(
                {x:self.element, y:enum_elements[0]}, assumptions=assumptions)
        else:
            # return nonmembershipEquiv.instantiate(
            #     {n:num(len(enum_elements)), x:self.element, y:enum_elements})
            return notInEnumSetIsBool.instantiate(
                {n:num(len(enum_elements)), x:self.element, y:enum_elements})

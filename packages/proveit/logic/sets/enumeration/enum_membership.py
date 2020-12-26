from proveit import defaults, USE_DEFAULTS, ExprTuple
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit import a, b, c, m, n, x, y


class EnumMembership(Membership):
    '''
    Defines methods that apply to membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
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
        from proveit import ProofFailure
        from . import fold_singleton, in_enumerated_set, fold
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return fold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
        else:
            try:
                idx = self.domain.operands.index(self.element)
                _a = self.domain.operands[:idx]
                _b = self.element
                _c = self.domain.operands[idx + 1:]
                _m = _a.num_elements(assumptions=assumptions)
                _n = _c.num_elements(assumptions=assumptions)
                return in_enumerated_set.instantiate(
                    {m: _m, n: _n, a: _a, b: _b, c: _c}, assumptions=assumptions)
            except (ProofFailure, ValueError):
                _y = enum_elements
                _n = _y.num_elements(assumptions=assumptions)
                return fold.instantiate({n: _n, x: self.element, y:_y}, 
                                        assumptions=assumptions)

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        From the EnumMembership object [element in {a, ..., n}],
        deduce and return:
        |– [element in {x, y, ..}] = [(element=a) or ... or (element=a)]
        '''
        from . import enum_set_def
        from . import singleton_def
        enum_elements = self.domain.elements

        if enum_elements.is_single():
            return singleton_def.instantiate(
                {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
        else:
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return enum_set_def.instantiate({n: _n, x: self.element, y: _y}, 
                                            assumptions=assumptions)

    def derive_in_singleton(self, expression, assumptions=USE_DEFAULTS):
        # implemented by JML 6/28/19
        from proveit.logic import TRUE, FALSE
        from . import in_singleton_eval_false, in_singleton_eval_true
        if expression.rhs == FALSE:
            return in_singleton_eval_false.instantiate(
                {x: expression.lhs.element, y: expression.lhs.domain.elements[0]}, assumptions=assumptions)
        elif expression.rhs == TRUE:
            return in_singleton_eval_true.instantiate(
                {x: expression.lhs.element, y: expression.lhs.domain.elements[0]}, assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in {x, y, ..}], derive and return [(element=x) or (element=y) or ..].
        '''
        from . import unfold_singleton, unfold
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return unfold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
        else:
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return unfold.instantiate({n: _n, x: self.element, y: _y}, 
                                      assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        from . import in_singleton_is_bool, in_enum_set_is_bool
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return in_singleton_is_bool.instantiate(
                {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
        else:
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return in_enum_set_is_bool.instantiate(
                    {n: _n, x: self.element, y: _y}, 
                    assumptions=assumptions)


class EnumNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set nonmembership, and ....
        '''
        yield self.unfold

    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return
        |– [element not in {a, ..., n}] =
           [(element != a) and ... and (element != n)]
        where self is the EnumNonmembership object.
        '''
        from . import not_in_singleton_equiv, nonmembership_equiv
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return not_in_singleton_equiv.instantiate(
                {x: self.element, y: enum_elements})
        else:
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return nonmembership_equiv.instantiate(
                    {n: _n, x: self.element, y: _y}, 
                    assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [element != a] AND ... AND [element != n],
        derive and return [element not in {a, b, ..., n}],
        where self is the EnumNonmembership object.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checked_assumptions(assumptions)
        from . import nonmembership_fold
        enum_elements = self.domain.elements
        return nonmembership_fold.instantiate(
            {n: num(len(enum_elements)), x: self.element, y: enum_elements},
            assumptions=assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element not-in {a, b, ..., n}], derive and return
        [(element!=a) AND (element!=b) AND ... AND (element!=n)].
        '''
        from . import (
            nonmembership_unfold, nonmembership_unfold_singleton)
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return nonmembership_unfold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]},
                assumptions=assumptions)
        else:
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return nonmembership_unfold.instantiate(
                {n: _n, x: self.element, y: _y}, 
                assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        from . import not_in_singleton_is_bool, not_in_enum_set_is_bool
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return not_in_singleton_is_bool.instantiate(
                {x: self.element, y: enum_elements[0]}, assumptions=assumptions)
        else:
            # return nonmembership_equiv.instantiate(
            #     {n:num(len(enum_elements)), x:self.element, y:enum_elements})
            _y = enum_elements
            _n = _y.num_elements(assumptions=assumptions)
            return not_in_enum_set_is_bool.instantiate(
                {n: _n, x: self.element, y: _y},
                assumptions=assumptions)

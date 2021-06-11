from proveit import (defaults, USE_DEFAULTS, ExprTuple,
                     prover, equality_prover, relation_prover)
from proveit.logic import Membership, Nonmembership
from proveit.numbers import num
from proveit import a, b, c, m, n, x, y


class EnumMembership(Membership):
    '''
    Defines methods that apply to membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Membership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership, and in boolean as
        a side-effect.
        '''
        yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        From [(element=x) or (element=y) or ..], derive and return
        [element in {x, y, ..}].
        '''
        from proveit import ProofFailure
        from . import fold_singleton, in_enumerated_set, fold
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return fold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]})
        else:
            try:
                idx = self.domain.operands.index(self.element)
                _a = self.domain.operands[:idx]
                _b = self.element
                _c = self.domain.operands[idx + 1:]
                _m = _a.num_elements()
                _n = _c.num_elements()
                return in_enumerated_set.instantiate(
                    {m: _m, n: _n, a: _a, b: _b, c: _c})
            except (ProofFailure, ValueError):
                _y = enum_elements
                _n = _y.num_elements()
                return fold.instantiate({n: _n, x: self.element, y:_y})

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
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
                    {x: self.element, y: enum_elements[0]}, auto_simplify=False)
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return enum_set_def.instantiate(
                    {n: _n, x: self.element, y: _y}, auto_simplify=False)

    @prover
    def derive_in_singleton(self, expression, **defaults_config):
        # implemented by JML 6/28/19
        # What is the purpose of this method? does this do exactly?
        # Provide some examples?
        from proveit.logic import TRUE, FALSE
        from . import in_singleton_eval_false, in_singleton_eval_true
        if expression.rhs == FALSE:
            return in_singleton_eval_false.instantiate(
                    {x: expression.lhs.element,
                    y: expression.lhs.domain.elements[0]},
                    auto_simplify=False)
        elif expression.rhs == TRUE:
            return in_singleton_eval_true.instantiate(
                    {x: expression.lhs.element,
                    y: expression.lhs.domain.elements[0]},
                    auto_simplify=False)

    @prover
    def unfold(self, **defaults_config):
        '''
        From [element in {x, y, ..}], derive and return
        [(element=x) or (element=y) or ..]. The derivation only works
        if the original membership claim is known to be true or
        provably true (possible based on assumptions). Notice that
        this is similar to but quite different from the definition()
        method. For example,
            Set(B,C,D).membership_object(C).unfold()
        returns:
            |- (C = B) OR (C = C) OR (C = D).
        As another example,
            Set(one, two, three).membership_object(three).unfold()
        returns
            |- (3 = 1) OR (3 = 2) OR (3 = 3).
        but Set(one, two, three).membership_object(four).unfold()
        gives an error.
        '''
        from . import unfold_singleton, unfold
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return unfold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]},
                auto_simplify=False)
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return unfold.instantiate(
                    {n: _n, x: self.element, y: _y}, 
                    auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import in_singleton_is_bool, in_enum_set_is_bool
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return in_singleton_is_bool.instantiate(
                {x: self.element, y: enum_elements[0]})
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return in_enum_set_is_bool.instantiate(
                    {n: _n, x: self.element, y: _y})


class EnumNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an enumerated set.
    '''

    def __init__(self, element, domain):
        Nonmembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set nonmembership, and ....
        '''
        yield self.unfold

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
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
                {x: self.element, y: enum_elements[0]})
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return nonmembership_equiv.instantiate(
                    {n: _n, x: self.element, y: _y})

    @prover
    def conclude(self, **defaults_config):
        '''
        From [element != a] AND ... AND [element != n],
        derive and return [element not in {a, b, ..., n}],
        where self is the EnumNonmembership object.
        '''
        # among other things, convert any assumptions=None
        # to assumptions=()
        from . import nonmembership_fold
        enum_elements = self.domain.elements
        _y = enum_elements
        _n = _y.num_elements()
        return nonmembership_fold.instantiate(
            {n: _n, x: self.element, y: _y})

    @prover
    def unfold(self, **defaults_config):
        '''
        From [element not-in {a, b, ..., n}], derive and return
        [(element!=a) AND (element!=b) AND ... AND (element!=n)].
        For example,
        Set(B,C,D).nonmembership_object(A).unfold(
                assumptions=[NotInSet(A, Set(B, C, D))])
        returns:
        A notin {B, C, D} |- (A != B) AND (A != C) AND (A != D)
        '''
        from . import (
            nonmembership_unfold, nonmembership_unfold_singleton)
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return nonmembership_unfold_singleton.instantiate(
                {x: self.element, y: enum_elements[0]},
                auto_simplify=False)
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return nonmembership_unfold.instantiate(
                {n: _n, x: self.element, y: _y},
                auto_simplify=False)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        from . import not_in_singleton_is_bool, not_in_enum_set_is_bool
        enum_elements = self.domain.elements
        if enum_elements.is_single():
            return not_in_singleton_is_bool.instantiate(
                {x: self.element, y: enum_elements[0]})
        else:
            _y = enum_elements
            _n = _y.num_elements()
            return not_in_enum_set_is_bool.instantiate(
                {n: _n, x: self.element, y: _y})

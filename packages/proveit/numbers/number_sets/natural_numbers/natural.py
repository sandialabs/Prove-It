import proveit
from proveit import prover, maybe_fenced_string
from proveit.numbers.number_sets.number_set import NumberSet
from proveit import n


class NaturalSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(self, 'Natural', r'\mathbb{N}', 
                           theory=__file__, styles=styles)

    def membership_object(self, element):
        from .natural_membership import NaturalMembership    
        return NaturalMembership(element, self)


class NaturalPosSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(
            self, 'NaturalPos', r'\mathbb{N}^+',
            theory=__file__, styles=styles)

    def membership_object(self, element):
        from .natural_membership import NaturalPosMembership    
        return NaturalPosMembership(element)

    def string(self, **kwargs):
        inner_str = NumberSet.string(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of
        # when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)

    def latex(self, **kwargs):
        inner_str = NumberSet.latex(self, **kwargs)
        # only fence if force_fence=True (nested exponents is an example of
        # when fencing must be forced)
        kwargs['fence'] = kwargs['force_fence'] if 'force_fence' in kwargs else False
        return maybe_fenced_string(inner_str, **kwargs)



if proveit.defaults.automation:
    # Import some fundamental theorems without quantifiers that are
    # imported when automation is used.
    from . import nat_pos_within_nat

# if proveit.defaults.automation:
#     try:
#         # Import some fundamental theorems without quantifiers that are
#         # imported when automation is used.
#         # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
#         from . import nat_pos_within_nat, nat_within_int, nat_pos_within_int
#     except:
#         pass

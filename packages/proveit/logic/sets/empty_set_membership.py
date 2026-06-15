from proveit import x, defaults, prover
from proveit.logic import SetMembership, SetNonmembership

class EmptySetMembership(SetMembership):
    '''
    Defines methods that apply to membership in the empty set
    (EmptySet). Technically, nothing is a member of the empty set;
    thus deductions to the contrary allow us to disprove assumptions
    that lead to such a deduction, and an empty set membership
    assumption should allow us to conclude anything.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def _readily_provable(self):
        '''
        Membership in the empty set is always FALSE, and thus is
        never readily provable, regardless of the element in question.
        '''
        return False

    def _readily_disprovable(self):
        '''
        Membership in the empty set is always FALSE, and thus is
        always readily disprovable, regardless of the element in
        question.
        '''
        return True

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From self = [x in EmptySet], derive and return FALSE.
        '''
        from . import empty_set_contradiction
        _x_sub = self.element
        return empty_set_contradiction.instantiate({x: _x_sub})

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From self = [x in EmptySet], derive conclusion, provided that
        the negation of conclusion implies [x in EmptySet] (because
        [x in EmptySet] should never be true).
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self.expr, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''
        From self = x in EmptySet, derive the negated conclusion,
        provided that the conclusion implies x in EmptySet (because
        x in EmptySet should never be true).
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self.expr, conclusion)

    def readily_in_bool(self):
        return True # EmptySetMembership is always boolean

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import empty_set_membership_is_bool
        _x_sub = self.element
        return empty_set_membership_is_bool.instantiate({x: _x_sub})


class EmptySetNonmembership(SetNonmembership):
    '''
    Defines methods that apply to non-membership in the empty set
    (EmptySet). Non-membership, i.e., x NotIn EmptySet, is always
    TRUE.
    '''

    def __init__(self, element, domain):
        SetNonmembership.__init__(self, element, domain)
        self.domain = domain

    def _readily_provable(self):
        '''
        The Nonmembership is always TRUE, and thus is always readily
        provable, regardless of the element in question.
        '''
        return True

    def _readily_disprovable(self):
        '''
        The Nonmembership is always TRUE, and thus is never readily
        disprovable, regardless of the element in question.
        '''
        return False

    @prover
    def conclude(self, **defaults_config):
        '''
        Empty set non-membership is always True, regardless of the
        element being considered. From self = [elem NotIn EmptySet],
        return |- [elem Notin EmptySet].
        '''
        from proveit.logic.sets import nothing_is_in_empty
        _x_sub = self.element
        return nothing_is_in_empty.instantiate({x: _x_sub})

    def readily_in_bool(self):
        return True # EmptySetNonmembership is always boolean

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import empty_set_nonmembership_is_bool
        _x_sub = self.element
        return empty_set_nonmembership_is_bool.instantiate({x: _x_sub})

# General Functions Related to Empty Set Membership

@prover
def affirm_via_empty_set_contradiction(
        claim_to_affirm, elem = None, **defaults_config):
    '''
    Derive and return the 'claim_to_affirm', provided
    that (1) claim_to_affirm is Boolean and (2) the negation of
    claim_to_affirm implies [elem in EmptySet] (because x in EmptySet
    is FALSE for all x).
    '''
    from . import empty_set_contradiction
    from proveit.logic import Not
    if elem is None: elem = x
    extended_assumptions = defaults.assumptions + (Not(claim_to_affirm),)
    contradiction = empty_set_contradiction.instantiate(
            {x:elem}, assumptions = extended_assumptions)
    contradiction_as_impl = contradiction.as_implication(Not(claim_to_affirm))
    return contradiction_as_impl.deny_antecedent(
            assumptions = extended_assumptions)

@prover
def deny_via_empty_set_contradiction(
        claim_to_deny, elem = None, **defaults_config):
    '''
    Derive and return the negation of the 'claim_to_deny', provided
    that (1) claim_to_deny is Boolean and (2) claim_to_deny implies
    [elem in EmptySet](because x in EmptySet is FALSE for all x).
    '''
    from . import empty_set_contradiction
    if elem is None:
        elem = x
    extended_assumptions = defaults.assumptions + (claim_to_deny,)
    contradiction = empty_set_contradiction.instantiate(
            {x:elem}, assumptions = extended_assumptions)
    contradiction_as_impl = contradiction.as_implication(claim_to_deny)
    return contradiction_as_impl.deny_antecedent(
            assumptions = extended_assumptions)

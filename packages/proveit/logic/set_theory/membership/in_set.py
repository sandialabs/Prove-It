from proveit import Literal, Operation, USE_DEFAULTS

class InSet(Operation):
    # operator of the InSet operation
    _operator_ = Literal(stringFormat='in',
                         latexFormat=r'\in',
                         context=__file__)

    # maps elements to InSet Judgments.
    # For example, map x to (x in S) if (x in S) is a Judgment.
    knownMemberships = dict()

    def __init__(self, element, domain):
        Operation.__init__(self, InSet._operator_, (element, domain))
        self.element = self.operands[0]
        self.domain = self.operands[1]
        if hasattr(self.domain, 'membershipObject'):
            self.membershipObject = self.domain.membershipObject(element)
            if not isinstance(self.membershipObject, Membership):
                raise TypeError("The 'membershipObject' of %s is a %s which "
                                "is not derived from %s as it should be."
                                %(self.domain, self.membershipObject.__class__,
                                  Membership))

    def __dir__(self):
        '''
        If the domain has a 'membershipObject' method, include methods from the
        object it generates.
        '''
        if 'membershipObject' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) + dir(self.membershipObject)))
        else:
            return sorted(self.__dict__.keys())

    def __getattr__(self, attr):
        '''
        If the domain has a 'membershipObject' method, include methods from the
        object it generates.
        '''
        if 'membershipObject' in self.__dict__:
            return getattr(self.membershipObject, attr)
        raise AttributeError

    def sideEffects(self, judgment):
        '''
        Store the proven membership in knownMemberships.
        If the domain has a 'membershipObject' method, side effects
        will also be generated from the 'sideEffects' object that it generates.
        '''
        InSet.knownMemberships.setdefault(self.element, set()).add(judgment)
        if hasattr(self, 'membershipObject'):
            for sideEffect in self.membershipObject.sideEffects(judgment):
                yield sideEffect

    def negationSideEffects(self, judgment):
        '''
        Fold Not(x in S) as (x not-in S) as an automatic side-effect.
        '''
        yield self.deduceNotIn

    def deduceNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from .not_in_set import NotInSet
        yield NotInSet(self.element, self.domain).concludeAsFolded(assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this membership statement is in the set of
        Booleans (i.e. membership is True or False).
        '''
        if hasattr(self, 'membershipObject'):
            return self.membershipObject.deduceInBool(assumptions)
        raise AttributeError

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is in the domain.
        First, see if it is known to be contained in a known subset of the
        domain.  Next, check if the element has a known simplification; if so,
        try to derive membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.membershipObject.conclude(..)' method to prove
        the membership.  If that fails, try simplifying the element
        again, this time using automation to push the simplification through
        if possible.
        '''
        from proveit.logic import Equals, SubsetEq
        from proveit import ProofFailure
        from proveit.logic import SimplificationError

        # See if the membership is already known.
        if self.element in InSet.knownMemberships:
            for knownMembership in InSet.knownMemberships[self.element]:
                if knownMembership.isSufficient(assumptions):
                    # x in R is a judgment; if we know that R subseteq S,
                    # or R = S we are done.
                    eqRel = Equals(knownMembership.domain, self.domain)
                    if eqRel.proven(assumptions):
                        return eqRel.subRightSideInto(knownMembership.innerExpr().domain)
                    subRel = SubsetEq(knownMembership.domain, self.domain)
                    if subRel.proven(assumptions):
                        # S is a superset of R, so now we can prove x in S.
                        return subRel.deriveSupersetMembership(self.element,
                                                                assumptions)

        # No known membership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(assumptions,
                                                              automation=False)
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None # reflection doesn't count
        except SimplificationError:
            elem_simplification = None

        if elem_simplification is None:
            # Let's try harder to simplify the element.
            try:
                elem_simplification = self.element.simplification(assumptions)
                if elem_simplification.lhs == elem_simplification.rhs:
                    elem_simplification = None # reflection doesn't count
            except SimplificationError:
                pass

        # If the element simplification succeeded, prove the membership
        # via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_membership = InSet(simple_elem, self.domain).prove(assumptions)
            inner_expr = simple_membership.innerExpr().element
            return elem_simplification.subLeftSideInto(inner_expr, assumptions)
        else:
            # Unable to simplify the element.  Try to conclude via
            # the 'membershipObject' if there is one.
            if hasattr(self, 'membershipObject'):
                return self.membershipObject.conclude(assumptions)

            raise ProofFailure(self, assumptions,
                               "Unable to conclude automatically; "
                               "the domain, %s, has no 'membershipObject' "
                               "method with a strategy for proving "
                               "membership."%self.domain)

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Attempt to form evaluation of whether (element in domain) is
        TRUE or FALSE.  If the domain has a 'membershipObject' method,
        attempt to use the 'equivalence' method from the object it generates.
        '''
        from proveit.logic import TRUE, NotInSet
        # try an 'equivalence' method (via the membership object)
        equiv = self.membershipObject.equivalence(assumptions)
        rhs_eval = equiv.rhs.evaluation(assumptions=assumptions)
        evaluation = equiv.applyTransitivity(rhs_eval, assumptions=assumptions)
        # try also to evaluate this by deducing membership
        # or non-membership in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'membershipObject'):
                    self.membershipObject.conclude(assumptions=assumptions)
            else:
                notInDomain = NotInSet(self.element, self.domain)
                if hasattr(notInDomain, 'nonmembershipObject'):
                    notInDomain.nonmembershipObject.conclude(assumptions=assumptions)
        except:
            pass
        return evaluation

class Membership:
    def __init__(self, element):
        '''
        Base class for any 'membership object' returned by a domain's
        'membershipObject' method.
        '''
        self.element = element

    def sideEffects(self, judgment):
        raise NotImplementedError("Membership object, %s, has no 'sideEffects' method implemented"%str(self.__class__))

    def conclude(self, assumptions):
        raise NotImplementedError("Membership object, %s, has no 'conclude' method implemented"%str(self.__class__))

    def equivalence(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Membership object, %s, has no 'equivalence' method implemented"%str(self.__class__))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Membership object, %s, has no 'deduceInBool' method implemented"%str(self.__class__))

from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import x, S

class NotInSet(Operation):
    # operator of the NotInSet operation
    _operator_ = Literal(stringFormat='not-in',
                         latexFormat=r'\notin',
                         context=__file__)

    # maps elements to NotInSet KnownTruths.
    # For example, map x to (x \nin S) if (x \nin S) is a KnownTruth.
    knownNonmemberships = dict()

    def __init__(self, element, domain):
        Operation.__init__(self, NotInSet._operator_, (element, domain))
        self.element = self.operands[0]
        self.domain = self.operands[1]
        if hasattr(self.domain, 'nonmembershipObject'):
            self.nonmembershipObject = self.domain.nonmembershipObject(element)
            if not isinstance(self.nonmembershipObject, Nonmembership):
                raise TypeError("The 'nonmembershipObject' of %s is a %s which "
                                "is not derived from %s as it should be."
                                %(self.domain,
                                  self.nonmembershipObject.__class__,
                                  Nonmembership))

    def __dir__(self):
        '''
        If the domain has a 'nonmembershipObject' method, include methods from the
        object it generates (also 'unfold' which defaults as 'unfoldNotIn' if it
        isn't defined in 'nonmembershipObject').
        '''
        if 'nonmembershipObject' in self.__dict__:
            return sorted(set(list(self.__dict__.keys()) + dir(self.membershipObject)))
        else:
            return sorted(list(self.__dict__.keys()) + 'unfold')

    def __getattr__(self, attr):
        '''
        If the domain has a 'nonmembershipObject' method, include methods from the
        object it generates (also 'unfold' defaults as 'unfoldNotIn' if it isn't
        defined in 'nonmembershipObject').
        '''
        if 'nonmembershipObject' in self.__dict__:
            return getattr(self.nonmembershipObject, attr)
        elif attr=='unfold':
            return self.unfoldNotIn # the default 'unfold' method
        raise AttributeError

    def sideEffects(self, knownTruth):
        '''
        Store the proven non-membership in knownNonmemberships.
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembershipObject' method, side effects
        will also be generated from the 'sideEffects' object that it generates.
        '''
        NotInSet.knownNonmemberships.setdefault(self.element, set()).add(knownTruth)
        yield self.unfoldNotIn
        if hasattr(self, 'nonmembershipObject'):
            for sideEffect in self.nonmembershipObject.sideEffects(knownTruth):
                yield sideEffect

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        '''
        from ._theorems_ import notInSetInBool
        from proveit._common_ import x, S
        return notInSetInBool.specialize({x:self.element, S:self.domain},
                                         assumptions=assumptions)

    def unfoldNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        From (x \notin y), derive and return Not(x \in y).
        '''
        from ._theorems_ import unfoldNotInSet
        return unfoldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is in the domain.
        First, see if it is not contained in a superset of the domain.
        Next, check if the element has a known simplification; if so,
        try to derive non-membership via this simplification.
        If there isn't a known simplification, next try to call
        the 'self.domain.nonmembershipObject.conclude(..)' method to prove
        the non-membership.  If that fails, try simplifying the element
        again, this time using automation to push the simplification through
        if possible.
        As a last resort, try 'concludeAsFolded'.
        '''
        from proveit.logic import SupersetEq, InSet
        from proveit import ProofFailure
        from proveit.logic import SimplificationError


        # See if the membership is already known.
        if self.element in NotInSet.knownNonmemberships:
            for knownNonmembership in NotInSet.knownNonmemberships[self.element]:
                if knownNonmembership.isSufficient(assumptions):
                    # x not in R is a known truth; if we know that
                    # R supseteq S, we are done.
                    supRel = SupersetEq(knownNonmembership.domain,
                                        self.domain)
                    if supRel.proven(assumptions):
                        # S is a subset of R, so now we can prove x not in S.
                        return supRel.deriveSubsetNonMembership(self.element,
                                                                assumptions)
        # No known membership works.  Let's see if there is a known
        # simplification of the element before trying anything else.
        try:
            elem_simplification = self.element.simplification(assumptions,
                                                              automation=True)
            if elem_simplification.lhs == elem_simplification.rhs:
                elem_simplification = None # reflection doesn't count
        except SimplificationError:
            elem_simplification = None

        # If the element simplification succeeded, prove the membership
        # via the simplified form of the element.
        if elem_simplification is not None:
            simple_elem = elem_simplification.rhs
            simple_nonmembership = NotInSet(simple_elem, self.domain).prove(assumptions)
            inner_expr = simple_nonmembership.innerExpr().element
            return elem_simplification.subLeftSideInto(inner_expr, assumptions)
        else:
            # If it has a 'nonmembershipObject', try to conclude
            # nonmembership using that.
            if hasattr(self, 'nonmembershipObject'):
                return self.nonmembershipObject.conclude(assumptions)
            else:
                # Otherwise, attempt to conclude via Not(x in S)
                return self.concludeAsFolded(assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from ._theorems_ import foldNotInSet
        return foldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        '''
        Attempt to form evaluation of whether (element not in domain) is
        TRUE or FALSE.  If the domain has a 'membershipObject' method,
        attempt to use the 'equivalence' method from the object it generates.
        '''
        from proveit.logic import Equals, TRUE, InSet
        # try an 'equivalence' method (via the nonmembership object)
        equiv = self.nonmembershipObject.equivalence(assumptions)
        val = equiv.evaluation(assumptions).rhs
        evaluation = Equals(equiv, val).prove(assumptions=assumptions)
        # try also to evaluate this by deducing membership or non-membership
        # in case it generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                if hasattr(self, 'nonmembershipObject'):
                    self.nonmembershipObject.conclude(assumptions=assumptions)
            else:
                inDomain = In(self.element, self.domain)
                if hasattr(inDomain, 'membershipObject'):
                    inDomain.membershipObject.conclude(assumptions=assumptions)
        except:
            pass
        return evaluation

class Nonmembership:
    '''
    Base class for any 'nonmembership object' return by a domain's
    'nonmembershipObject' method.
    '''
    def __init__(self, element):
        self.element = element

    def sideEffects(self, knownTruth):
        raise NotImplementedError("Nonmembership object has no 'sideEffects' method implemented")

    def conclude(self, assumptions):
        raise NotImplementedError("Nonmembership object has no 'conclude' method implemented")

    def equivalence(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Nonmembership object has no 'equivalence' method implemented")

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Nonmembership object has no 'deduceInBool' method implemented")

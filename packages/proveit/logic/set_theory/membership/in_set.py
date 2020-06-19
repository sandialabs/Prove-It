from proveit import Literal, Operation, USE_DEFAULTS

class InSet(Operation):
    # operator of the InSet operation
    _operator_ = Literal(stringFormat='in',
                         latexFormat=r'\in',
                         context=__file__)    
    
    # maps elements to InSet KnownTruths.
    # For exmple, map x to (x in S) if (x in S) is a KnownTruth.
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
    
    def sideEffects(self, knownTruth):
        '''
        Store the proven membership in knownMemberships.
        If the domain has a 'membershipObject' method, side effects
        will also be generated from the 'sideEffects' object that it generates.
        '''
        InSet.knownMemberships.setdefault(self.element, set()).add(knownTruth)
        if hasattr(self, 'membershipObject'):
            for sideEffect in self.membershipObject.sideEffects(knownTruth):
                yield sideEffect

    def negationSideEffects(self, knownTruth):
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
        First, see if it is contained in a subset of the domain.  
        If that fails and the domain has a 'membershipObject' method,
        try calling 'conclude' on the object it generates.
        try conclude(self, assumptions, minimal_automation=False)
        '''
        from proveit.logic import SubsetEq
        from proveit import ProofFailure
        # try to conclude some x in S
        if self.element in InSet.knownMemberships:
            for knownMembership in InSet.knownMemberships[self.element]:
                if knownMembership.isSufficient(assumptions):
                    try:
                        # x in R is a known truth; if we can proof R subseteq S, we are done.
                        subsetRelation = SubsetEq(knownMembership.domain, self.domain).prove(assumptions)
                        # S is a superset of R, so now we can prove x in S.
                        return subsetRelation.deriveSupsersetMembership(self.element, assumptions=assumptions)
                    except ProofFailure:
                        pass # no luck, keep trying
        # could not prove it through a subset relationship,
        # now try to use a MembershipObject
        if hasattr(self, 'membershipObject'):
            return self.membershipObject.conclude(assumptions)
              
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to form evaluation of whether (element in domain) is
        TRUE or FALSE.  If the domain has a 'membershipObject' method,
        attempt to use the 'equivalence' method from the object it generates.
        '''
        from proveit.logic import Equals, TRUE, NotInSet
        # try an 'equivalence' method (via the membership object)
        equiv = self.membershipObject.equivalence(assumptions)
        val = equiv.evaluation(assumptions).rhs
        evaluation = Equals(equiv, val).prove(assumptions=assumptions)
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

    def sideEffects(self, knownTruth):
        raise NotImplementedError("Membership object, %s, has no 'sideEffects' method implemented"%str(self.__class__))

    def conclude(self, assumptions):
        raise NotImplementedError("Membership object, %s, has no 'conclude' method implemented"%str(self.__class__))
    
    def equivalence(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Membership object, %s, has no 'equivalence' method implemented"%str(self.__class__))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        raise NotImplementedError("Membership object, %s, has no 'deduceInBool' method implemented"%str(self.__class__))


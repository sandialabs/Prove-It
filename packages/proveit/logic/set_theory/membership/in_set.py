from proveit import Literal, Operation, USE_DEFAULTS

class InSet(Operation):
    # operator of the InSet operation
    _operator_ = Literal(stringFormat='in', latexFormat=r'\in', context=__file__)    
    
    # maps elements to InSet KnownTruths.  For exmple, map x to (x in S) if (x in S) is a KnownTruth.
    knownMemberships = dict()
    
    def __init__(self, element, domain):
        Operation.__init__(self, InSet._operator_, (element, domain))
        self.element = self.operands[0]
        self.domain = self.operands[1]
    
    def sideEffects(self, knownTruth):
        '''
        Store the proven membership in knownMemberships.
        If the domain has a 'membershipSideEffects' method, it will be called
        and given the element and knownTruth.  Also, the 'unfold' method is called.
        '''
        InSet.knownMemberships.setdefault(self.element, set()).add(knownTruth)
        if hasattr(self.domain, 'membershipSideEffects'):
                for sideEffect in self.domain.membershipSideEffects(self.element, knownTruth):
                    yield sideEffect
        yield self.unfold   

    def negationSideEffects(self, knownTruth):
        '''
        Fold Not(x in S) as (x not-in S) as an automatic side-effect.
        '''
        yield self.deduceNotIn
        
    def deduceNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from not_in_set import NotIn
        yield NotIn(self.element, self.domain).concludeAsFolded(assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is not in the domain.
        First, see if it is contained in a subset of the domain.  
        If that fails, try calling 'deduceMembership' on the domain
        with the element and assumptions parameters.
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
        # could not prove it through a subset relationship, now try deduceMembership
        if hasattr(self.domain, 'deduceMembership'):
            return self.domain.deduceMembership(self.element, assumptions)
        raise AttributeError("'deduceMembership' is not implemented for a domain of type " + str(self.domain.__class__))
    
    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduces and returns an equivalence for (x in S), by definition.
        For example, (x in {y}) = (x = y)
        '''
        if hasattr(self.domain, 'membershipEquivalence'):
            return self.domain.membershipEquivalence(self.element, assumptions=assumptions)
        raise AttributeError("'membershipEquivalence' is not implemented for a domain of type " + str(self.domain.__class__))            
                
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (x in S), derive and return an unfolded version.
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        if hasattr(self.domain, 'unfoldMembership'):
            return self.domain.unfoldMembership(self.element, assumptions=assumptions)
        raise AttributeError("'unfoldMembership' is not implemented for a domain of type " + str(self.domain.__class__))
    
    def evaluate(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate whether element is or is not in the given domain.
        '''
        from proveit.logic import Equals, TRUE
        evaluation = None
        try:
            equiv = self.equivalence(assumptions)
            val = equiv.evaluate(assumptions).rhs
            evaluation = Equals(equiv, val).prove(assumptions=assumptions)
        except:
            pass
        # try also to evaluate this by deducing membership or non-membership in case it 
        # generates a shorter proof.
        try:
            if evaluation.rhs == TRUE:
                self.domain.deduceMembership(self.element, assumptions)
            else:
                self.domain.deduceNonmembership(self.element, assumptions)
        except:
            pass
        if evaluation is None:
            # as a last resort, try default evaluation methods
            return BinaryOperation.evaluate(self, assumptions)
        return evaluation
            


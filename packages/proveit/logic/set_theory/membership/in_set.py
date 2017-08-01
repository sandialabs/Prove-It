from proveit import Literal, BinaryOperation, USE_DEFAULTS, tryDerivation
from proveit._common_ import x, S

class InSet(BinaryOperation):
    # operator of the InSet operation
    _operator_ = Literal(stringFormat='in', latexFormat=r'\in', context=__file__)    
    
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, InSet._operator_, element, domain)
        self.element = self.operands[0]
        self.domain = self.operands[1]
    
    def deriveSideEffects(self, knownTruth):
        '''
        If the domain has a 'deduceMembershipSideEffects' method, it will be called
        and given the element and assumptions.  Also, the 'unfold' method is called.
        '''
        if hasattr(self.domain, 'deduceMembershipSideEffects'):
            tryDerivation(self.domain.deduceMembershipSideEffects, self.element, knownTruth)
        tryDerivation(self.unfold, assumptions=knownTruth.assumptions)    

    def deduceNegationSideEffects(self, knownTruth):
        '''
        From not(x in S) derive x not in S.
        '''
        tryDerivation(self.deduceNotIn, knownTruth.assumptions)
        
    def deduceNotIn(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from _theorems_ import foldNotInSet
        return foldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is not in the domain by calling
        'deduceMembership' on the domain with the element and assumptions.
        '''
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
            


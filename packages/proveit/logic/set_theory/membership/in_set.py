from proveit import Literal, BinaryOperation, USE_DEFAULTS, tryDerivation
from proveit.common import x, S

IN = Literal(__package__, stringFormat = 'in', latexFormat = r'\in')

class InSet(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, IN, element, domain)
        self.element = element
        self.domain = domain
    
    @classmethod
    def operatorOfOperation(subClass):
        return IN    

    def deriveSideEffects(self, knownTruth):
        '''
        If the domain has a 'deduceMembershipSideEffects' method, it will be called
        and given the element and assumptions.  Also, the 'unfold' method is called.
        '''
        if hasattr(self.domain, 'deduceMembershipSideEffects'):
            tryDerivation(self.domain.deduceMembershipSideEffects, self.element, assumptions=knownTruth.assumptions)
        tryDerivation(self.unfold, assumptions=knownTruth.assumptions)    
        tryDerivation(self.deriveNotInSetEqFalse, assumptions=knownTruth.assumptions)    

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
    
    def deriveNotInSetEqFalse(self, assumptions=USE_DEFAULTS):
        '''
        From (x in S) derive and return [(x not in S) = FALSE]
        '''
        from _theorems_ import notInSetEqFalseIfInSet
        return notInSetEqFalseIfInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

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
                self.domain.deduceNonMembership(self.element, assumptions)
        except:
            pass
        if evaluation is None:
            # as a last resort, try default evaluation methods
            return BinaryOperation.evaluate(self, assumptions)
        return evaluation
            


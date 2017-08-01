from proveit import Literal, BinaryOperation, USE_DEFAULTS, tryDerivation
from proveit._common_ import x, S

class NotInSet(BinaryOperation):
    # operator of the NotInSet operation
    _operator_ = Literal(stringFormat='not-in', latexFormat=r'\notin', context=__file__)    
    
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, NotInSet._operator_, element, domain)
        self.element = self.operands[0]
        self.domain = self.operands[1]  

    def deduceInBool(self):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        '''
        self.domain.deduceNotInSetIsBool(self.element)
    
    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduces and returns an equivalence for (x not in S), by definition.
        For example, (x not in {y}) = (x != y)
        '''
        if hasattr(self.domain, 'nonmembershipEquivalence'):
            return self.domain.nonmembershipEquivalence(self.element, assumptions=assumptions)
        raise AttributeError("'nonmembershipEquivalence' is not implemented for a domain of type " + str(self.domain.__class__))            
        
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (x \notin y), derive and return Not(x \in y).
        '''
        from _theorems_ import unfoldNotInSet
        return unfoldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is not in the domain by calling
        'deduceNonmembership' on the domain with the element and assumptions.
        '''
        if hasattr(self.domain, 'deduceNonmembership'):
            return self.domain.deduceNonmembership(self.element, assumptions)
        return self.concludeAsFolded(assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from _theorems_ import foldNotInSet
        return foldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)
    
    def deriveSideEffects(self, knownTruth):
        '''
        If the domain has a 'deduceNonmembershipSideEffects' method, it will be called
        and given the element and assumptions.  Also, the 'unfold' method is called.
        '''
        if hasattr(self.domain, 'deduceNonmembershipSideEffects'):
            tryDerivation(self.domain.deduceNonmembershipSideEffects, self.element, assumptions=knownTruth.assumptions)
        tryDerivation(self.unfold, assumptions=knownTruth.assumptions)            

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
                self.domain.deduceNonmembership(self.element, assumptions)
            else:
                self.domain.deduceMembership(self.element, assumptions)
        except:
            pass
        if evaluation is None:
            # as a last resort, try default evaluation methods
            return BinaryOperation.evaluate(self, assumptions)
        return evaluation

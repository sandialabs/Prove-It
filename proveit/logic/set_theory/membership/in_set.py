from proveit import Literal, BinaryOperation, USE_DEFAULTS, tryDerivation

IN = Literal(__package__, stringFormat = 'in', latexFormat = r'\in')

class InSet(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, IN, element, domain)
        self.element = element
        self.domain = domain
    
    @classmethod
    def operatorOfOperation(subClass):
        return IN    
        
    """
    # LEADS TO PARADOX.  ONLY ALLOWED WHEN THE DOMAIN IS A KNOWN SET.
    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        self.domain.deduceInSetIsBool(self.element)
    """
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From (x in S), derive and return an unfolded version.
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        return self.domain.unfoldElemInSet(self.element, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is in the domain by calling
        'deduceInSet' on the element with the domain and assumptions.
        '''
        return self.domain.deduceElemInSet(self.element, assumptions)

    
    def deriveSideEffects(self, knownTruth):
        '''
        If the domain has a 'deduceMembershipSideEffects' method, it will be called
        and given the element and assumptions.
        '''
        if hasattr(self.domain, 'deduceMembershipSideEffects'):
            tryDerivation(self.domain.deduceMembershipSideEffects, self.element, assumptions=knownTruth.assumptions)
        tryDerivation(self.unfold, assumptions=knownTruth.assumptions)    
        
    """
    def concludeAsFolded(self):
        '''
        Derive this folded version, x in S, from the unfolded version.
        Examples are: (x in {y}) from (x=y), (x in (A union B)) from ((x in A) or (x in B)).
        This may be extended to work for other types of sets by implementing
        the deduceElemInSet(...) method for each type [see deduceElemInSet(..) defined
        for Singleton or Union].
        '''    
        return self.domain.deduceElemInSet(self.element)
    """
    
    """
    def deriveIsInExpansion(self, expandedSet):
        '''
        From x in S, derive x in expandedSet via S subseteq expendedSet.
        '''
        #from sets import unionDef, x, A, B
        #TODO : derive x in S => x in S or x in expandingSet
        #return unionDef.specialize({x:self.element, A:self.domain, B:self.expandingSet}).deriveLeft()
        pass
    """

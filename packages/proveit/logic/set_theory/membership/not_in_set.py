from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import x, S

class NotInSet(Operation):
    # operator of the NotInSet operation
    _operator_ = Literal(stringFormat='not-in',
                         latexFormat=r'\notin',
                         context=__file__)    
    
    def __init__(self, element, domain):
        Operation.__init__(self, NotInSet._operator_, (element, domain))
        self.element = self.operands[0]
        self.domain = self.operands[1]  
        """
        if hasattr(self.domain, 'nonmembershipObject'):
            self.nonmembershipObject = self.domain.nonmembershipObject(element)
            if not isinstance(self.nonmembershipObject, Nonmembership):
                raise TypeError("The 'nonmembershipObject' of %s should be from a class derived from 'embership'"%str(self.domain))
        """
    
    def __dir__(self):
        '''
        If the domain has a 'nonmembershipObject' method, include methods from the
        object it generates (also 'unfold' which defaults as 'unfoldNotIn' if it
        isn't defined in 'nonmembershipObject').
        '''
        if 'membershipObject' in self.__dict__:
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
            return getattr(self.membershipObject, attr)
        elif attr=='unfold':
            return self.unfoldNotIn # the default 'unfold' method
        raise AttributeError 
    
    def sideEffects(self, knownTruth):
        '''
        Unfold x not-in S as Not(x in S) as an automatic side-effect.
        If the domain has a 'nonmembershipObject' method, side effects
        will also be generated from the 'sideEffects' object that it generates.
        '''
        yield self.unfoldNotIn
        if hasattr(self, 'nonmembershipObject'):
            for sideEffect in self.nonmembershipObject.sideEffects(knownTruth):
                yield sideEffect
        
    def deduceInBool(self):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        PERHAPS MEMBERSHIP/NON-MEMBERSHIP SHOULD ALWAYS BE IN BOOLEAN, THOUGH
        ILL-DEFINED DOMAINS CAN NEVER HAVE MEMBERSHIP TO BE TRUE -- REVISIT.
        '''
        # self.domain.deduceNotInSetIsBool(self.element)
        # replaced by wdc 10/16/2019
        from ._theorems_ import notInSetInBool
        from proveit._common_ import x, S
        return notInSetInBool.specialize({x:self.element, S:self.domain})
        
    def unfoldNotIn(self, assumptions=USE_DEFAULTS):
        '''
        From (x \notin y), derive and return Not(x \in y).
        '''
        from ._theorems_ import unfoldNotInSet
        return unfoldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)

    def conclude(self, assumptions):
        '''
        Attempt to conclude that the element is not in the domain
        via the 'nonmembership object'
        (if the domain has a 'nonmembershipObject' method).
        Otherwise, try 'concludeAsFolded'.
        '''
        if hasattr(self, 'nonmembershipObject'):
            return self.nonmembershipObject.conclude(assumptions)
        return self.concludeAsFolded(assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from ._theorems_ import foldNotInSet
        return foldNotInSet.specialize({x:self.element, S:self.domain}, assumptions=assumptions)        

    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
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
    
    def equivalence(self):
        raise NotImplementedError("Nonmembership object has no 'equivalence' method implemented")

    def deduceInBool():
        raise NotImplementedError("Nonmembership object has no 'deduceInBool' method implemented")


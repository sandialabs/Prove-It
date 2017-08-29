"""
A TransitiveRelation is a generic base class for binary
relationships that are transitive.  Less than and greater than
relationships are examples (so are subset and superset relationships).
For example, transitivity in the "less than" context means that 
a<b and b<c implies that a<c.  Equality (proveit.logic.Equals) is
special kind of TransitiveRelation that is alsy symmetric; that is,
y=x if x=y.  proveit.logic.Equals is a TransitiveRelation, but
overloads the default methods.  The TransitiveRelation class
provides convenient automation capabilities for performing
a transitive search to conclude a new relation from known relations
using transitivity rules.  To enable this, each TransitiveRelation
needs to track to define knownLeftSides and knownRightSides as
class dictionaries; these will be populated as side effects for
each proven relation (see deriveSideEffects).  Also, the
applyTransitivity method should be appropriately implemented.
The default version handles the case when the "other" relation
is an equality (in which case, substitution may simply be performed).
"""


from proveit import Expression, USE_DEFAULTS, safeDummyVar
from proveit import defaults, KnownTruth, ProofFailure
from binary_operation import BinaryOperation

class TransitiveRelation(BinaryOperation):
    r'''
    Base class for generic transitive relations.  Examples
    are <, <=, >, >= as well as subset, subseteq, superset,
    and superseteq relations.  proveit.logic.Equals is a special 
    TransitiveRelation which is also symmetric (x=y means that y=x).
    '''
    
    def __init__(self, operator,lhs, rhs):
        BinaryOperation.__init__(self,operator, lhs, rhs)
        self.lhs = lhs
        self.rhs = rhs

    def sideEffects(self, knownTruth):
        '''
        Automatically derive the reversed form of transitive
        relations as side effects (e.g., y > x from x < y).
        Also, store known left sides and known right sides 
        in class member dictionaries: knownLeftSides, knownRightSides
        whilc will enable transitivity searches.
        '''
        self.__class__.knownLeftSides.setdefault(self.lhs, set()).add(knownTruth)
        self.__class__.knownRightSides.setdefault(self.rhs, set()).add(knownTruth)
        if (self.lhs != self.rhs):
            # automatically derive the reversed equivalent form
            yield self.deriveReversed

    def conclude(self, assumptions):
        '''
        Try to conclude the TransitivityRelation using other 
        TransitivityRelations or Equals that are known to be true via transitivity.
        For example, if a<b, b=c, and c<=d are known
        truths (under the given assumptions), we can conclude that
        a<d (under these assumptions).
        '''
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        Relation = self.__class__
        return transitivitySearch(self, Relation.knownRelationsFromLeft, Relation.knownRelationsFromRight, assumptions)

    @classmethod
    def knownRelationsFromLeft(orderingClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, right-hand-side) pairs for this
        transitivie relationship (or equality) that involve the given expression on 
        the left side and are known to be true under the given assumptions.
        '''
        from proveit.logic import Equals
        for knownTruth in orderingClass.knownLeftSides.get(expr, []):
            if knownTruth.isSufficient(assumptionsSet):
                yield (knownTruth, knownTruth.rhs)
        for (knownTruth, otherExpr) in Equals.knownRelationsFromLeft(expr, assumptionsSet):
            yield (knownTruth, otherExpr)
                
    @classmethod
    def knownRelationsFromRight(orderingClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, left-hand-side) pairs for this
        transitivie relationship (or equality) that involve the given expression on 
        the right side and are known to be true under the given assumptions.
        '''
        from proveit.logic import Equals
        for knownTruth in orderingClass.knownRightSides.get(expr, []):
            if knownTruth.isSufficient(assumptionsSet):
                yield (knownTruth, knownTruth.lhs)
        for (knownTruth, otherExpr) in Equals.knownRelations(expr, assumptionsSet):
            yield (knownTruth, otherExpr)
        
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply transitivity to derive a new relation from 'self' and 'other'.
        For example, from self:a<b, other:b=c, derive a<c.
        This must be implemented for the different types of transitive
        relations.  This default version handles the case where
        'other' is an equality (as in the above example.
        '''
        from proveit.logic import Equals
        if isinstance(other,Equals):
            if other.lhs in (self.lhs, self.rhs):
                subrule = other.rhsSubstitute
                commonExpr = other.lhs
            elif other.rhs in (self.lhs, self.rhs):
                subrule = other.lhsSubstitute
                commonExpr = other.rhs
            else:
                raise ValueError("Equality does not involve either side of inequality!")
            X = safeDummyVar(self)
            if commonExpr == self.lhs:
                return subrule(self.operator.operationMaker([X,self.rhs]),X)
            elif commonExpr == self.rhs:
                return subrule(self.operator.operationMaker([self.lhs,X]),X)
        raise NotImplementedError('Must implement applyTransitivity appropriately for each kind of TransitiveRelation')

def transitivitySearch(relation, knownRelationsFromLeft, knownRelationsFromRight, assumptions):
    '''
    Performs a breadth-first, bidirectional (meet in the middle) search attempting
    to prove the given relation by applying transitivity derivations.
    If successful, the generated KnownTruth is returned; otherwise a
    ProofFailure exception is raised.
    '''
    assumptionsSet = set(assumptions)
    
    if not isinstance(relation, Expression):
        raise TypeError('The relation is expected to be an Expression')
    desiredRelation = relation
    
    # "Chains" map end-points to list of known true relations that get us there
    # by applying transitivity rules.
    # Left chain values will be a list of relations that can take us from
    # relation.lhs to the left chain end-point.
    # Right chain values will be a list of relations that can take us from
    # relation.rhs to the right chain end-point.
    leftChains, rightChains = {relation.lhs:[]}, {relation.rhs:[]}
    unexploredLeft, unexploredRight = dict(leftChains), dict(rightChains)
    
    # while there is something left to explore on both side
    # (otherwise, we have hit a dead end on one of the sides)
    while len(unexploredLeft)>0 and len(unexploredRight)>0:
        # choose the side with the fewest unexplored endpoints.
        # (bias on the left since left-to-right is a common convention)
        if len(unexploredLeft) <= len(unexploredRight):
            chains, unexploredChains = leftChains, unexploredLeft
            extensions = lambda endpoint : knownRelationsFromLeft(endPoint, assumptionsSet)
            endPoints, otherEndPoints = leftChains.keys(), rightChains.keys()
        else:
            chains, unexploredChains = rightChains, unexploredRight
            extensions = lambda endpoint : knownRelationsFromRight(endPoint, assumptionsSet)
            endPoints, otherEndPoints = rightChains.keys(), leftChains.keys()
                        
        # search for extensions to the unexplored chains and see if any make
        # it to the other side
        newChains = dict()
        for endPoint, chain in unexploredChains.iteritems():
            for relation, newEndPoint in extensions(endPoint):
                if not isinstance(relation, KnownTruth) or not isinstance(newEndPoint, Expression):
                    raise TypeError(str(relation.__class__) + '.knownRelationsFromLeft and ' + str(relation.__class__) \
                                       + '.knownRelationsFromRight should yield (KnownTruth, Expression) pairs')
                if newEndPoint not in endPoints:
                    # We only care about new chains with new end-points.
                    newChains[newEndPoint] = chain + [relation]
                    
                    # Do we have an end to end solution?
                    if newEndPoint in otherEndPoints:
                        # made it to the other side. we have a solution.
                        # Apply transitivities to generate it and return this new known truth.
                        if chains is leftChains:
                            # bridge the left extension with the reversed right chain
                            fullChain = newChains[newEndPoint] + list(reversed(rightChains[newEndPoint]))
                        else:
                            # bridge the left chain with the reversed right extension
                            fullChain = leftChains[newEndPoint] + list(reversed(newChains[newEndPoint]))
                        applyTransitivities(fullChain, assumptions=assumptions)
                        try:
                            # try to prove the original relation, after applying the transitivities.
                            # if this does not work, the chain wasn't quite what we needed
                            # (this could happen, for example, if a strong inequality was desired
                            # but a weak inequality was produced) let's continue the search.
                            return desiredRelation.prove(assumptions)
                        except ProofFailure:
                            pass
        
        # get the new unexplored chains and update the full set of chains with the new chains
        unexploredChains.clear()
        unexploredChains.update({endPoint:chain for endPoint,chain in newChains.iteritems() \
                                if endPoint not in chains})
        chains.update(newChains)
        
    raise ProofFailure(relation, assumptions, 'No proof found via applying transitivity amongst known proven relations.')
                
def applyTransitivities(chain, assumptions=USE_DEFAULTS):
    '''
    Apply transitvity rules on a list of relations in the given chain
    to proof the relation over the chain end points.
    Each element of the chain must be a KnownTruth object that represents
    a proven relation for which transitivity rules may be applied via
    an 'applyTransitivity' method (such as a KnownTruth for a proven
    Equals statement).  The chain must "connect" in the sense that any
    two neighbors in the chain can be joined vie applyTransitivity.
    The transitivity rule will be applied left to right.
    '''
    assumptions = defaults.checkedAssumptions(assumptions)
    if len(chain) == 0:
        raise TransitivityException('Empty transitivity relation train')
    if not all(isinstance(element, KnownTruth) for element in chain):
        raise TypeError('Expecting chain elements to be KnownTruth objects')
    while len(chain) >= 2:
        first = chain.pop(0)
        second = chain.pop(0)
        chain.insert(0, first.applyTransitivity(second, assumptions=assumptions))
    return chain[0] # we are done

class TransitivityException:
    def __init__(self, msg):
        self.msg = msg
    def str(self):
        return self.msg
        
from proveit import USE_DEFAULTS, defaults, KnownTruth, ProofFailure
from proveit import Expression

def transitivitySearch(relation, assumptions):
    '''
    Performs a breadth-first, bidirectional (meet in the middle) search attempting
    to prove the given relation by applying transitivity derivations.
    If successful, the generated KnownTruth is returned; otherwise a
    ProofFailure exception is raised.
    '''
    
    assumptionsSet = set(assumptions)
    
    if not isinstance(relation, Expression):
        raise TypeError('The relation is expected to be an Expression')
    Relation = relation.__class__
    desiredRelation = relation
    
    # "Chains" map end-points to list of known true relations that get us there
    # by applying transitivity rules.
    # Left chain values will be a list of relations that can take us from
    # relation.lhs to the left chain end-point.
    # Right chain values will be a list of relations that can take us from
    # relation.rhs to the right chain end-point.
    leftChains, rightChains = {relation.lhs:[]}, {relation.rhs:[]}
    unexploredLeft, unexploredRight = leftChains, rightChains
    
    # while there is something left to explore on both side
    # (otherwise, we have hit a dead end on one of the sides)
    while len(unexploredLeft)>0 and len(unexploredRight)>0:
        
        # choose the side with the fewest unexplored endpoints.
        # (bias on the left since left-to-right is a common convention)
        if len(unexploredLeft) <= len(unexploredRight):
            chains, unexploredChains = leftChains, unexploredLeft
            extensions = lambda endpoint : Relation.knownRelationsFromLeft(endPoint, assumptionsSet)
            endPoints, otherEndPoints = leftChains.keys(), rightChains.keys()
        else:
            chains, unexploredChains = rightChains, unexploredRight
            extensions = lambda endpoint : Relation.knownRelationsFromRight(endPoint, assumptionsSet)
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
                    # we only care about new chains with new end-points.
                    newChains[newEndPoint] = chain + [relation]
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
        
    raise ProofFailure('No proof found via applying transitivity amongst known proven relations')
                
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
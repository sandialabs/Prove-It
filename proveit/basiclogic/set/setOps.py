from proveit.basiclogic.genericOps import BinaryOperation, AssociativeOperation, OperationOverInstances
from proveit.expression import Literal, Operation, Lambda, STRING, LATEX
from proveit.multiExpression import multiExpression, MultiVariable, Etcetera
from proveit.inLiteral import IN
from proveit.everythingLiteral import EVERYTHING
from proveit.common import f, x, y, A, B, S, P, Q, yEtc


pkg = __package__

EVERYTHING.formatMap = {STRING:'EVERYTHING', LATEX:r'\rm{EVERYTHING}'}
NOTHING = Literal(pkg, 'NOTHING', {STRING:'NOTHING', LATEX:r'\emptyset'})

class In(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, IN, element, domain)
        self.element = element
        self.domain = domain
    
    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        from axioms import inSetIsInBool
        return inSetIsInBool.specialize({x:self.element, S:self.domain}).checked()
    
    def unfold(self):
        '''
        From (x in S), derive and return an unfolded version.
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        return self.domain.unfoldElemInSet(self.element).checked({self})
    
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
    def deriveIsInExpansion(self, expandedSet):
        '''
        From x in S, derive x in expandedSet via S subseteq expendedSet.
        '''
        #from sets import unionDef, x, A, B
        #TODO : derive x in S => x in S or x in expandingSet
        #return unionDef.specialize({x:self.element, A:self.domain, B:self.expandingSet}).deriveLeft()
        pass
    """
    
# The IN Literal is defined at the top level of prove-it, but its operationMaker must be set here.
IN.formatMap = {STRING:'in', LATEX:r'\in'}
IN.operationMaker = lambda operands : In(*operands)

class NotIn(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, NOTIN, element, domain)
        self.element = element
        self.domain = domain  

    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        from theorems import notInSetIsInBool
        return notInSetIsInBool.specialize({x:self.element, S:self.domain}).checked()
    
    def unfold(self):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from theorems import unfoldNotIn
        return unfoldNotIn.specialize({x:self.element, S:self.domain}).deriveConclusion().checked({self})


NOTIN = Literal(pkg, 'NOTIN', {STRING:'not in', LATEX:r'\notin'}, lambda operands : NotIn(*operands))

class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, elem)
        self.elem = elem

    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return '{' + str(self.elem) + '}'
        elif formatType == LATEX:
            return r'\{' + self.elem.formatted(formatType) + r'\}'        
 
    def unfoldElemInSet(self, element):
        '''
        From [element in {y}], derive and return (element = y).
        '''
        from axioms import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveRightViaEquivalence()
    
    def deduceElemInSet(self, element):
        '''
        From (element = y), derive and return [element in {y}] where self represents {y}.
        '''   
        from axioms import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveLeftViaEquivalence()

SINGLETON = Literal(pkg, 'SINGLETON', operationMaker = lambda operands : Singleton(operands[0]))

class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, elem)
        self.elem = elem

    def __str__(self):
        return 'Complement(' + str(self.elem) + ')'

COMPLEMENT = Literal(pkg, 'COMPLEMENT', operationMaker = lambda operands : Complement(operands[0]))
        
class Union(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        AssociativeOperation.__init__(self, UNION, *operands)

    def deriveCompletion(self):
        '''
        derive and return S union Complement(S) = EVERYTHING or
        Complement(S) union S = EVERYTHING if this is a union of either or these forms.
        ''' 
        from theorems import complementCompletion, complementCompletionReversed
        if len(self.operands) == 2:
            leftOperand, rightOperand = self.operands       
            if leftOperand == Complement(rightOperand):
                return complementCompletion.specialize({S:leftOperand})
            elif Complement(leftOperand) == rightOperand:
                return complementCompletionReversed.specialize({S:rightOperand})

    def unfoldElemInSet(self, element):
        '''
        From [element in (A union B)], derive and return [(element in A) or (element in B)],
        where self represents (A union B). 
        '''
        from axioms import unionDef
        if len(self.operands) == 2:
            leftOperand, rightOperand = self.operands       
            return unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From [(element in A) or (element in B)], derive and return [element in (A union B)]
        where self represents (A union B).
        ''' 
        from axioms import unionDef
        if len(self.operands) == 2:
            leftOperand, rightOperand = self.operands              
            return unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveLeft()

UNION = Literal(pkg, 'UNION', {STRING:'union', LATEX:r'\bigcup'}, lambda operands : Union(*operands))

class Intersection(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        AssociativeOperation.__init__(self, INTERSECTION, *operands)

    def unfoldElemInSet(self, element):
        '''
        From [element in (A intersection B)], derive and return [(element in A) and (element in B)],
        where self represents (A intersection B). 
        '''
        from axioms import intersectionDef
        return intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From  [(element in A) and (element in B)], derive and return [element in (A intersection B)],
        where self represents (A intersection B). 
        '''
        from axioms import intersectionDef
        return intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveLeft()

INTERSECTION = Literal(pkg, 'INTERSECTION', {STRING:'intersection', LATEX:r'\bigcap'}, lambda operands : Intersection(*operands))

class Difference(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, DIFFERENCE, A, B)
    
DIFFERENCE = Literal(pkg, 'DIFFERENCE', {STRING:'-', LATEX:'-'}, lambda operands : Difference(*operands))

class SubsetEq(BinaryOperation):
    def __init__(self, subSet, superSet):
        BinaryOperation.__init__(self, SUBSET_EQ, subSet, superSet)
        
    def unfold(self, elemInstanceVar=x):
        '''
        From A subset B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        from theorems import unfoldSubsetEq
        return unfoldSubsetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().checked({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A subset B, from the unfolded version,
        (forall_{x in A} x in B).
        '''
        from theorems import foldSubsetEq
        return foldSubsetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

SUBSET_EQ = Literal(pkg, 'SUBSET_EQ', {STRING:'subseteq', LATEX:r'\subseteq'}, lambda operands : SubsetEq(*operands))

class SupersetEq(BinaryOperation):
    def __init__(self, superSet, subSet):
        BinaryOperation.__init__(self, SUPERSET_EQ, superSet, subSet)
        
    def unfold(self, elemInstanceVar=x):
        '''
        From A superset B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        from theorems import unfoldSupersetEq
        return unfoldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().checked({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A superset B, from the unfolded version,
        (forall_{x in B} x in A).
        '''
        from theorems import foldSupersetEq
        return foldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

SUPERSET_EQ = Literal(pkg, 'SUPERSET_EQ', {STRING:'superseteq', LATEX:r'\supseteq'}, lambda operands : SupersetEq(*operands))
 
class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, domain=EVERYTHING, conditions=tuple()):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, domain, conditions)
        self.instanceElement = instanceElement

    def formatted(self, formatType, fence=False):
        outStr = ''
        innerFence = (len(self.conditions) > 0)
        formattedInstanceVars = self.instanceVars.formatted(formatType, fence=False)
        formattedInstanceElement = self.instanceElement.formatted(formatType, fence=innerFence)
        formattedDomain = self.domain.formatted(formatType, fence=True)
        formattedConditions = self.conditions.formatted(formatType, fence=False) 
        if formatType == LATEX: outStr += r"\left\{"
        else: outStr += "{"
        outStr += formattedInstanceElement
        if len(self.conditions) > 0:
            if formatType == LATEX: outStr += r'~|~'
            else: outStr += ' s.t. ' # such that
            outStr += formattedConditions
        if formatType == LATEX: outStr += r"\right\}"
        else: outStr += "}"
        outStr += '_{' + formattedInstanceVars
        if self.domain != EVERYTHING:
            if formatType == LATEX: outStr += r' \in '
            else: outStr += ' in '
            outStr += formattedDomain
        outStr += '}'
        return outStr

    def unfoldElemInSet(self, element):
        '''
        From (x in {Q(y) | P(y)}), derive and return P(x), where x is meant as the given element.
        '''
        from theorems import unfoldSetOfAll, unfoldSimpleSetOfAll
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return unfoldSimpleSetOfAll.specialize({Pop:Psub, x:element, y:self.instanceVars[0]}).deriveConclusion()
        else:
            Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return unfoldSetOfAll.specialize({f_op:f_sub, Q_op:Q_op_sub, x:element, yEtc:self.instanceVars}).deriveConclusion()
    
    def deduceElemInSet(self, element):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        from theorems import foldSetOfAll, foldSimpleSetOfAll
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return foldSimpleSetOfAll.specialize({Pop:Psub, x:element, y:self.instanceVars[0]}).deriveConclusion()
        else:
            Q_op, Q_op_sub = Etcetera(Operation(MultiVariable(Q), self.instanceVars)), self.conditions
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return foldSetOfAll.specialize({f_op:f_sub, Q_op:Q_op_sub, x:element, yEtc:self.instanceVars}).deriveConclusion()

def setOfAllMaker(operands):
    params = OperationOverInstances.extractParameters(operands)
    return SetOfAll(params['instanceVars'], params['instanceExpr'], params['domain'], params['conditions'])
SET = Literal(pkg, 'SET', operationMaker=setOfAllMaker)


from proveit import BinaryOperation, AssociativeOperation, OperationOverInstances
from proveit import Operation, Literal, Etcetera, MultiVariable
from proveit.common import f, x, y, A, B, S, P, Q, yEtc


pkg = __package__

IN = Literal(pkg, stringFormat = 'in', latexFormat = r'\in')
NOTIN = Literal(pkg, stringFormat = 'not in', latexFormat = r'\notin')
SINGLETON = Literal(pkg, stringFormat = 'SINGLETON')
COMPLEMENT = Literal(pkg, stringFormat = 'COMPLEMENT')
UNION = Literal(pkg, stringFormat = 'union', latexFormat = r'\bigcup')
INTERSECTION = Literal(pkg, stringFormat = 'intersection', latexFormat = r'\bigcap')
DIFFERENCE = Literal(pkg, '-')
SUBSET_EQ = Literal(pkg, stringFormat = 'subseteq', latexFormat = r'\subseteq')
SUPERSET_EQ = Literal(pkg, stringFormat = 'superseteq', latexFormat = r'\supseteq')
SET = Literal(pkg, 'SET')

class InSet(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, IN, element, domain)
        self.element = element
        self.domain = domain
    
    @classmethod
    def operatorOfOperation(subClass):
        return IN    
    
    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        self.domain.deduceInSetIsBool(self.element)
    
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

class NotInSet(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, NOTIN, element, domain)
        self.element = element
        self.domain = domain  

    @classmethod
    def operatorOfOperation(subClass):
        return NOTIN    
    
    def deduceInBool(self):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        '''
        self.domain.deduceNotInSetIsBool(self.element)
    
    def unfold(self):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from theorems import unfoldNotIn
        return unfoldNotIn.specialize({x:self.element, S:self.domain}).deriveConclusion().checked({self})


class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, elem)
        self.elem = elem

    @classmethod
    def operatorOfOperation(subClass):
        return SINGLETON    

    def string(self, **kwargs):
        return '{' + str(self.elem) + '}'
    
    def latex(self, **kwargs):
        return r'\{' + self.elem.latex() + r'\}'        
 
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

class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, elem)
        self.elem = elem

    @classmethod
    def operatorOfOperation(subClass):
        return COMPLEMENT    
        
class Union(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        AssociativeOperation.__init__(self, UNION, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return UNION    
    
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

class Intersection(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        AssociativeOperation.__init__(self, INTERSECTION, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return INTERSECTION  
    
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

class Difference(BinaryOperation):
    def __init__(self, A, B):
        BinaryOperation.__init__(self, DIFFERENCE, A, B)

    @classmethod
    def operatorOfOperation(subClass):
        return DIFFERENCE
        
class SubsetEq(BinaryOperation):
    def __init__(self, subSet, superSet):
        BinaryOperation.__init__(self, SUBSET_EQ, subSet, superSet)

    @classmethod
    def operatorOfOperation(subClass):
        return SUBSET_EQ
        
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

class SupersetEq(BinaryOperation):
    def __init__(self, superSet, subSet):
        BinaryOperation.__init__(self, SUPERSET_EQ, superSet, subSet)
        
    @classmethod
    def operatorOfOperation(subClass):
        return SUPERSET_EQ

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
 
class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, domain=None, conditions=tuple()):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, domain, conditions)
        self.instanceElement = instanceElement

    @classmethod
    def operatorOfOperation(subClass):
        return SET
    
    def formatted(self, formatType, fence=False):
        outStr = ''
        innerFence = (len(self.conditions) > 0)
        formattedInstanceVars = self.instanceVars.formatted(formatType, fence=False)
        formattedInstanceElement = self.instanceElement.formatted(formatType, fence=innerFence)
        formattedDomain = self.domain.formatted(formatType, fence=True)
        formattedConditions = self.conditions.formatted(formatType, fence=False) 
        if formatType == 'latex': outStr += r"\left\{"
        else: outStr += "{"
        outStr += formattedInstanceElement
        if len(self.conditions) > 0:
            if formatType == 'latex': outStr += r'~|~'
            else: outStr += ' s.t. ' # such that
            outStr += formattedConditions
        if formatType == 'latex': outStr += r"\right\}"
        else: outStr += "}"
        outStr += '_{' + formattedInstanceVars
        if self.domain is not None:
            if formatType == 'latex': outStr += r' \in '
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



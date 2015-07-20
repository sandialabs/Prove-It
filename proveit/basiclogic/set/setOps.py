from proveit.basiclogic.genericOperations import BinaryOperation, AssociativeOperation, OperationOverInstances
from proveit.expression import Literal, Operation, Lambda, STRING, LATEX
from proveit.basiclogic.variables import A, B, S, P, x, y

pkg = __package__

EVERYTHING = Literal('EVERYTHING')
NOTHING = Literal('NOTHING', {STRING:'NOTHING', LATEX:r'\emptyset'})

class In(BinaryOperation):
    def __init__(self, element, itsSet):
        BinaryOperation.__init__(self, IN, element, itsSet)
        self.element = element
        self.itsSet = itsSet
        
    def deduceInBool(self):
        '''
        Deduce and return that this 'in' statement is in the set of BOOLEANS.
        '''
        from axioms import inSetIsInBool
        return inSetIsInBool.specialize({x:self.element, S:self.itsSet}).check()
    
    def unfold(self):
        '''
        From (x in S), derive and return an unfolded version.
        Examples are: (x=y) from (x in {y}), ((x in A) or (x in B)) from (x in (A union B)).
        This may be extended to work for other types of sets by implementing
        the unfoldElemInSet(...) method for each type [see unfoldElemInSet(..) defined
        for Singleton or Union].
        '''
        return self.itsSet.unfoldElemInSet(self.element).check({self})
    
    def concludeAsFolded(self):
        '''
        Derive this folded version, x in S, from the unfolded version.
        Examples are: (x in {y}) from (x=y), (x in (A union B)) from ((x in A) or (x in B)).
        This may be extended to work for other types of sets by implementing
        the deduceElemInSet(...) method for each type [see deduceElemInSet(..) defined
        for Singleton or Union].
        '''    
        return self.itsSet.deduceElemInSet(self.element)
    
    def deriveIsInExpansion(self, expandedSet):
        '''
        From x in S, derive x in expandedSet via S subseteq expendedSet.
        '''
        #from sets import unionDef, x, A, B
        #TODO : derive x in S => x in S or x in expandingSet
        #return unionDef.specialize({x:self.element, A:self.itsSet, B:self.expandingSet}).deriveLeft()
        pass
    
    def evaluateForall(self, forallStmt):
        '''
        Given a forall statement over some set, evaluate it to TRUE or FALSE if possible
        via the set's evaluateForallInSet method.
        '''
        return self.itsSet.evaluateForallInSet(forallStmt)
    
    def unfoldForall(self, forallStmt):
        '''
        Given a forall statement over some set, unfold it if possible via the set's
        unfoldForallInSet method.
        '''
        return self.itsSet.unfoldForallInSet(forallStmt)
    
    def foldAsForall(self, forallStmt):
        '''
        Given a forall statement over some set, derive it from an unfolded version
        if possible via the set's foldAsForallInSet method.
        '''
        return self.itsSet.foldAsForallInSet(forallStmt)

IN = Literal(pkg, 'IN', {STRING:'in', LATEX:r'\in'}, lambda operands : In(*operands))

class NotIn(BinaryOperation):
    def __init__(self, element, theSet):
        BinaryOperation.__init__(self, NOTIN, element, theSet)
        self.element = element
        self.theSet = theSet
        
    def formattedOperator(self, formatType):
        if formatType == STRING:
            return 'not in'
        elif formatType == LATEX:
            return r'\notin'        

NOTIN = Literal(pkg, 'NOTIN', {STRING:'not in', LATEX:r'\notin'}, lambda operands : NotIn(*operands))

class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, elem)
        self.elem = elem

    def formatted(self, formatType, fenced=False):
        if formatType == STRING:
            return '{' + str(self.elem) + '}'
        elif formatType == LATEX:
            return '{' + self.elem.formatted(formatType) + '}'        
        else:
            return "<mfenced open='{' close='}'>" + self.elem.formatted(formatType) + '</mfenced>'

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

SINGLETON = Literal(pkg, 'SINGLETON', lambda operand : Singleton(operand))

class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, elem)
        self.elem = elem

    def __str__(self):
        return 'Complement(' + str(self.elem) + ')'

COMPLEMENT = Literal(pkg, 'COMPLEMENT', lambda operand : Complement(operand))
        
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
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand       
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
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand       
            return unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From [(element in A) or (element in B)], derive and return [element in (A union B)]
        where self represents (A union B).
        ''' 
        from axioms import unionDef
        if len(self.operand) == 2:
            leftOperand, rightOperand = self.operand                 
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

class SubsetEq(BinaryOperation):
    def __init__(self, subSet, superSet):
        BinaryOperation.__init__(self, SUBSET_EQ, subSet, superSet)
        
    def unfold(self, elemInstanceVar=x):
        '''
        From A subset B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''        
        from theorems import unfoldSubsetEq
        return unfoldSubsetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().check({self})
    
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
        return unfoldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion().check({self})
    
    def concludeAsFolded(self, elemInstanceVar=x):
        '''
        Derive this folded version, A superset B, from the unfolded version,
        (forall_{x in B} x in A).
        '''
        from theorems import foldSupersetEq
        return foldSupersetEq.specialize({A:self.leftOperand, B:self.rightOperand, x:elemInstanceVar}).deriveConclusion()

SUPERSET_EQ = Literal(pkg, 'SUPERSET_EQ', {STRING:'superseteq', LATEX:r'\superseteq'}, lambda operands : SupersetEq(*operands))
 
class SetOfAll(OperationOverInstances):
    def __init__(self, instanceVars, instanceElement, conditions=None):
        '''
        Create an expression representing the set of all instanceElement for instanceVars such that the conditions are satisfied:
        {instanceElement | conditions}_{instanceVar}
        '''
        OperationOverInstances.__init__(self, SET, instanceVars, instanceElement, conditions)
        self.instanceElement = instanceElement

    def formatted(self, formatType, fenced=False):
        outStr = ''
        innerFenced = (len(self.condition) > 0)
        if formatType == STRING:
            outStr += '{'
            outStr += self.instanceElement.formatted(formatType, fenced=innerFenced)
            if len(self.condition) > 0:
                outStr += ' s.t. ' # such that
                if len(self.condition) == 1:
                    outStr += self.condition.formatted(formatType, fenced=True)
                else:
                    outStr += ', '.join([condition.formatted(formatType, fenced=True) for condition in self.condition])
            outStr += '}'
            if fenced: outStr += ']'
        return outStr

    def unfoldElemInSet(self, element):
        '''
        From (x in {Q(y) | P(y)}), derive and return P(x), where x is meant as the given element.
        '''
        from theorems import unfoldSetOfAll
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return unfoldSetOfAll.specialize({P:Lambda(self.instanceVar, self.instanceExpression), x:element}).deriveConclusion().check({PofElement})
    
    def deduceElemInSet(self, element):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''   
        from theorems import foldSetOfAll
        PofElement = self.instanceExpression.substitute({self.instanceVar:element})
        return foldSetOfAll.specialize({P:Lambda(self.instanceVar, self.instanceExpression), x:element}).deriveConclusion().check({PofElement})

SET = Literal(pkg, 'SET', lambda operand : SetOfAll(operand.argument, operand.expression, operand.domainCondition))


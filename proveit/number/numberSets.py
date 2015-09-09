from proveit.expression import Literal, LATEX, Variable
from proveit.multiExpression import Etcetera
from proveit.common import a, b
from proveit.basiclogic import Forall, In, BinaryOperation, AssociativeOperation
import integer.theorems
import real.theorems
import complex.theorems

pkg = __package__

Z   = Literal(pkg,'Z',{LATEX:r'\mathbb{Z}'})
Zp  = Literal(pkg,'Z^+',{LATEX:r'\mathbb{Z}^+'})
R   = Literal(pkg,'R',{LATEX:r'\mathbb{R}'})
zeroToOne = Literal(pkg,'zeroToOne',{LATEX:r'[0,1]'})

Reals = Literal(pkg,'Reals',{LATEX:r'\mathbb{R}'})
RealsPos = Literal(pkg,'RealsPos',{LATEX:r'\mathbb{R}^+'})
Integers = Literal(pkg,'Integers',{LATEX:r'\mathbb{Z}'})
Naturals = Literal(pkg,'Naturals',{LATEX:r'\mathbb{N}'})
Complexes = Literal(pkg,'Complexes',{LATEX:r'\mathbb{C}'})

class NumberOp:
    def __init__(self, closureTheoremDict):
        self.closureTheoremDict = closureTheoremDict
        
    def deriveInNumberSet(self, numberSet, suppressWarnings=False):
        '''
        Derive this mathematical expression is in some number set (Integers, Reals, Complexes, ..)
        using the closure theorem dictionaries of the operation and applying recursively
        according to the conditions for specializing this theorem. 
        '''
        import integer.theorems 
        import real.theorems
        if numberSet not in self.closureTheoremDict:
            raise NumberClosureException('Could not derive ' + str(self.__class__) + ' expression in ' + numberSet + ' set. Unknown case.')
        closureThm = self.closureTheoremDict[numberSet]
        if not isinstance(closureThm, Forall):
            raise Exception('Expecting closure theorem to be a Forall expression')
        iVars = closureThm.instanceVars
        if not len(iVars) == 2:
            raise Exception('Expecting two instance variables for the closure theorem')    
        # Specialize the closure theorem differently for BinaryOperation or AccociativeOperation cases.   
        if isinstance(self, BinaryOperation):
            closureSpec = closureThm.specialize({iVars[0]:self.operands[0], iVars[1]:self.operands[1]})
        elif isinstance(self, AssociativeOperation):
            closureSpec = closureThm.specialize({a:self.operands[0], Etcetera(b):self.operands[1:]})
        else:
            raise Exception('Expecting NumberOp to be a BinaryOperation or AssociativeOperation')
        # Grab the conditions for the specialization of the closure theorem
        for stmt, _, _, conditions in closureSpec.statement._specializers:
            if stmt._expression == closureThm:
                # check each condition and apply recursively if it is in some set                
                for condition in conditions:
                    condition = condition._expression
                    if isinstance(condition, In):
                        domain = condition.domain
                        elements = condition.elements
                        for elem in elements:
                            if hasattr(elem, 'deriveInNumberSet'):
                                try:
                                    elem.deriveInNumberSet(domain, suppressWarnings=suppressWarnings)
                                except NumberClosureException as e:
                                    if not suppressWarnings:
                                        print "Warning, could not perform nested number set derivation: ", str(e)
                            elif isinstance(elem, Variable) or isinstance(elem, Literal):
                                # for good measure, specialize containment theorems
                                if domain == Complexes:
                                    integer.theorems.inComplexes.specialize({a:elem})
                                    real.theorems.inComplexes.specialize({a:elem})
                                elif domain == Reals:
                                    integer.theorems.inReals.specialize({a:elem})
        return closureSpec                            

    def deriveInIntegers(self, suppressWarnings=False):
        return self.deriveInNumberSet(Integers, suppressWarnings=suppressWarnings)
        
    def deriveInReals(self, suppressWarnings=False):
        return self.deriveInNumberSet(Reals, suppressWarnings=suppressWarnings)

    def deriveInComplexes(self, suppressWarnings=False):
        return self.deriveInNumberSet(Complexes, suppressWarnings=suppressWarnings)

def deriveInNumberSet(*expressions, **kwargs):
    numberSet = kwargs['numberSet']
    suppressWarnings = kwargs['suppressWarnings'] if 'supressWarnings' in kwargs else False
    for expr in expressions:
        if not expr.hasattr('deriveInNumberSet'):
            if not suppressWarnings:
                print "Expression does not have 'deriveInNumberSet' method: ", str(expr)
            continue
        expr.deriveInNumberSet(numberSet, suppressWarnings=suppressWarnings)

def deriveInIntegers(*expressions, **kwargs):
    '''
    For each given expression, attempt to derive that it is in the set of integers.
    Warnings/errors may be suppressed by setting suppressWarnings to True.
    '''
    kwargs['numberSet'] = Integers
    return deriveInNumberSet(*expressions, **kwargs)

def deriveInReals(*expressions, **kwargs):
    '''
    For each given expression, attempt to derive that it is in the set of reals.
    Warnings/errors may be suppressed by setting suppressWarnings to True.
    '''
    kwargs['numberSet'] = Reals
    return deriveInNumberSet(*expressions, **kwargs)

def deriveInComplexes(*expressions, **kwargs):
    '''
    For each given expression, attempt to derive that it is in the set of complexes.
    Warnings/errors may be suppressed by setting suppressWarnings to True.
    '''
    kwargs['numberSet'] = Complexes
    return deriveInNumberSet(*expressions, **kwargs)

class NumberClosureException(Exception):
    def __init__(self, msg):
        self.msg
    def __str__(self):
        return self.msg
    
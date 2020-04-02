from proveit import (Literal, Operation, OperationOverInstances, free_vars,
                     maybeFenced, USE_DEFAULTS, ProofFailure)
from proveit.logic import InSet
from proveit.number.sets import RealInterval, Interval, Reals, Integers, Naturals, Complexes
from proveit.number.negation import Neg
from proveit._common_ import a, f, P, S, QQ, xx

class Sum(OperationOverInstances):
    # operator of the Sum operation.
    _operator_ = Literal(stringFormat='Sum', latexFormat=r'\sum', context=__file__)   
    _init_argname_mapping_ = {'indexOrIndices':'instanceParamOrParams', 
                              'summand':'instanceExpr'}
    
#    def __init__(self, summand-instanceExpression, indices-instanceVars, domains):
#    def __init__(self, instanceVars, instanceExpr, conditions = tuple(), domain=EVERYTHING):
#
    def __init__(self, indexOrIndices, summand, domain=None, domains=None, conditions=tuple(), _lambda_map=None):
        r'''
        Sum summand over indices over domains.
        Arguments serve analogous roles to Forall arguments (found in basiclogic/booleans):
        indices: instance vars
        summand: instanceExpressions
        domains: conditions (except no longer optional)
        '''
        # nestMultiIvars=True will cause it to treat multiple instance variables as nested Sum operations internally
        # and only join them together as a style consequence.
        OperationOverInstances.__init__(self, Sum._operator_, indexOrIndices, summand, domain=domain, domains=domains, conditions=conditions, nestMultiIvars=True, _lambda_map=_lambda_map)
        if hasattr(self, 'instanceVar'):
            self.index = self.instanceVar
        if hasattr(self, 'instanceVars'):
            self.indices = self.instanceVars
        self.summand = self.instanceExpr
        """
        # think about this later
        if isinstance(self.domain,RealInterval):
            raise ValueError('Sum cannot sum over non-discrete set (e.g. Interval)')
        elif self.domain == Reals:
            raise ValueError('Sum cannot sum over Reals.')
        elif self.domain == Integers:
            self.domain = Interval(Neg(infinity),infinity)
        elif self.domain == Naturals:
            self.domain = Interval(zero,infinity)
        """

    def deduceInNumberSet(self, numberSet, assumptions=USE_DEFAULTS):
        from ._theorems_ import summationNatsClosure, summationIntsClosure, summationRealsClosure, summationComplexesClosure
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        Operation(P, self.instanceVars)
        self.summand
        if numberSet == Naturals:
            thm = summationNatsClosure
        elif numberSet == Integers:
            thm = summationIntsClosure
        elif numberSet == Reals:
            thm = summationRealsClosure
        elif numberSet == Complexes:
            thm = summationComplexesClosure
        else:
            raise ProofFailure(InSet(self, numberSet), assumptions, "'deduceInNumberSet' not implemented for the %s set"%str(numberSet))
        return thm.specialize({P_op:P_op_sub, S:self.domain, Q_op:Q_op_sub}, relabelMap={xMulti:self.instanceVars}, 
                                assumptions=assumptions).deriveConsequent(assumptions=assumptions)    
    
    def _formatted(self, formatType, **kwargs):
        # MUST BE UPDATED TO DEAL WITH 'joining' NESTED LEVELS
        fence = kwargs['fence'] if 'fence' in kwargs else False
        if isinstance(self.domain,Interval):
            lower = self.domain.lowerBound.formatted(formatType)
            upper = self.domain.upperBound.formatted(formatType)
            formattedInner = self.operator.formatted(formatType)+r'_{'+self.index.formatted(formatType)+'='+lower+r'}'+r'^{'+upper+r'} '
            explicitIvars = list(self.explicitInstanceVars())
            hasExplicitIvars = (len(explicitIvars) > 0)
            explicitConds = list(self.explicitConditions())
            hasExplicitConds = (len(explicitConds) > 0)
            if hasExplicitConds:
                if hasExplicitIvars: 
                    formattedInner += " | "
                formattedInner += ', '.join(condition.formatted(formatType) for condition in explicitConds) 
            formattedInner += self.summand.formatted(formatType, fence=fence) 
            return maybeFenced(formatType, formattedInner, fence=fence)
        else:
            return OperationOverInstances._formatted(self, formatType, fence)

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a Interval where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from proveit.logic import SimplificationError
        from axioms import sumSingle
        if isinstance(self.domain, Interval) and self.domain.lowerBound == self.domain.upperBound:
            if len(self.instanceVars) == 1:
                return sumSingle.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound})
        raise SimplificationError("Sum simplification only implemented for a summation over a Interval of one instance variable where the upper and lower bound is the same")

    def simplified(self, assumptions=frozenset()):
        '''
        For the trivial case of summing over only one item (currently implemented just
        for a Interval where the endpoints are equal),
        derive and return this summation expression equated the simplified form of
        the single term.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
        
    def reduceGeomSum(self, assumptions=frozenset()):
        r'''
        If sum is geometric sum (finite or infinite), provide analytic expression for sum.
        May need assumptions to proven prerequisite number set conditions.
        '''
        from theorems import infGeomSum, finGeomSum
        mVal = self.indices[0]
        
        try:
#            self.r = extractExpBase(self.summand)
            xVal = self.summand.base
        except:
            raise ValueError("Summand not an exponential!")
        if not isinstance(self.domain,Interval):
            raise ValueError("Not explicitly summing over Interval!")
        else:
            if self.domain.lowerBound == zero and self.domain.upperBound == infinity:
                #We're in the infinite geom sum domain!
                deduceInComplexes(xVal, assumptions)
                return infGeomSum.specialize({x:xVal, m:mVal})
            else:
                #We're in the finite geom sum domain!
                kVal = self.domain.lowerBound
                lVal = self.domain.upperBound
                deduceInIntegers(kVal, assumptions)
                deduceInIntegers(lVal, assumptions)
                deduceInComplexes(xVal, assumptions)
                return finGeomSum.specialize({x:xVal, m:mVal, k:kVal, l:lVal})
#        else:
#            print "Not a geometric sum!"

    def shift(self, shiftAmount, assumptions=frozenset()):
        '''
        Shift the summation indices by the shift amount, deducing and returning
        the equivalence of this summation with a index-shifted version.
        '''
        from theorems import indexShift
        if len(self.indices) != 1 or not isinstance(self.domain, Interval):
            raise Exception('Sum shift only implemented for summations with one index over a Interval')
        fOp, fOpSub = Operation(f, self.index), self.summand
        deduceInIntegers(self.domain.lowerBound, assumptions)
        deduceInIntegers(self.domain.upperBound, assumptions)
        deduceInIntegers(shiftAmount, assumptions)
        return indexShift.specialize({fOp:fOpSub, x:self.index}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, c:shiftAmount})

    def join(self, secondSummation, assumptions=frozenset()):
        '''
        Join the "second summation" with "this" summation, deducing and returning
        the equivalence of these summations added with the joined summation.
        Both summation must be over Intervals.
        The relation between the first summation upper bound, UB1, and the second
        summation lower bound, LB2 must be explicitly either UB1 = LB2-1 or LB2=UB1+1.
        '''
        from theorems import sumSplitAfter, sumSplitBefore
        from proveit.number.common import one
        from proveit.number import Sub, Add
        if not isinstance(self.domain, Interval) or not isinstance(secondSummation.domain, Interval):
            raise Exception('Sum joining only implemented for Interval domains')
        if self.summand != secondSummation.summand:
            raise Exception('Sum joining only allowed when the summands are the same')            
        if self.domain.upperBound == Sub(secondSummation.domain.lowerBound, one):
            sumSplit = sumSplitBefore 
            splitIndex = secondSummation.domain.lowerBound
        elif secondSummation.domain.lowerBound == Add(self.domain.upperBound, one):
            sumSplit = sumSplitAfter
            splitIndex = self.domain.upperBound
        else:
            raise Exception('Sum joining only implemented when there is an explicit increment of one from the upper bound and the second summations lower bound')
        lowerBound, upperBound = self.domain.lowerBound, secondSummation.domain.upperBound
        deduceInIntegers(lowerBound, assumptions)
        deduceInIntegers(upperBound, assumptions)
        deduceInIntegers(splitIndex, assumptions)
        return sumSplit.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:lowerBound, b:splitIndex, c:upperBound, x:self.indices[0]}).deriveReversed()
        
    def split(self, splitIndex, side='after', assumptions=frozenset()):
        r'''
        Splits summation over one Interval {a ... c} into two summations.
        If side == 'after', it splits into a summation over {a ... splitIndex} plus
        a summation over {splitIndex+1 ... c}.  If side == 'before', it splits into
        a summation over {a ... splitIndex-1} plus a summation over {splitIndex ... c}.
        As special cases, splitIndex==a with side == 'after' splits off the first single
        term.  Also, splitIndex==c with side == 'before' splits off the last single term.
        r'''
        if not isinstance(self.domain, Interval) :
            raise Exception('Sum splitting only implemented for Interval domains')
        if side=='before' and self.domain.upperBound==splitIndex: return self.splitOffLast()
        if side=='after' and self.domain.lowerBound==splitIndex: return self.splitOffFirst()
        if isinstance(self.domain, Interval) and len(self.instanceVars) == 1:
            from theorems import sumSplitAfter, sumSplitBefore
            sumSplit = sumSplitAfter if side == 'after' else sumSplitBefore
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            deduceInIntegers(splitIndex, assumptions)
            # Also needs lowerBound <= splitIndex and splitIndex < upperBound
            return sumSplit.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:splitIndex, c:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a Interval of one instance variable")


    def splitOffLast(self, assumptions=frozenset()):
        from axioms import sumSplitLast
        if isinstance(self.domain, Interval) and len(self.instanceVars) == 1:
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            # Also needs lowerBound < upperBound
            return sumSplitLast.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a Interval of one instance variable")

    def splitOffFirst(self, assumptions=frozenset()):
        from theorems import sumSplitFirst # only for associative summation
        if isinstance(self.domain, Interval) and len(self.instanceVars) == 1:
            deduceInIntegers(self.domain.lowerBound, assumptions)
            deduceInIntegers(self.domain.upperBound, assumptions)
            # Also needs lowerBound < upperBound
            return sumSplitFirst.specialize({Operation(f, self.instanceVars):self.summand}).specialize({a:self.domain.lowerBound, b:self.domain.upperBound, x:self.indices[0]})
        raise Exception("splitOffLast only implemented for a summation over a Interval of one instance variable")

    def factor(self, theFactor, pull="left", groupFactor=False, groupRemainder=None, assumptions=frozenset()):
        '''
        Pull out a common factor from a summation, pulling it either to the "left" or "right".
        If groupFactor is True and theFactor is a product, it will be grouped together as a 
        sub-product.  groupRemainder is not relevant kept for compatibility with other factor
        methods.  Returns the equality that equates self to this new version.
        Give any assumptions necessary to prove that the operands are in Complexes so that
        the associative and commutation theorems are applicable.
        '''
        from proveit.number.multiplication.theorems import distributeThroughSummationRev
        from proveit.number import Mult
        if not free_vars(theFactor).isdisjoint(self.indices):
            raise Exception('Cannot factor anything involving summation indices out of a summation')
        # We may need to factor the summand within the summation
        summand_assumptions = assumptions | {InSet(index, self.domain) for index in self.indices}
        summandFactorEq = self.summand.factor(theFactor, pull, groupFactor=False, groupRemainder=True, assumptions=summand_assumptions)
        summandInstanceEquivalence = summandFactorEq.generalize(self.indices, domain=self.domain).checked(assumptions)
        eq = Equation(self.instanceSubstitution(summandInstanceEquivalence).checked(assumptions))
        factorOperands = theFactor.operands if isinstance(theFactor, Mult) else theFactor
        xDummy, zDummy = self.safeDummyVars(2)
        # Now do the actual factoring by reversing distribution
        if pull == 'left':
            Pop, Pop_sub = Operation(P, self.indices), summandFactorEq.rhs.operands[-1]
            xSub = factorOperands
            zSub = []
        elif pull == 'right':
            Pop, Pop_sub = Operation(P, self.indices), summandFactorEq.rhs.operands[0]
            xSub = []
            zSub = factorOperands
        # We need to deduce that theFactor is in Complexes and that all instances of Pop_sup are in Complexes.
        deduceInComplexes(factorOperands, assumptions=assumptions)
        deduceInComplexes(Pop_sub, assumptions=assumptions | {InSet(idx, self.domain) for idx in self.indices}).generalize(self.indices, domain=self.domain).checked(assumptions)
        # Now we specialize distributThroughSummationRev
        spec1 = distributeThroughSummationRev.specialize({Pop:Pop_sub, S:self.domain, yEtc:self.indices, xEtc:Etcetera(MultiVariable(xDummy)), zEtc:Etcetera(MultiVariable(zDummy))}).checked()
        eq.update(spec1.deriveConclusion().specialize({Etcetera(MultiVariable(xDummy)):xSub, Etcetera(MultiVariable(zDummy)):zSub}))
        if groupFactor and len(factorOperands) > 1:
            eq.update(eq.eqExpr.rhs.group(endIdx=len(factorOperands), assumptions=assumptions))
        return eq.eqExpr #.checked(assumptions)
            


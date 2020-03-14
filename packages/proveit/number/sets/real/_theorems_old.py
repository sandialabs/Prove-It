from proveit.logic import Forall, InSet, NotInSet, Iff, NotEquals
from proveit.number import Reals, RealsNeg, RealsPos, IntervalCC, IntervalOC, IntervalCO, IntervalOO
from proveit.number import Integers, Complexes, GreaterThan, LessThan, LessThanEquals, Add, Mult
from proveit.common import a, b, c, n, x
from proveit.number.common import zero, one, e, pi
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

inComplexes = Forall(a,
                    InSet(a,Complexes),
                    domain = Reals)
inComplexes

inRealsPos_inReals = Forall(a, InSet(a,Reals), domain = RealsPos)
inRealsPos_inReals

inRealsNeg_inReals = Forall(a, InSet(a,Reals), domain = RealsNeg)
inRealsNeg_inReals

inRealsPos_inComplexes = Forall(a, InSet(a,Complexes), domain = RealsPos)
inRealsPos_inComplexes

inRealsNeg_inComplexes = Forall(a, InSet(a,Complexes), domain = RealsNeg)
inRealsNeg_inComplexes

inRealsPos_iff_positive = Forall(a, Iff(InSet(a, RealsPos), GreaterThan(a, zero)), domain=Reals)
inRealsPos_iff_positive

inRealsNeg_iff_negative = Forall(a, Iff(InSet(a, RealsNeg), LessThan(a, zero)), domain=Reals)
inRealsNeg_iff_negative

# transferred
positive_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[GreaterThan(a, zero)])
positive_implies_notZero

# transferred
negative_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[LessThan(a, zero)])
negative_implies_notZero

# transferred
allInIntervalOO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOO(a, b)), domain=Reals)
allInIntervalOO_InReals 

# transferred
allInIntervalCO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCO(a, b)), domain=Reals)
allInIntervalCO_InReals 

# transferred
allInIntervalOC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOC(a, b)), domain=Reals)
allInIntervalOC_InReals 

# transferred
allInIntervalCC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCC(a, b)), domain=Reals)
allInIntervalCC_InReals 

# transferred
intervalOOLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOO(a, b)), domain=Reals)
intervalOOLowerBound

# transferred
intervalOOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalOO(a, b)), domain=Reals)
intervalOOUpperBound

# transferred
intervalCOLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCO(a, b)), domain=Reals)
intervalCOLowerBound

# transferred
intervalCOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalCO(a, b)), domain=Reals)
intervalCOUpperBound

# transferred
intervalOCLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOC(a, b)), domain=Reals)
intervalOCLowerBound

# transferred
intervalOCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalOC(a, b)), domain=Reals)
intervalOCUpperBound

# transferred
intervalCCLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCC(a, b)), domain=Reals)
intervalCCLowerBound

# transferred
intervalCCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalCC(a, b)), domain=Reals)
intervalCCUpperBound

# transferred
inIntervalOO = Forall((a, b, x), InSet(x, IntervalOO(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThan(x, b)])
inIntervalOO

# transferred
inIntervalCO = Forall((a, b, x), InSet(x, IntervalCO(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThan(x, b)])
inIntervalCO

# transferred
inIntervalOC = Forall((a, b, x), InSet(x, IntervalOC(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThanEquals(x, b)])
inIntervalOC

# transferred
inIntervalCC = Forall((a, b, x), InSet(x, IntervalCC(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThanEquals(x, b)])
inIntervalCC

# transferred
rescaleInIntervalOO = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalOO(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalOO(a, b)), domain=Reals)
rescaleInIntervalOO

# transferred
rescaleInIntervalOC = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalOC(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalOC(a, b)), domain=Reals)
rescaleInIntervalOC

# transferred
rescaleInIntervalCO = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalCO(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalCO(a, b)), domain=Reals)
rescaleInIntervalCO

# transferred
rescaleInIntervalCC = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalCC(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalCC(a, b)), domain=Reals)
rescaleInIntervalCC

# transferred
relaxIntervalCO = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalCO(a, b)), domain=Reals)
relaxIntervalCO

# transferred
relaxIntervalOC = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalOC(a, b)), domain=Reals)
relaxIntervalOC

# transferred
relaxIntervalOOleft = Forall((a, b), Forall(x, InSet(x, IntervalCO(a, b)), 
                                            domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOleft

# transferred
relaxIntervalOOright = Forall((a, b), Forall(x, InSet(x, IntervalOC(a, b)), 
                                             domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOright

# transferred
notIntIfBetweenSuccessiveInts = Forall(n, Forall(x, NotInSet(x, Integers), domain=IntervalOO(n, Add(n, one))), domain=Integers)
notIntIfBetweenSuccessiveInts

# transferred
eInRealsPos = InSet(e,RealsPos)
eInRealsPos

# transferred
eNotZero = NotEquals(e,zero)
eNotZero

# transferred
piInRealsPos = InSet(pi,RealsPos)
piInRealsPos

# transferred
piNotZero = NotEquals(pi, zero)
piNotZero

endTheorems(locals(), __package__)

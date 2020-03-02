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

inRationalsPos_iff_positive = Forall(a, Iff(InSet(a, RationalsPos), Greater(a, zero)), domain=Rationals)
inRationalsPos_iff_positive

inRealsNeg_iff_negative = Forall(a, Iff(InSet(a, RealsNeg), LessThan(a, zero)), domain=Reals)
inRealsNeg_iff_negative

positive_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[GreaterThan(a, zero)])
positive_implies_notZero

negative_implies_notZero = Forall(a, NotEquals(a, zero), domain=Reals, conditions=[LessThan(a, zero)])
negative_implies_notZero

allInIntervalOO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOO(a, b)), domain=Reals)
allInIntervalOO_InReals 

allInIntervalCO_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCO(a, b)), domain=Reals)
allInIntervalCO_InReals 

allInIntervalOC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalOC(a, b)), domain=Reals)
allInIntervalOC_InReals 

allInIntervalCC_InReals = Forall((a, b), Forall(x, InSet(x, Reals), domain=IntervalCC(a, b)), domain=Reals)
allInIntervalCC_InReals 

intervalOOLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOO(a, b)), domain=Reals)
intervalOOLowerBound

intervalOOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalOO(a, b)), domain=Reals)
intervalOOUpperBound

intervalCOLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCO(a, b)), domain=Reals)
intervalCOLowerBound

intervalCOUpperBound = Forall((a, b), Forall(x, LessThan(x, b), domain=IntervalCO(a, b)), domain=Reals)
intervalCOUpperBound

intervalOCLowerBound = Forall((a, b), Forall(x, LessThan(a, x), domain=IntervalOC(a, b)), domain=Reals)
intervalOCLowerBound

intervalOCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalOC(a, b)), domain=Reals)
intervalOCUpperBound

intervalCCLowerBound = Forall((a, b), Forall(x, LessThanEquals(a, x), domain=IntervalCC(a, b)), domain=Reals)
intervalCCLowerBound

intervalCCUpperBound = Forall((a, b), Forall(x, LessThanEquals(x, b), domain=IntervalCC(a, b)), domain=Reals)
intervalCCUpperBound

inIntervalOO = Forall((a, b, x), InSet(x, IntervalOO(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThan(x, b)])
inIntervalOO

inIntervalCO = Forall((a, b, x), InSet(x, IntervalCO(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThan(x, b)])
inIntervalCO

inIntervalOC = Forall((a, b, x), InSet(x, IntervalOC(a, b)), domain=Reals, conditions=[LessThan(a, x), LessThanEquals(x, b)])
inIntervalOC

inIntervalCC = Forall((a, b, x), InSet(x, IntervalCC(a, b)), domain=Reals, conditions=[LessThanEquals(a, x), LessThanEquals(x, b)])
inIntervalCC

rescaleInIntervalOO = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalOO(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalOO(a, b)), domain=Reals)
rescaleInIntervalOO

rescaleInIntervalOC = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalOC(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalOC(a, b)), domain=Reals)
rescaleInIntervalOC

rescaleInIntervalCO = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalCO(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalCO(a, b)), domain=Reals)
rescaleInIntervalCO

rescaleInIntervalCC = Forall((a, b, c), Forall(x, InSet(Mult(c, x), IntervalCC(Mult(c, a), Mult(c, b))), 
                                               domain=IntervalCC(a, b)), domain=Reals)
rescaleInIntervalCC

relaxIntervalCO = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalCO(a, b)), domain=Reals)
relaxIntervalCO

relaxIntervalOC = Forall((a, b), Forall(x, InSet(x, IntervalCC(a, b)), 
                                        domain=IntervalOC(a, b)), domain=Reals)
relaxIntervalOC

relaxIntervalOOleft = Forall((a, b), Forall(x, InSet(x, IntervalCO(a, b)), 
                                            domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOleft

relaxIntervalOOright = Forall((a, b), Forall(x, InSet(x, IntervalOC(a, b)), 
                                             domain=IntervalOO(a, b)), domain=Reals)
relaxIntervalOOright

notIntIfBetweenSuccessiveInts = Forall(n, Forall(x, NotInSet(x, Integers), domain=IntervalOO(n, Add(n, one))), domain=Integers)
notIntIfBetweenSuccessiveInts

eInRealsPos = InSet(e,RealsPos)
eInRealsPos

eNotZero = NotEquals(e,zero)
eNotZero

piInRealsPos = InSet(pi,RealsPos)
piInRealsPos

piNotZero = NotEquals(pi, zero)
piNotZero

endTheorems(locals(), __package__)

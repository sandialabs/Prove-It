from proveit import Operation
from proveit.logic import Forall, InSet, NotInSet, NotEquals, And, Implies, Equals, Booleans
from proveit.number import Integers, Naturals, NaturalsPos, Interval, Reals, RealsPos, Complexes
from proveit.number import Add, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.number import Len
from proveit.common import a, b, n, m, x, y, P, S, xMulti, xEtc, PxEtc
from proveit.number import zero, one, two, three, four, five, six, seven, eight, nine
from proveit.number.common import Pzero, Pm, P_mAddOne, Pn
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

zeroInNats = InSet(zero, Naturals)

successiveNats = Forall(n, InSet(Add(n, one), Naturals), domain=Naturals)

inductionLemma = Forall(n, Forall(S, Implies(And(InSet(zero, S), Forall(x, InSet(Add(x,one), S), domain=S)), InSet(n, S))), domain=Naturals)

induction = Forall(P, Implies(And(Pzero, Forall(m, P_mAddOne, domain=Naturals, conditions=[Pm])), Forall(n, Pn, Naturals)))

zeroLenExprTuple = Equals(Len(), zero)

multiVarInduction = Forall(P, Implies(Forall((xMulti, y), Implies(PxEtc, Operation(P, [xEtc, y]))), Forall(xMulti, PxEtc)))

inIntsIsBool = Forall(a, InSet(InSet(a, Integers), Booleans))
inIntsIsBool

notInIntsIsBool = Forall(a, InSet(NotInSet(a, Integers), Booleans))
notInIntsIsBool

intsInReals = Forall(a, InSet(a, Reals), domain=Integers)
intsInReals

intsInComplexes = Forall(a, InSet(a, Complexes), domain=Integers)
intsInComplexes

inNaturalsIfNonNeg = Forall(a, InSet(a,Naturals), domain=Integers, conditions=[GreaterThanEquals(a, zero)])
inNaturalsIfNonNeg

inNaturalsPosIfPos = Forall(a, InSet(a,NaturalsPos), domain=Integers, conditions=[GreaterThan(a, zero)])
inNaturalsPosIfPos

intervalInInts = Forall((a, b), Forall(n, InSet(n, Integers), domain=Interval(a, b)), domain=Integers)
intervalInInts          

intervalInNats = Forall((a, b), Forall(n, InSet(n, Naturals), domain=Interval(a, b)), domain=Naturals)
intervalInNats  

intervalInNatsPos = Forall((a, b), Forall(n, InSet(n, NaturalsPos), domain=Interval(a, b)), domain=Integers, conditions=[GreaterThan(a, zero)])
intervalInNatsPos

allInNegativeIntervalAreNegative = Forall((a, b), Forall(n, LessThan(n, zero), domain=Interval(a, b)), domain=Integers, conditions=[LessThan(b, zero)])
allInNegativeIntervalAreNegative

allInPositiveIntervalArePositive = Forall((a, b), Forall(n, GreaterThan(n, zero), domain=Interval(a, b)), domain=Integers, conditions=[GreaterThan(a, zero)])
allInPositiveIntervalArePositive

intervalLowerBound = Forall((a, b), Forall(n, LessThanEquals(a, n), domain=Interval(a, b)), domain=Integers)
intervalLowerBound

intervalUpperBound = Forall((a, b), Forall(n, LessThanEquals(n, b), domain=Interval(a, b)), domain=Integers)
intervalUpperBound

inInterval = Forall((a, b, n), InSet(n, Interval(a, b)), domain=Integers, conditions=[LessThanEquals(a, n), LessThanEquals(n, b)])
inInterval

natsInInts = Forall(a,InSet(a,Integers),domain = Naturals)
natsInInts

natsInReals = Forall(a,InSet(a,Reals),domain = Naturals)
natsInReals

natsInComplexes = Forall(a,InSet(a,Complexes),domain = Naturals)
natsInComplexes

natsPosInNaturals = Forall(a,InSet(a,Naturals),domain = NaturalsPos)
natsPosInNaturals

natsPosInIntegers = Forall(a,InSet(a,Integers),domain = NaturalsPos)
natsPosInIntegers

natsPosInRealsPos = Forall(a,InSet(a,RealsPos),domain = NaturalsPos)
natsPosInRealsPos

natsPosInReals = Forall(a,InSet(a,Reals),domain = NaturalsPos)
natsPosInReals

natsPosInComplexes = Forall(a,InSet(a,Complexes),domain = NaturalsPos)
natsPosInComplexes

naturalsLowerBound = Forall(n, GreaterThanEquals(n, zero), domain=Naturals)
naturalsLowerBound

naturalsPosLowerBound = Forall(n, GreaterThanEquals(n, one), domain=NaturalsPos)
naturalsPosLowerBound

oneInNaturals = InSet(one,Naturals)
oneInNaturals

twoInNaturals = InSet(two,Naturals)
twoInNaturals

threeInNaturals = InSet(three,Naturals)
threeInNaturals

fourInNaturals = InSet(four,Naturals)
fourInNaturals

fiveInNaturals = InSet(five,Naturals)
fiveInNaturals

sixInNaturals = InSet(six,Naturals)
sixInNaturals

sevenInNaturals = InSet(seven,Naturals)
sevenInNaturals

eightInNaturals = InSet(eight,Naturals)
eightInNaturals

nineInNaturals = InSet(nine,Naturals)
nineInNaturals

oneNotZero = NotEquals(one, zero)
oneNotZero

twoNotZero = NotEquals(two, zero)
twoNotZero

threeNotZero = NotEquals(three, zero)
threeNotZero

fourNotZero = NotEquals(four, zero)
fourNotZero

fiveNotZero = NotEquals(five, zero)
fiveNotZero

sixNotZero = NotEquals(six, zero)
sixNotZero

sevenNotZero = NotEquals(seven, zero)
sevenNotZero

eightNotZero = NotEquals(eight, zero)
eightNotZero

nineNotZero = NotEquals(nine, zero)
nineNotZero

oneIsPositive = GreaterThan(one,zero)
oneIsPositive

twoIsPositive = GreaterThan(two,zero)
twoIsPositive

threeIsPositive = GreaterThan(three,zero)
threeIsPositive

fourIsPositive = GreaterThan(four,zero)
fourIsPositive

fiveIsPositive = GreaterThan(five,zero)
fiveIsPositive

sixIsPositive = GreaterThan(six,zero)
sixIsPositive

sevenIsPositive = GreaterThan(seven,zero)
sevenIsPositive

eightIsPositive = GreaterThan(eight,zero)
eightIsPositive

nineIsPositive = GreaterThan(nine,zero)
nineIsPositive

oneInNaturalsPos = InSet(one, NaturalsPos)
oneInNaturalsPos

twoInNaturalsPos = InSet(two, NaturalsPos)
twoInNaturalsPos

threeInNaturalsPos = InSet(three, NaturalsPos)
threeInNaturalsPos

fourInNaturalsPos = InSet(four, NaturalsPos)
fourInNaturalsPos

fiveInNaturalsPos = InSet(five, NaturalsPos)
fiveInNaturalsPos

sixInNaturalsPos = InSet(six, NaturalsPos)
sixInNaturalsPos

sevenInNaturalsPos = InSet(seven, NaturalsPos)
sevenInNaturalsPos

eightInNaturalsPos = InSet(eight, NaturalsPos)
eightInNaturalsPos

nineInNaturalsPos = InSet(nine, NaturalsPos)
nineInNaturalsPos

naturalsInduction = Forall(P, Implies(And(Operation(P, zero), 
                                          Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                 domain=Naturals)),
                                      Forall(n, Operation(P, n), domain=Naturals)))
naturalsInduction      

naturalsPosInduction = Forall(P, Implies(And(Operation(P, one), 
                                             Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                    domain=NaturalsPos)),
                                         Forall(n, Operation(P, n), domain=NaturalsPos)))
naturalsPosInduction 

endTheorems(locals(), __package__)

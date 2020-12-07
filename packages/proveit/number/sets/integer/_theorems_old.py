from proveit import Operation
from proveit.logic import Forall, InSet, NotInSet, NotEquals, And, Implies, Equals, Boolean
from proveit.number import Integer, Natural, NaturalPos, Interval, Reals, RealsPos, Complexes
from proveit.number import Add, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.number import Len
from proveit.common import a, b, n, m, x, y, P, S, xMulti, xEtc, PxEtc
from proveit.number import zero, one, two, three, four, five, six, seven, eight, nine
from proveit.number.common import Pzero, Pm, P_mAddOne, Pn
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

zeroInNats = InSet(zero, Natural)

successiveNats = Forall(n, InSet(Add(n, one), Natural), domain=Natural)

inductionLemma = Forall(n, Forall(S, Implies(And(InSet(zero, S), Forall(x, InSet(Add(x,one), S), domain=S)), InSet(n, S))), domain=Natural)

induction = Forall(P, Implies(And(Pzero, Forall(m, P_mAddOne, domain=Natural, conditions=[Pm])), Forall(n, Pn, Natural)))

zeroLenExprTuple = Equals(Len(), zero)

multiVarInduction = Forall(P, Implies(Forall((xMulti, y), Implies(PxEtc, Operation(P, [xEtc, y]))), Forall(xMulti, PxEtc)))

inIntsIsBool = Forall(a, InSet(InSet(a, Integer), Boolean))
inIntsIsBool

notInIntsIsBool = Forall(a, InSet(NotInSet(a, Integer), Boolean))
notInIntsIsBool

intInReals = Forall(a, InSet(a, Reals), domain=Integer)
intInReals

intInComplexes = Forall(a, InSet(a, Complexes), domain=Integer)
intInComplexes

inNaturalIfNonNeg = Forall(a, InSet(a,Natural), domain=Integer, conditions=[GreaterThanEquals(a, zero)])
inNaturalIfNonNeg

inNaturalPosIfPos = Forall(a, InSet(a,NaturalPos), domain=Integer, conditions=[GreaterThan(a, zero)])
inNaturalPosIfPos

intervalInInt = Forall((a, b), Forall(n, InSet(n, Integer), domain=Interval(a, b)), domain=Integer)
intervalInInt          

intervalInNat = Forall((a, b), Forall(n, InSet(n, Natural), domain=Interval(a, b)), domain=Natural)
intervalInNat  

intervalInNatPos = Forall((a, b), Forall(n, InSet(n, NaturalPos), domain=Interval(a, b)), domain=Integer, conditions=[GreaterThan(a, zero)])
intervalInNatPos

allInNegativeIntervalAreNegative = Forall((a, b), Forall(n, LessThan(n, zero), domain=Interval(a, b)), domain=Integer, conditions=[LessThan(b, zero)])
allInNegativeIntervalAreNegative

allInPositiveIntervalArePositive = Forall((a, b), Forall(n, GreaterThan(n, zero), domain=Interval(a, b)), domain=Integer, conditions=[GreaterThan(a, zero)])
allInPositiveIntervalArePositive

intervalLowerBound = Forall((a, b), Forall(n, LessThanEquals(a, n), domain=Interval(a, b)), domain=Integer)
intervalLowerBound

intervalUpperBound = Forall((a, b), Forall(n, LessThanEquals(n, b), domain=Interval(a, b)), domain=Integer)
intervalUpperBound

inInterval = Forall((a, b, n), InSet(n, Interval(a, b)), domain=Integer, conditions=[LessThanEquals(a, n), LessThanEquals(n, b)])
inInterval

natInInt = Forall(a,InSet(a,Integer),domain = Natural)
natInInt

natInReals = Forall(a,InSet(a,Reals),domain = Natural)
natInReals

natInComplexes = Forall(a,InSet(a,Complexes),domain = Natural)
natInComplexes

natsPosInNatural = Forall(a,InSet(a,Natural),domain = NaturalPos)
natsPosInNatural

natsPosInInteger = Forall(a,InSet(a,Integer),domain = NaturalPos)
natsPosInInteger

natPosInRealsPos = Forall(a,InSet(a,RealsPos),domain = NaturalPos)
natPosInRealsPos

natPosInReals = Forall(a,InSet(a,Reals),domain = NaturalPos)
natPosInReals

natPosInComplexes = Forall(a,InSet(a,Complexes),domain = NaturalPos)
natPosInComplexes

naturalLowerBound = Forall(n, GreaterThanEquals(n, zero), domain=Natural)
naturalLowerBound

naturalPosLowerBound = Forall(n, GreaterThanEquals(n, one), domain=NaturalPos)
naturalPosLowerBound

oneInNatural = InSet(one,Natural)
oneInNatural

twoInNatural = InSet(two,Natural)
twoInNatural

threeInNatural = InSet(three,Natural)
threeInNatural

fourInNatural = InSet(four,Natural)
fourInNatural

fiveInNatural = InSet(five,Natural)
fiveInNatural

sixInNatural = InSet(six,Natural)
sixInNatural

sevenInNatural = InSet(seven,Natural)
sevenInNatural

eightInNatural = InSet(eight,Natural)
eightInNatural

nineInNatural = InSet(nine,Natural)
nineInNatural

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

oneInNaturalPos = InSet(one, NaturalPos)
oneInNaturalPos

twoInNaturalPos = InSet(two, NaturalPos)
twoInNaturalPos

threeInNaturalPos = InSet(three, NaturalPos)
threeInNaturalPos

fourInNaturalPos = InSet(four, NaturalPos)
fourInNaturalPos

fiveInNaturalPos = InSet(five, NaturalPos)
fiveInNaturalPos

sixInNaturalPos = InSet(six, NaturalPos)
sixInNaturalPos

sevenInNaturalPos = InSet(seven, NaturalPos)
sevenInNaturalPos

eightInNaturalPos = InSet(eight, NaturalPos)
eightInNaturalPos

nineInNaturalPos = InSet(nine, NaturalPos)
nineInNaturalPos

naturalsInduction = Forall(P, Implies(And(Operation(P, zero), 
                                          Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                 domain=Natural)),
                                      Forall(n, Operation(P, n), domain=Natural)))
naturalsInduction      

naturalsPosInduction = Forall(P, Implies(And(Operation(P, one), 
                                             Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                    domain=NaturalPos)),
                                         Forall(n, Operation(P, n), domain=NaturalPos)))
naturalsPosInduction 

endTheorems(locals(), __package__)

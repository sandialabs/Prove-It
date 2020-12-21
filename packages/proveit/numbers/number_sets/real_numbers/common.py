from .reals import RealSet, RealPosSet, RealNegSet
from .irrational import IrrationalLiteral

Real = RealSet()
RealPos = RealPosSet()
RealNeg = RealNegSet()

e = IrrationalLiteral('e')
pi = IrrationalLiteral('pi', r'\pi')

from proveit.common import A, B, C, D
from proveit.expression import Variable
from proveit.multiExpression import Block
#from circuit import ImplicitIdentities

B1 = Variable('B1')
B2 = Variable('B2')
B3 = Variable('B3')
C1 = Variable('C1')
C2 = Variable('C2')
C3 = Variable('C3')
I = Variable('I')
IB = Variable('IB')
IC = Variable('IC')

# some Variable labels
Ablock = Block(A)
Bblock = Block(B)
B1block = Block(B1)
B2block = Block(B2)
B3block = Block(B3)
Cblock = Block(C)
C1block = Block(C1)
C2block = Block(C2)
C3block = Block(C3)
Dblock = Block(D)

'''
# for implicit identity gates
Is = ImplicitIdentities(I) 
IsB = ImplicitIdentities(IB) 
IsC = ImplicitIdentities(IC) 
'''

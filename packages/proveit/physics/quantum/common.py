from proveit.common import A, B, C, D
from proveit.expression import Variable, Literal, LATEX, STRING
from proveit.multiExpression import Block
from proveit.numbers import Exp, frac, sqrt
from proveit.numbers.common import zero, one, two
from proveit.numbers.numberSets import Complex
from proveit.linalg import TensorExp, SU
from proveit.physics.quantum.circuit import Gate
from proveit.physics.quantum.quantumOps import Ket

pkg = __package__

I = Literal(pkg, 'I') # Single qubit identity
X = Literal(pkg, 'X') # Pauli-X
Y = Literal(pkg, 'Y') # Pauli-Y
Z = Literal(pkg, 'Z') # Pauli-Z
H = Literal(pkg, 'H') # Hadamard

# PASS: either a blank spot or continuation of a wire in a quantum circuit.
# Can be used when initializing the circuit with a list of lists -- these PASS elements
# are subsequently removed and turned into empty spots of the quantum circuit tensor.
PASS = Literal(pkg, 'PASS') 

PLUS = Literal(pkg, 'PLUS', {LATEX:'+', STRING:'+'}) # For positive X eigenstate
MINUS = Literal(pkg, 'MINUS', {LATEX:'-', STRING:'-'}) # For negative X eigenstate

ket0 = Ket(zero)
ket1 = Ket(one)
ketPlus = Ket(PLUS)
ketMinus = Ket(MINUS)

Xgate = Gate(X)
Ygate = Gate(Y)
Zgate = Gate(Z)
Hgate = Gate(H)

CTRL_UP = Literal(pkg, 'CTRL_UP')
CTRL_DN = Literal(pkg, 'CTRL_DN')
CTRL_UPDN = Literal(pkg, 'CTRL_UPDN')

WIRE_UP = Literal(pkg, 'WIRE_UP') # wire goes up to link with another wire
WIRE_DN = Literal(pkg, 'WIRE_DN') # wire goes down to link with another wire
WIRE_LINK = Literal(pkg, 'WIRE_LINK') # link destination for WIRE_UP or WIRE_DN

QubitSpace = Exp(Complex, two)
QubitRegisterSpace = lambda n : TensorExp(Exp(Complex, two), n) 
RegisterSU = lambda n : SU(Exp(two, n))

invRoot2 = frac(one, sqrt(two))

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

from proveit.expression import Literal, STRING, LATEX
from proveit.number import Exponentiate, Abs, Subtract, Multiply, Fraction
from proveit.number.common import one, two
from proveit.common import l
from proveit.physics.quantum.QPE.phaseEstOps import Alpha

pkg = __package__

# U: Unitary operator to apply quantum phase estimation.
U_ = Literal(pkg, 'U')

# n: Number of qubits which U acts on.
n_ = Literal(pkg, 'n')

# u: Eigenvector of U to apply the quantum phase estimation.
u_ = Literal(pkg, 'u')

# phase: Eigenvalue phase of u w.r.t. U.  U u = e^{i \varphi} u.
#        This \varphi is the phase that is the objective of phase estimation.
phase_ = Literal(pkg, 'phase', {LATEX:r'\varphi'})

# t: Number of qubit registers for the quantum phase estimation.
#    We prove that this is the bits of precision of phase estimation.
t_ = Literal(pkg, 't')

# Psi: Outcome of register qubits following the quantum phase estimation circuit.
Psi_ = Literal(pkg, 'PSI', {STRING:'Psi', LATEX:r'\Psi'})

# m: Random variable for the measurement of Psi as an integer from the register's binary representation.
m_ = Literal(pkg, 'm')

# phase_m: Random variable for the phase result of the quantum phase estimation.
#          phase_m = m / 2^t
phase_m_ = Literal(pkg, 'phase_m', {LATEX:r'\varphi_m'})

# b: The "best" outcome of m such that phase_m is as close as possible to phase.
b_ = Literal(pkg, 'b')

# 2^t
two_pow_t = Exponentiate(two, t_)

# 2^{t-1}
two_pow_t_minus_one = Exponentiate(two, Subtract(t_, one))

alpha_l = Alpha(l)
abs_alpha_l = Abs(Alpha(l))
alpha_l_sqrd = Exponentiate(Abs(Alpha(l)), two)

# delta: difference between the phase and the best phase_m
delta_ = Literal(pkg, 'delta', {LATEX:r'\delta'})



from proveit.expression import Literal, STRING, LATEX
from proveit.number import Exponentiate, Abs, Add, Subtract, Neg, Multiply, Fraction, DiscreteContiguousSet
from proveit.number.common import one, two
from proveit.common import k, l, eps
from proveit.physics.quantum.QPE.phaseEstOps import SubIndexed

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
# psi: indexed intermediate output registers inside the quantum phase estimation circuit.
psi_ = Literal(pkg, 'psi', {STRING:'psi', LATEX:r'\psi'})
psi_k = SubIndexed(psi_, k)
psi_t = SubIndexed(psi_, t_)
psi_next = SubIndexed(psi_, Add(k, one))
psi_1 = SubIndexed(psi_, one)

U_pow_two_pow_k = Exponentiate(U_, Exponentiate(two, k))

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

# amplitude of output register as indexted
alpha_ = Literal(pkg, 'alpha', {STRING:'alpha', LATEX:r'\alpha'})
alpha_l = SubIndexed(alpha_, l)
abs_alpha_l = Abs(alpha_l)
alpha_l_sqrd = Exponentiate(Abs(alpha_l), two)

# delta: difference between the phase and the best phase_m
delta_ = Literal(pkg, 'delta', {LATEX:r'\delta'})

fullDomain = DiscreteContiguousSet(Add(Neg(Exponentiate(two, Subtract(t_, one))), one),
                                                         Exponentiate(two, Subtract(t_, one)))
negDomain = DiscreteContiguousSet(Add(Neg(two_pow_t_minus_one), one), Neg(Add(eps, one)))
posDomain = DiscreteContiguousSet(Add(eps, one), two_pow_t_minus_one)
epsDomain = DiscreteContiguousSet(one, Subtract(two_pow_t_minus_one, two))

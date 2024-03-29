from proveit import Literal, Operation, Function, prover, equality_prover
from proveit import UnsatisfiedPrerequisites
from proveit import a, b
from proveit.logic import InSet
from proveit.numbers import Interval
# from proveit.basiclogic.generic_ops import BinaryOperation
# from proveit.numbers.number_sets import NumberOp, Integer

pkg = __package__  # delete later?


class QPE(Function):
    '''
    Represents the quantum circuit for the quantum phase estimation
    algorithm.
    '''
    # the literal operator of the QPE operation
    _operator_ = Literal(string_format='QPE', latex_format=r'\textrm{QPE}',
                         theory=__file__)

    def __init__(self, U, t, *, styles=None):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, QPE._operator_, (U, t),
                           styles=styles)


class QPE1(Function):
    '''
    Represents the first stage of the quantum circuit for the quantum 
    phase estimation algorithm (up to the quantum Fourier transform
    part).
    '''
    # the literal operator of the QPE operation
    _operator_ = Literal(string_format='QPE1', latex_format=r'\textrm{QPE}_1',
                         theory=__file__)

    def __init__(self, U, t, *, styles=None):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, QPE1._operator_, (U, t),
                           styles=styles)


class PhaseEst(Operation):
    '''
    Represents the quantum circuit for estimating the phase.  The
    quantum phase estimation algorithm consists of a PHASE_ESTIMATOR
    followed by quantum fourier transform.
    '''
    # the literal operator of the PhaseEst operation
    _operator_ = Literal(string_format='PHASE_EST',
                         latex_format=r'{\rm PHASE\_EST}', theory=__file__)

    def __init__(self, U, t, *, styles=None):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, PhaseEst._operator_, (U, t),
                           styles=styles)


class Psuccess(Operation):
    '''
    Probability of success for a given epsilon where success is
    defined as the measured theta_m being with epsilon of the true
    theta (phase).
    '''
    # the literal operator of the Psuccess operation
    _operator_ = Literal(string_format='Psuccess',
                         latex_format=r'P_{\rm success}', theory=__file__)

    def __init__(self, eps, *, styles=None):
        '''
        P_success(eps)
        '''
        Operation.__init__(self, Psuccess._operator_, eps,
                           styles=styles)


class Pfail(Operation):
    '''
    Probability of failure for a given epsilon where success is
    defined as the measured theta_m being within epsilon of the true
    theta (phase).
    '''
    # the literal operator of the Pfail operation
    _operator_ = Literal(string_format='Pfail',
                         latex_format=r'P_{\rm fail}', theory=__file__)

    def __init__(self, eps, *, styles=None):
        '''
        P_fail(eps)
        '''
        Operation.__init__(self, Pfail._operator_, eps,
                           styles=styles)


# Comment from wdc on Sun 1/26/2020
# This is the original ModAdd() operation class.
# See below for attempts to update to current Prove-It.
# class ModAdd(BinaryOperation, NumberOp):
#     '''
#     Addition module 2^t
#     '''
#     def __init__(self, a, b):
#         BinaryOperation.__init__(self, MOD_ADD, a, b)

#     def _closureTheorem(self, number_set):
#         from .theorems import mod_add_closure
#         if number_set == Integer:
#             return mod_add_closure

# MOD_ADD = Literal(pkg, 'MOD_ADD', {LATEX:r'\oplus'}, operation_maker = lambda operands : ModAdd(*operands))

class ModAdd(Operation):
    '''
    Addition module 2^t
    Generated/updated from original above by wdc, beginning 1/26/2020.
    This depends on the mod_ad_closure thm in the quantum/QPE theory,
    BUT that theorem ipynb also requires items from this phase_est_ops.py
    file, in particular requiring this same ModAdd operation class.
    '''
    # the literal operator of the ModAdd operation class
    _operator_ = Literal('MOD_ADD', latex_format=r'\oplus',
                         theory=__file__)

    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, ModAdd._operator_, (a, b),
                           styles=styles)
        
    @equality_prover("defined", "define")
    def definition(self, **defaults_config):
        from . import _mod_add_def
        _a, _b = self.operands
        return _mod_add_def.instantiate({a:_a, b:_b})

    @prover
    def deduce_in_interval(self, **defaults_config):
        from . import _mod_add_closure
        _a, _b = self.operands
        return _mod_add_closure.instantiate({a:_a, b:_b})

    def readily_provable_number_set(self):
        from . import _two_pow_t, _mod_add_closure
        from proveit.numbers import Mod, Add
        if not _mod_add_closure.is_usable():
            raise UnsatisfiedPrerequisites("_mod_add_closure not usable")
        return Mod(Add(self.operands[0], self.operands[1]),
                   _two_pow_t).readily_provable_number_set()
        
    @prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        interval_membership = self.deduce_in_interval()
        if isinstance(number_set, Interval):
            if number_set == interval_membership.domain:
                return interval_membership
            return number_set.deduce_elem_in_set(self)
        if InSet(self, number_set).proven():
            # proven as a side-effect
            return InSet(self, number_set).prove()
        raise NotImplementedError(
                "Proving %s in %s has not been implemented"
                %(self, number_set))

class SubIndexed(Operation):
    '''
    Formats a function-type Operation via a subscript.
    For the 'psi' label, also wraps it in a ket.
    '''
    def __init__(self, label, index, *, styles=None):
        Operation.__init__(self, label, index, styles=styles)
        self.label = self.operator
        self.index = self.operand

    def _formatted(self, format_type, fence=False, **kwargs):
        formatted_label = self.label.formatted(format_type, fence=True)
        formatted_index = self.index.formatted(format_type, fence=False)
        indexed_str = formatted_label + '_{' + formatted_index + '}'
        if str(self.label) == 'psi':
            # If it is indexing 'psi', wrap it in a ket.
            if format_type=='latex':
                return r'\lvert %s \rangle'%indexed_str
            else:
                return r'|%s>'%indexed_str
        return indexed_str
        

from proveit.numbers import i, two, pi, Neg, exp, frac, Mult

def exp2pi_i_on_two_pow_t(*exp_factors):
    from proveit.physics.quantum.QPE import _two_pow_t
    return exp(frac(Mult(*((two, pi, i) + exp_factors)), _two_pow_t))

def exp_neg_2pi_i_on_two_pow_t(*exp_factors):
    from proveit.physics.quantum.QPE import _two_pow_t
    return exp(Neg(frac(Mult(*((two, pi, i) + exp_factors)), _two_pow_t)))

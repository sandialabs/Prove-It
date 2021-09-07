from proveit import (equality_prover, Operation, Function, Literal, 
                     TransRelUpdater)
from proveit import x
from proveit.linear_algebra import SU, TensorExp
from proveit.numbers import one, num, Complex, Exp

pkg = __package__  # delete this later; will no longer be needed


class Bra(Function):
    '''
    Class to represent a Dirac bra vector of the form ⟨0| or ⟨1|.
    '''
    # the literal operator of the Bra operation
    _operator_ = Literal(string_format='BRA', theory=__file__)

    def __init__(self, label, *, styles=None):
        Function.__init__(self, Bra._operator_, label, styles=styles)
        self.label = self.operands[0]  # might need to change

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
    
    def formatted(self, format_type, **kwargs):
        if format_type == 'latex':
            return (r'\langle '
                    + self.label.formatted(format_type, fence=False)
                    + r' \rvert')
        else:  # using the unicode \u2329 for the left angle bracket
            return (u'\u2329'
                    + self.label.formatted(format_type, fence=False)
                    + '|')

    # could instead use string() or latex() method instead


class Ket(Function):
    '''
    Class to represent a Dirac ket vector of the form |0⟩ or |1⟩.
    '''
    # the literal operator of the Ket operation
    _operator_ = Literal(string_format='KET', theory=__file__)

    def __init__(self, label, *, styles=None):
        Function.__init__(self, Ket._operator_, label, styles=styles)
        self.label = self.operands[0]

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
    
    def formatted(self, format_type, no_lvert=False, **kwargs):
        left_str = r'\lvert ' if format_type == 'latex' else '|'
        if no_lvert:
            left_str = ''
        if format_type == 'latex':
            return (left_str +
                    self.label.formatted(format_type, fence=False) +
                    r' \rangle')
        else:  # using the unicode \u232A for the right angle bracket
            return (left_str
                    + self.label.formatted(format_type, fence=False)
                    + u'\u232A')
class Qmult(Operation):
    '''
    A Qmult Operation can string together a sequences of quantum 
    operators and/or kets.  Properly defined, a ket is a vector
    in a Hilbert space and a quantum operator acts (under Qmult)
    as a linear map from a Hilbert space to either the same Hilbert 
    space or a complex number.  The latter is denoted as a 'bra'.
    Using 'op' to denote a quantum operator from Hilbert space to
    Hilbert space, the following combinations are defined:
        Qmult(bra, ket) : c-number
        Qmult(op, ket)  : ket
        Qmult(bra, op)  : bra
        Qmult(op, op)   : op
        Qmult(ket, bra) : op
        Qmult(X, c-number) : X
        Qmult(c-number, X) : X
    where X is a ket, bra, op, or c-number.
    
    Qmult(ket, ket), Qmult(bra, bra),
    Qmult(ket, op), Qmult(op, bra) are NOT defined.
    
    When a Qmult is applied to a single quantum operator, it 
    denotes the mapping represented by the operand:
        Qmult(op) : ket -> ket
        Qmult(bra) : ket -> c-number
        
    The formatting is the same as for matrix multiplication with
    just thin spaces in LaTeX except when there is a single
    operand in which case we wrap the operand in square brackets
    to denote that it represents the corresponding mapping.
    '''
    
    _operator_ = Literal(string_format=r'.', latex_format=r'\thinspace',
                         theory=__file__)
    
    def __init__(self, *operands, styles=None):
        Operation.__init__(self, Qmult._operator_, operands,
                           styles=styles)
    
    def string(self, **kwargs):    
        if self.operands.is_single():
            # Single operand: wrap it in square braces to show
            # we are treating it as an operator (a function).
            return r'\left[' + self.operand.string() + r'\right]'
        return Operation.string(self, **kwargs)
        
    def latex(self, **kwargs):    
        # Turn sub-fence on since the operator is just a space that
        # doesn't serve as a good delimiter of the operands.
        if self.operands.is_single():
            # Single operand: wrap it in square braces to show
            # we are treating it as an operator (a function).
            return r'\left[' + self.operand.latex() + r'\right]'
        kwargs['sub_fence'] = True
        return Operation.latex(self, **kwargs)

class QmultCodomainLiteral(Literal):
    '''
    A product (Qmult, specifically) of a sequence of bras, kets, 
    and/or quantum operators, if and only if they are in a valid 
    sequence, will yield a vector in a vector space over complex numbers
    (including the complex numbers themselves), or a linear map between 
    vectors between vectors spaces over complex numbers.  We regard this
    as a proper class called the QmultCodomain.      
    '''
    def __init__(self, *, styles=None):
        Literal.__init__(self, 'Q*', r'\mathcal{Q^*}', styles=styles)

    @property
    def is_proper_class(self):
        '''
        Vector spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

class RegisterBra(Function):
    '''
    Class to represent a Dirac bra vector that acknowledges the
    size of the register. Intended params are not quite clear ...
    '''
    # the literal operator of the RegisterBra operation
    _operator_ = Literal(string_format='REGISTER_BRA', theory=__file__)

    def __init__(self, label, size, *, styles=None):
        Function.__init__(self, RegisterBra._operator_, (label, size),
                          styles=styles)
        self.label = self.operands[0]   # value
        self.size = self.operands[1]   # size of the register

    def _config_latex_tool(self, lt):
        Function._config_latex_tool(self, lt)
        # Expression._config_latex_tool(self, lt)
        if 'mathtools' not in lt.packages:
            lt.packages.append('mathtools')

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
    
    def formatted(self, format_type, fence=False):
        formatted_label = self.label.formatted(format_type, fence=False)
        formatted_size = self.size.formatted(format_type, fence=False)
        if format_type == 'latex':
            # can't seem to get the \prescript latex to work, so using
            # a temporary work-around with an 'empty' subscript; much
            # googling hasn't uncovered explanation for why \prescript
            # isn't working in the ipynbs
            # return (r'\prescript{}{' + formatted_size + r'}\langle '
            #         + formatted_label + r' \rvert')
            return (r'{_{' + formatted_size + r'}}\langle '
                    + formatted_label + r' \rvert')
        else:
            return '{' + formatted_size + '}_' + \
                u'\u2329' + formatted_label + '|'


class RegisterKet(Function):
    '''
    Class to represent a Dirac ket vector that acknowledges the
    size of the register on which it is defined.
    '''
    # the literal operator of the RegisterKet operation
    _operator_ = Literal(string_format='REGISTER_KET', theory=__file__)

    def __init__(self, label, size, *, styles=None):
        Function.__init__(self, RegisterKet._operator_, (label, size),
                          styles=styles)
        self.label = self.operands[0]   # value for the ket
        self.size = self.operands[1]   # size of the register

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
    
    def formatted(self, format_type, fence=False, no_lvert=False):
        formatted_label = self.label.formatted(format_type, fence=False)
        formatted_size = self.size.formatted(format_type, fence=False)
        left_str = r'\lvert ' if format_type == 'latex' else '|'
        if no_lvert:
            left_str = ''
        if format_type == 'latex':
            return (left_str + formatted_label + r' \rangle_{'
                    + formatted_size + '}')
        else:
            return (left_str + formatted_label + u'\u232A' + '_{'
                    + formatted_size + '}')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this RegisterKet
        expression assuming the operands have been simplified.
        
        Currently deals only with:
        (1) simplifying a RegisterKet with register size = 1 to a
            simple Ket. It's not immediately clear that we always want
            to do such a thing, but here goes.
        '''

        if self.size == one:
            from . import single_qubit_register_ket
            return single_qubit_register_ket.instantiate(
                    {x: self.label}, preserve_all=True)

        # Else simply return self=self.
        # Establishing some minimal infrastructure
        # for future development
        expr = self
        # for convenience updating our equation:
        eq = TransRelUpdater(expr)
        # Future processing possible here.
        return eq.relation


class Meas(Function):
    '''
    Class to represent the making of a measurement on a ket |𝜑⟩.
    '''
    # the literal operator of the Meas operation
    _operator_ = Literal(string_format='MEAS', latex_format=r'\mathcal{M}',
                         theory=__file__)

    def __init__(self, ket, *, styles=None):
        Function.__init__(self, Meas._operator_, ket, styles=styles)
        self.ket = ket


def QubitRegisterSpace(num_Qbits):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    # need some extra curly brackets around the Exp() expression
    # to allow the latex superscript to work on something
    # already superscripted
    return TensorExp({Exp(Complex, num(2))}, num_Qbits)


def RegisterSU(n):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    return SU(Exp(num(2), n))

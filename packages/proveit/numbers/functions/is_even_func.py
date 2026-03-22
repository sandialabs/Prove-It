from proveit import Literal
from proveit import ClassMembership

class IsEvenFunc(ClassMembership):
    '''
    IsEvenFunc denotes membership in the class of even functions on
    some domain D.  Even functions satisfy the property that
    f(-x) = f(x).  For example x ↦ x^2 or x ↦ Cos(x).

    The initial development here is based on some analogous code and
    related concepts/structures in the VecSpaces() class and
    MonDecFuncs class, some pieces of which remain below despite their
    relevance still being questionable. This comment paragraph can
    eventually be deleted.
    '''
    
    _operator_ = Literal(
            string_format=r'IsEvenFunc',
            latex_format=r'\textrm{IsEvenFunc}',
            theory=__file__)

    # A default domain may be set for convenience when determining
    # known memberships in EvenFuncs.
    default_domain = None

        
    def __init__(self, func, domain=None, *, styles=None, _operator=None):
        if _operator is None:
            _operator = IsEvenFunc._operator_
        if domain is None: domain=IsEvenFunc.default_domain
        if domain is None:
            raise ValueError("Must supply a 'domain'; "
                             "IsEvenFunc.default_domain has not been set")
        ClassMembership.__init__(self, _operator, 
                                 func, domain, styles=styles)
        self.domain = domain

    @staticmethod
    def yield_known_domain(even_fxn):
        '''
        Given a monotonically-decreasing function, yield its
        known domain(s).
        '''
        if mon_dec_fxn in self.yield_known_memberships(even_fxn):
            judgments = MonDecFuncs.known_mon_dec_funcs_memberships[mon_dec_fxn]
            for judgment in judgments:
                yield judgment.expr.domain.domain

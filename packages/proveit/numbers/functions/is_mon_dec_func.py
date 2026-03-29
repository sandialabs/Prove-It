from proveit import Literal, prover
from proveit import ClassMembership

class IsMonDecFunc(ClassMembership):
    '''
    IsMonDecFuncs denotes membership in the class of monotonically-
    decreasing functions on some domain D.
    For example, x ↦ 1/x^2 is monotonically decreasing over (0, infty).

    The initial development here is based on some analogous code and
    related concepts/structures in the VecSpaces() class, some pieces
    of which remain below despite their relevance still being
    questionable. This comment paragraph can eventually be deleted.

    We might eventually include a user-specifiable ordering for the
    domain, but assume for the time being that all orderings use the
    standard less than ordering < .
    '''
    
    _operator_ = Literal(
            string_format=r'IsMonDecFunc',
            latex_format=r'\textrm{IsMonDecFunc}',
            theory=__file__)

    # A default domain may be set for convenience when determining
    # known memberships in MonDecFuncs.
    default_domain = None
        
    def __init__(self, func, domain=None, *,
                 styles=None, _operator=None):
        if _operator is None:
            _operator = IsMonDecFunc._operator_
        if domain is None: domain=IsMonDecFunc.default_domain
        if domain is None:
            raise ValueError("Must supply a 'domain'; "
                             "IsMonDecFunc.default_domain has not been set")
        ClassMembership.__init__(self, _operator, func, domain,
                                 styles=styles)
        self.domain = domain

    def formatted_class(self, format_type):
        domain_field = self.domain.formatted(format_type, fence=False)
        if format_type == 'latex':
            return r'{\rm MonDecFunc}(%s)'%domain_field
        return r'MonDecFunc(%s)'%domain_field

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude the function is monotonically-decreasing.
        '''
        return deduce_as_mon_dec_func(self.element, domain=self.domain)

@prover
def deduce_as_mon_dec_func(fxn, *, domain=None, 
                           strict=False, **defaults_config):
    '''
    Prove that the Lambda-map specified by fxn is contained in the
    set of monotonically-decreasing functions defined over the domain.
    Unless strict is True, the returned proven membership may be
    over a broader domain (that is, a stronger statement than required).
    
    For example, we might have fxn = Lambda(x, 1/x^2) and
    domain = RealPos, in which case we try to prove that
    Lambda(x, 1/x^2) is in the set of MonDecFuncs(RealPos).
    '''
    membership = None
    
    # This current implementation cheats to handle a specific case of
    # intrest.  We can make this more general at a later date.
    from proveit import x
    from proveit.logic import SubsetEq
    from proveit.numbers.functions import one_over_x_sqrd_in_mon_dec_fxns
    from proveit.numbers import RealPos
    if fxn == one_over_x_sqrd_in_mon_dec_fxns.element:
        if domain is not None:
            SubsetEq(domain, RealPos).prove()
        return one_over_x_sqrd_in_mon_dec_fxns.instantiate({x:fxn.parameter})
    
    if domain is not None and IsMonDecFunc(fxn, domain).proven():
        # fxn already known to be a monotonically-decreasing function.
        return IsMonDecFunc(fxn, domain).prove()
    
    if hasattr(fxn, 'deduce_as_mon_dec_func'):
        # If there is a 'deduce_as_mon_dec_func' class method for the
        # fxn, try that.
        membership = fxn.deduce_as_mon_dec_func()

    if membership is not None:
        if (not isinstance(membership, Judgment)
            or not isinstance(membership.expr, IsMonDecFunc)
            or membership.element != fxn):
            raise ValueError(
                    "Expecting an IsMonDecFunc of %s but got %s"%
                (fxn, membership))
        return membership

    raise NotImplementedError(
            "'deduce_as_mon_dec_func' is not implemented for this case")


from proveit import Literal
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

    @staticmethod
    def yield_known_domain(mon_dec_fxn):
        '''
        Given a monotonically-decreasing function, yield its
        known domain(s).
        '''
        if mon_dec_fxn in MonDecFuncs.known_mon_dec_funcs_memberships:
            judgments = MonDecFuncs.known_mon_dec_funcs_memberships[mon_dec_fxn]
            for judgment in judgments:
                yield judgment.expr.domain.domain


def containing_mon_dec_func(fxn, *, domain):
    '''
    Return a MonDecFunc over the given domain which contains 'fxn' as
    a member.  Call the 'deduce_in_mon_dec_func' class method on 'fxn'
    if there is one. Raise a NotImplementedError otherwise.
    '''
    if hasattr(vec, 'deduce_in_vec_space'):
        vec_in_space = vec.deduce_in_vec_space(field=field)
        # Check that vec_in_space has the right form.
        if (not isinstance(vec_in_space, Judgment) or
                not isinstance(vec_in_space.expr, InSet)):
            raise TypeError("'deduce_in_vec_space' expected to "
                            "return an InSet Judgment")
        if vec_in_space.expr.element != vec:
            raise ValueError("'deduce_in_vec_space' expected to "
                             "return an InSet Judgment with "
                             "the 'vec' as the 'element'")
        vec_space = vec_in_space.domain
        # Make sure we can prove vec_space is, in fact, a
        # vector space.
        deduce_as_vec_space(vec_space, field=field)
        return vec_space
    raise NotImplementedError(
            "'containing_vec_space' is only implemented when "
            "the element has a 'deduce_in_vec_space' method; %s "
            "does not have such a method"%vec.__class__)   

from proveit import (defaults, ExprRange, Function, Literal, Judgment,
                     UnsatisfiedPrerequisites, prover)
from proveit import n
from proveit.logic import InClass, ClassMembership, InSet, SetMembership
from proveit.numbers import Interval, Real

class MonDecFuncs(Function):
    '''
    MonDecFuncs denotes the set of monotonically-decreasing functions
    on some domain D and codomain C and is meant to capture and
    articulate properties of functions such as 1/x^2 on (0, infty).

    The initial development here is based on some analogous code and
    related concepts/structures in the VecSpaces() class, some pieces
    of which remain below despite their relevance still being
    questionable. This comment paragraph can eventually be deleted.

    We might eventually include a user-specifiable ordering for the
    domain, but assume for the time being that all orderings use the
    standard less than ordering < .
    '''
    
    _operator_ = Literal(
            string_format=r'MonDecFuncs',
            latex_format=r'\textrm{MonDecFuncs}',
            theory=__file__)

    # A default domain may be set for convenience when determining
    # known memberships in MonDecFuncs.
    default_domain = None
    
    # Not clear this is still relevant, but might be useful.
    # Map functions to their known membership(s) within 
    # MonDecFuncs(D) for some domain D. Such a membership relation
    # indicates that it is a monotonically-decreasing function
    # over the corresponding domain.
    known_mon_dec_funcs_memberships = dict()

        
    def __init__(self, domain, *, codomain=Real, styles=None, _operator=None):
        if _operator is None:
            _operator = MonDecFuncs._operator_
        Function.__init__(self, _operator, domain, styles=styles)
        self.domain = domain
        self.codomain = codomain
    

    def membership_object(self, element):
        return MonDecFuncsMembership(element, self)


    @property
    def is_proper_class(self):
        '''
        The collection of monotonically-decreasing functions over a
        domain D with codomain C consistitutes a set instead of a
        proper class. Thus we can use the standard InSet when
        considering the collection as a domain.
        '''
        return False


    # keeping this temporarily while we evaluate its usefulness for
    # this MonDecFuncs context
    @staticmethod
    def get_domain(domain=None, *, may_be_none=False):
        '''
        Return the given domain if one is provided (not None), or the 
        default_domain if one was specified, or raise an exception.
        '''
        if domain is not None:
            return domain
        if MonDecFuncs.default_domain is not None:
            return MonDecFuncs.default_domain
        if not may_be_none:
            raise ValueError("A domain for MonDecFuncs was not specified "
                             "and MonDecFuncs.default_domain was not set.")


    # Not obviously relevant
    # @staticmethod
    # def yield_known_vec_spaces(vec, *, field=None):
    #     '''
    #     Given a vector expression, vec, yield any vector spaces,
    #     over the specified field, known to contain vec.
    #     If the field is not specified, VecSpaces.default_field will
    #     be used, and if a default has not been specified an exception
    #     will be raised.
    #     '''
    #     field = VecSpaces.get_field(field, may_be_none=True)
    #     if vec not in InSet.known_memberships:
    #         return # No known memberships to potentially yield.
    #     for membership in InSet.known_memberships[vec]:
    #         if not membership.is_applicable():
    #             # Skip it if it isn't usable under current default
    #             # assumptions.
    #             continue 
    #         # Check if the membership domain is a vector space over the
    #         # specified field.
    #         domain = membership.domain
    #         vec_space = None
    #         if (field is None and 
    #                 domain in VecSpaces.known_vec_spaces_memberships):
    #             vec_space = domain
    #         elif (field is not None and
    #                   InClass(domain, VecSpaces(field)).proven()):
    #             vec_space = domain
    #         else:
    #             try:
    #                 vec_space = including_vec_space(domain, field=field)
    #             except NotImplementedError:
    #                 pass
    #             if vec_space is None:
    #                 try:
    #                     vec_space_membership = deduce_as_vec_space(domain)
    #                     if vec_space_membership.domain.field == field:
    #                         vec_space = vec_space_membership.element
    #                 except NotImplementedError:
    #                     pass
    #         if vec_space is not None:
    #             # Match found: vec is a member of a domain
    #             # that is a vector space over the specified field.
    #             yield vec_space


    # @staticmethod
    # def yield_known_fields(vec_space):
    #     '''
    #     Given a vector space, yield its known fields.
    #     '''
    #     if vec_space in VecSpaces.known_vec_spaces_memberships:
    #         judgments = VecSpaces.known_vec_spaces_memberships[vec_space]
    #         for judgment in judgments:
    #             yield judgment.expr.domain.field

    # THIS NEEDS WORK! NEEDS TESTING
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


    # @staticmethod
    # def known_vec_space(vec, *, field=None):
    #     '''
    #     Return the known vector space of the given vec under the
    #     specified field (or the default field).
    #     '''
    #     field = VecSpaces.get_field(field, may_be_none=True)
    #     try:
    #         return next(VecSpaces.yield_known_vec_spaces(vec, field=field))
    #     except StopIteration:
    #         # We may not know that 'vec' is in a vector space,
    #         # but we may be able to deduce it in a straightforward
    #         # manner provided it has a 'deduce_in_vec_space' method.
    #         try:
    #             return containing_vec_space(vec, field=field)
    #         except NotImplementedError:
    #             over_field_msg = "" if field is None else " over %s"%field
    #             raise UnsatisfiedPrerequisites(
    #                     "%s is not known to be in a vector space%s"
    #                     %(vec, over_field_msg))

    # @staticmethod
    # def known_vec_spaces(vecs, *, field=None):
    #     '''
    #     Return the known vector spaces of the given vecs under the
    #     specified field (or the default field).
    #     '''
    #     # Effort to appropriately handle an ExprRange operand added
    #     # here by wdc and ww on 1/3/2022.
    #     vec_spaces = []
    #     for vec in vecs:
    #         if isinstance(vec, ExprRange):
    #             # create our expr range
    #             with defaults.temporary() as tmp_defaults:
    #                 assumption = InSet(vec.parameter,
    #                         Interval(vec.true_start_index, vec.true_end_index))
    #                 tmp_defaults.assumptions = (
    #                         defaults.assumptions + (assumption ,))
    #                 body = VecSpaces.known_vec_space(vec.body, field=field)
    #             vec_spaces.append(
    #                 ExprRange(vec.parameter, body,
    #                           vec.true_start_index, vec.true_end_index))
    #         else:
    #             vec_spaces.append(VecSpaces.known_vec_space(vec, field=field))

    #     return vec_spaces
    
    # @staticmethod
    # def known_field(vec_space):
    #     '''
    #     Given a vector space, return any known field.
    #     '''
    #     try:
    #         return next(VecSpaces.yield_known_fields(vec_space))
    #     except StopIteration:
    #         raise UnsatisfiedPrerequisites("%s is not a known vector space"
    #                                        %vec_space)

    
# class VecSpacesMembership(ClassMembership):
#     def __init__(self, element, domain):
#         ClassMembership.__init__(self, element, domain)
#         if not isinstance(domain, VecSpaces):
#             raise TypeError("domain expected to be VecSpaces, not %s"
#                             %domain.__class__)
#         self.field = domain.field
    
#     def side_effects(self, judgment):
#         '''
#         Remember known VecSpaces memberships.
#         '''
#         VecSpaces.known_vec_spaces_memberships.setdefault(
#                 self.element, set()).add(judgment)
#         return # generator yielding nothing
#         yield
    
#     def conclude(self):
#         '''
#         Attempt to conclude this membership in a class of vector
#         spaces.
#         '''
#         return deduce_as_vec_space(self.element, field=self.field)


class MonDecFuncsMembership(SetMembership):
    '''
    Defines methods that apply to membership in the set of
    monotonically-decreasing functions (MonDecFuncs), each element
    of which is characterized by its own domain and codomain.
    '''
    def __init__(self, element, domain):
        # Realize here that the 'element' is a function (manifesting
        # as a Lambda map) and the 'domain' is MonDecFuncs, which
        # itself has a domain/codomain specification
        SetMembership.__init__(self, element, domain)
        if not isinstance(domain, MonDecFuncs):
            raise TypeError("domain expected to be MonDecFuncs, not %s"
                            %domain.__class__)
        # analogous case for the following?
        # self.field = domain.field
    
    def side_effects(self, judgment):
        '''
        Remember known MonDecFuncs memberships.
        '''
        MonDecFuncs.known_mon_dec_funcs_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield
    
    def conclude(self):
        '''
        Attempt to conclude this membership in a set of monotonically-
        decreasing functions.
        '''
        # return deduce_as_vec_space(self.element, field=self.field)
        return deduce_as_mon_dec_func(self.element, domain=self.domain.domain)


## ======================== ##
##  Utility Fxns            ##
##  Utility and details     ##
##  still being worked out  ##
## =======================  ##

# def containing_vec_space(vec, *, field):
#     '''
#     Return a vector space over the given field which contains vec
#     as a member.  Call the 'deduce_in_vec_space' class method on
#     'vec' if there is one.  Raise a NotImplementedError otherwise.
#     '''
#     if hasattr(vec, 'deduce_in_vec_space'):
#         vec_in_space = vec.deduce_in_vec_space(field=field)
#         # Check that vec_in_space has the right form.
#         if (not isinstance(vec_in_space, Judgment) or
#                 not isinstance(vec_in_space.expr, InSet)):
#             raise TypeError("'deduce_in_vec_space' expected to "
#                             "return an InSet Judgment")
#         if vec_in_space.expr.element != vec:
#             raise ValueError("'deduce_in_vec_space' expected to "
#                              "return an InSet Judgment with "
#                              "the 'vec' as the 'element'")
#         vec_space = vec_in_space.domain
#         # Make sure we can prove vec_space is, in fact, a
#         # vector space.
#         deduce_as_vec_space(vec_space, field=field)
#         return vec_space
#     raise NotImplementedError(
#             "'containing_vec_space' is only implemented when "
#             "the element has a 'deduce_in_vec_space' method; %s "
#             "does not have such a method"%vec.__class__)

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

# @prover
# def deduce_as_vec_space(expr, *, field=None, **defaults_config):
#     '''
#     Prove that the given expression is contained in the class of vector
#     spaces over some field.
#     '''
#     from proveit.logic import CartExp
#     membership = None
#     if field is not None and InClass(expr, VecSpaces(field)).proven():
#         # Already known as an appropriate vector space.
#         return InClass(expr, VecSpaces(field)).prove()
#     if isinstance(expr, CartExp):
#         '''
#         For the Cartesian exponentiation of rational, real, or
#         complex numbers, we can deduce that it is a member of
#         the class of vector spaces over the corresponding field.
#         '''
#         from proveit.numbers import Rational, Real, Complex
#         from . import (
#                 rational_vec_set_is_vec_space, real_vec_set_is_vec_space, 
#                 complex_vec_set_is_vec_space)
#         if expr.base == Rational:
#             membership = rational_vec_set_is_vec_space.instantiate(
#                     {n:expr.exponent})
#         elif expr.base == Real:
#             membership = real_vec_set_is_vec_space.instantiate({n:expr.exponent})
#         elif expr.base == Complex:
#             membership = complex_vec_set_is_vec_space.instantiate({
#                     n:expr.exponent})
#         else:
#             raise NotImplementedError(
#                     "'deduce_as_vec_space' is not implemented "
#                     "to handle %s"%expr)
#     if hasattr(expr, 'deduce_as_vec_space'):
#         # If there is a 'deduce_as_vec_space' class method for the
#         # expression, try that.
#         membership = expr.deduce_as_vec_space()
#     if membership is not None:
#         InClass.check_proven_class_membership(
#                 membership, expr, VecSpaces)
#         if field is not None and membership.domain.field != field:
#             raise ValueError("'deduce_as_vec_space' proved membership in "
#                              "vector spaces over %s, not over the requested "
#                              "%s field"%(membership.domain.field, field))
            
#         return membership
#     raise NotImplementedError(
#             "'deduce_as_vec_space' is only implemented when "
#             "the element is a CartExp expression or has a "
#             "'deduce_as_vec_space' method; %s "
#             "does not have such a method"%expr.__class__)


@prover
def deduce_as_mon_dec_func(fxn, *, domain=None, **defaults_config):
    '''
    Prove that the Lambda-map specified by fxn is contained in the
    set of monotonically-decreasing functions defined over the domain.
    For example, we might have fxn = Lambda(x, 1/x^2) and
    domain = RealPos, in which case we try to prove that
    Lambda(x, 1/x^2) is in the set of MonDecFuncs(RealPos).
    '''
    membership = None

    if domain is not None and InSet(fxn, MonDecFuncs(domain)).proven():
        # fxn already known to be a monotonically-decreasing function.
        return InSet(fxn, MonDecFuncs(domain)).prove()
    
    if hasattr(fxn, 'deduce_as_mon_dec_func'):
        # If there is a 'deduce_as_mon_dec_func' class method for the
        # fxn, try that.
        membership = fxn.deduce_as_mon_dec_func()

    # in the original VecSpaces.deduce_as_vec_space(), the following
    # checked for proper class membership before returning the
    # the membership; instead we are dealing with a set membership
    # and temporarily achieve this check manually further below
    # if membership is not None:
    #     InClass.check_proven_class_membership(
    #             membership, expr, VecSpaces)
    #     if field is not None and membership.domain.field != field:
    #         raise ValueError("'deduce_as_vec_space' proved membership in "
    #                          "vector spaces over %s, not over the requested "
    #                          "%s field"%(membership.domain.field, field))

    # def check_proven_class_membership(membership, element, class_of_class):
    #     if (not isinstance(membership, Judgment)
    #             or not isinstance(membership.expr, InClass)
    #             or membership.element != element
    #             or not isinstance(membership.domain, class_of_class)):
    #         raise ValueError(
    #                 "Failed to meet expectation: %s is supposed to be a "
    #                 "proven Judgment that %s is a member of a class "
    #                 "represented by an Expression of type %s"
    #                 %(membership, element, class_of_class)) 
    
    if membership is not None:
        if (not isinstance(membership, Judgment)
            or not isinstance(membership.expr, InSet)
            or membership.element != fxn
            or not isinstance(membership.domain, MonDecFuncs)):
            raise ValueError(
                    "Failed ... with message to be completed!")
        return membership

    raise NotImplementedError(
            "'deduce_as_mon_dec_func' is not implemented for this case")


def including_vec_space(subset, *, field):
    '''
    Return a vector space over the given field which includes
    the 'subset'.  Handles the following CartExpr cases:
        C^n contains R^n and Q^n as well as C^n
        R^n contains Q^n as well as R^n
        Q^n only contains Q^n
    Otherwise, call the 'including_vec_space' class method on
    'subset' if there is one.  Raise a NotImplementedError if all else
    fails.
    '''
    from proveit.logic import SubsetEq, CartExp
    from proveit.numbers import Rational, Real, Complex
    vec_space = None
    if isinstance(subset, CartExp):
        if field is None or field==subset.base:
            vec_space = subset
        elif ((field == Complex and subset.base in (Rational, Real))
              or (field == Real and subset.base == Rational)):
            vec_space = CartExp(field, subset.exponent)
    if ((field==Complex and (subset in (Rational, Real))) or
            (field==Real and subset==Rational)):
        vec_space = field
    if vec_space is None and hasattr(subset, 'including_vec_space'):
        vec_space = subset.including_vec_space(field=field)
    if vec_space is None:
        raise NotImplementedError(
                "'including_vec_space' is not implemented "
                "to handle %s over field %s and %s has no "
                "'including_vec_space' method"
                %(subset, field, subset))
    # Make sure it is a vector space
    deduce_as_vec_space(vec_space)
    # Make sure the field is a match.
    if field is not None:
        if VecSpaces.known_field(vec_space) != field:
            raise ValueError(
                    "%s is NOT a vector space over %s as requested."
                    %(vec_space, field))
    if subset != vec_space:
        # Make sure this new domain contains the
        # old domain.
        SubsetEq(subset, vec_space).prove()
    return vec_space

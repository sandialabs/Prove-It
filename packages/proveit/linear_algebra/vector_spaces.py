from proveit import (defaults, ExprRange, Function, Literal, Judgment,
                     ProofFailure, UnsatisfiedPrerequisites, prover)
from proveit import n
from proveit.logic import InClass, ClassMembership, InSet
from proveit.numbers import Interval

class VecSpaces(Function):
    '''
    A VecSpaces expression denotes the class of vector spaces
    over a particular field for the VecAdd and ScalarMult operations.
    
    The VecSpaces definition will enforce the operand to be a field
    in order to contain any members (or even define membership).
    This will allow us to use VecSpaces without an explicit constraint
    on its 'field' operand.
    
    Expression types that may represent vector spaces may implement a
    'deduce_as_vec_space' method to prove its membership in
    the appropriate class of vector spaces over a provided 'field'.

    Expression types that represent a vector in any vector space may 
    implement a 'deduce_in_vec_space' method to prove its membership in
    that space/
    '''
    
    _operator_ = Literal(
            string_format=r'VecSpaces', latex_format=r'\textrm{VecSpaces}',
            theory=__file__)

    # A default field may be set for convenience when determining
    # a known vector spaces (see 'yield_known_vec_spaces').
    default_field = None
    
    # Map vector spaces to their known membership(s) within 
    # VecSpaces(K) for some field K. Such a membership relation is the 
    # indication that it is a vector space over the corresponding field.
    known_vec_spaces_memberships = dict() 
        
    def __init__(self, field, *, styles=None, _operator=None):
        if _operator is None:
            _operator = VecSpaces._operator_
        Function.__init__(self, _operator, field, styles=styles)
        self.field = field
    
    def membership_object(self, element):
        return VecSpacesMembership(element, self)
    
    @property
    def is_proper_class(self):
        '''
        Vector spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

    @staticmethod
    def get_field(field=None, *, may_be_none=False):
        '''
        Return the given field if one is provide (not None), or the 
        default_field if one was specified, or raise an exception.
        '''
        if field is not None:
            return field
        if VecSpaces.default_field is not None:
            return VecSpaces.default_field
        if not may_be_none:
            raise ValueError("A field for vector spaces was not specified "
                             "and VecSpaces.default_field was not set.")

    @staticmethod
    def yield_known_vec_spaces(vec, *, field=None):
        '''
        Given a vector expression, vec, yield any vector spaces,
        over the specified field, known to contain vec.
        If the field is not specified, VecSpaces.default_field will
        be used, and if a default has not been specified an exception
        will be raised.
        '''
        field = VecSpaces.get_field(field, may_be_none=True)
        if vec not in InSet.known_memberships:
            return # No known memberships to potentially yield.
        for membership in InSet.known_memberships[vec]:
            if not membership.is_applicable():
                # Skip it if it isn't usable under current default
                # assumptions.
                continue 
            # Check if the membership domain is a vector space over the
            # specified field.
            domain = membership.domain
            vec_space = None
            if (field is None and 
                    domain in VecSpaces.known_vec_spaces_memberships):
                vec_space = domain
            elif (field is not None and
                      InClass(domain, VecSpaces(field)).proven()):
                vec_space = domain
            else:
                try:
                    vec_space = including_vec_space(domain, field=field)
                except NotImplementedError:
                    pass
                if vec_space is None:
                    try:
                        vec_space_membership = deduce_as_vec_space(domain)
                        if vec_space_membership.domain.field == field:
                            vec_space = vec_space_membership.element
                    except NotImplementedError:
                        pass
            if vec_space is not None:
                # Match found: vec is a member of a domain
                # that is a vector space over the specified field.
                yield vec_space
    
    @staticmethod
    def yield_known_fields(vec_space):
        '''
        Given a vector space, yield its known fields.
        '''
        if vec_space in VecSpaces.known_vec_spaces_memberships:
            judgments = VecSpaces.known_vec_spaces_memberships[vec_space]
            for judgment in judgments:
                yield judgment.expr.domain.field

    @staticmethod
    def known_vec_space(vec, *, field=None):
        '''
        Return the known vector space of the given vec under the
        specified field (or the default field).
        '''
        field = VecSpaces.get_field(field, may_be_none=True)
        try:
            return next(VecSpaces.yield_known_vec_spaces(vec, field=field))
        except StopIteration:
            # We may not know that 'vec' is in a vector space,
            # but we may be able to deduce it in a straightforward
            # manner provided it has a 'deduce_in_vec_space' method.
            try:
                return containing_vec_space(vec, field=field)
            except NotImplementedError:
                over_field_msg = "" if field is None else " over %s"%field
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be in a vector space%s"
                        %(vec, over_field_msg))

    @staticmethod
    def known_vec_spaces(vecs, *, field=None):
        '''
        Return the known vector spaces of the given vecs under the
        specified field (or the default field).
        '''
        # Effort to appropriately handle an ExprRange operand added
        # here by wdc and ww on 1/3/2022.
        vec_spaces = []
        for vec in vecs:
            if isinstance(vec, ExprRange):
                # create our expr range
                with defaults.temporary() as tmp_defaults:
                    assumption = InSet(vec.parameter,
                            Interval(vec.true_start_index, vec.true_end_index))
                    tmp_defaults.assumptions = (
                            defaults.assumptions + (assumption ,))
                    body = VecSpaces.known_vec_space(vec.body, field=field)
                vec_spaces.append(
                    ExprRange(vec.parameter, body,
                              vec.true_start_index, vec.true_end_index))
            else:
                vec_spaces.append(VecSpaces.known_vec_space(vec, field=field))

        return vec_spaces

    @staticmethod
    def common_known_vec_space(vecs, *, field=None):
        '''
        Return a known vector space that is in common among the given
        vectors.
        '''
        # We need to find a vector space that is common to
        # all of the terms.
        candidate_vec_spaces = None
        for vec in vecs:
            cur_vec_spaces = set(VecSpaces.yield_known_vec_spaces(
                    vec, field=field))
            if hasattr(vec, 'deduce_in_vec_space'):
                try:
                    vec_space_membership = vec.deduce_in_vec_space(
                            field=field)
                    cur_vec_spaces.add(vec_space_membership.domain)
                except (UnsatisfiedPrerequisites, NotImplementedError,
                        ProofFailure):
                    pass
            if candidate_vec_spaces is None:
                candidate_vec_spaces = cur_vec_spaces
            else:
                candidate_vec_spaces.intersection_update(cur_vec_spaces)
        try:
            return next(iter(candidate_vec_spaces))
        except StopIteration:
            # No known common vector space membership over the 
            # specified field.
            field_str = '' if field is None else ' over %s'%field
            raise UnsatisfiedPrerequisites(
                    "No common known vector space%s was found among %s."
                    %(field_str, vecs))
    
    @staticmethod
    def known_field(vec_space):
        '''
        Given a vector space, return any known field.
        '''
        try:
            return next(VecSpaces.yield_known_fields(vec_space))
        except StopIteration:
            raise UnsatisfiedPrerequisites("%s is not a known vector space"
                                           %vec_space)

    
class VecSpacesMembership(ClassMembership):
    def __init__(self, element, domain):
        ClassMembership.__init__(self, element, domain)
        if not isinstance(domain, VecSpaces):
            raise TypeError("domain expected to be VecSpaces, not %s"
                            %domain.__class__)
        self.field = domain.field
    
    def side_effects(self, judgment):
        '''
        Remember known VecSpaces memberships.
        '''
        VecSpaces.known_vec_spaces_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield
    
    def conclude(self):
        '''
        Attempt to conclude this membership in a class of vector
        spaces.
        '''
        return deduce_as_vec_space(self.element, field=self.field)

def containing_vec_space(vec, *, field):
    '''
    Return a vector space over the given field which contains vec
    as a member.  Call the 'deduce_in_vec_space' class method on
    'vec' if there is one.  Raise a NotImplementedError otherwise.
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

@prover
def deduce_as_vec_space(expr, *, field=None, **defaults_config):
    '''
    Prove that the given expression is contained in the class of vector
    spaces over some field.
    '''
    from proveit.logic import CartExp
    membership = None
    if field is not None and InClass(expr, VecSpaces(field)).proven():
        # Already known as an appropriate vector space.
        return InClass(expr, VecSpaces(field)).prove()
    if isinstance(expr, CartExp):
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of vector spaces over the corresponding field.
        '''
        from proveit.numbers import Rational, Real, Complex
        from . import (
                rational_vec_set_is_vec_space, real_vec_set_is_vec_space, 
                complex_vec_set_is_vec_space)
        if expr.base == Rational:
            membership = rational_vec_set_is_vec_space.instantiate(
                    {n:expr.exponent})
        elif expr.base == Real:
            membership = real_vec_set_is_vec_space.instantiate({n:expr.exponent})
        elif expr.base == Complex:
            membership = complex_vec_set_is_vec_space.instantiate({
                    n:expr.exponent})
        else:
            raise NotImplementedError(
                    "'deduce_as_vec_space' is not implemented "
                    "to handle %s"%expr)
    if hasattr(expr, 'deduce_as_vec_space'):
        # If there is a 'deduce_as_vec_space' class method for the
        # expression, try that.
        membership = expr.deduce_as_vec_space()
    if membership is not None:
        InClass.check_proven_class_membership(
                membership, expr, VecSpaces)
        if field is not None and membership.domain.field != field:
            raise ValueError("'deduce_as_vec_space' proved membership in "
                             "vector spaces over %s, not over the requested "
                             "%s field"%(membership.domain.field, field))
            
        return membership
    raise NotImplementedError(
            "'deduce_as_vec_space' is only implemented when "
            "the element is a CartExp expression or has a "
            "'deduce_as_vec_space' method; %s "
            "does not have such a method"%expr.__class__)

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

from collections import deque
from functools import wraps
from proveit import Expression, Operation, StyleOptions
from proveit import (defaults, USE_DEFAULTS, Judgment, ProofFailure,
                     prover)
from .sorter import TransitivitySorter


class Relation(Operation):
    r'''
    Base class for generic relations.  Examples
    are Equals, NotEquals, Less, Subset, etc.
    '''

    def __init__(self, operator, normal_lhs, normal_rhs, *, styles):
        # We need to pass along 'direction':'normal' rather than
        # relying about StyleOption defaults because we don't want
        # that to be overwritten by the style of the last expression
        # with the same meaning.
        Operation.__init__(self, operator, (normal_lhs, normal_rhs),
                           styles=styles)
        assert self.operands.is_double(), "%s is not double"%self.operands
        # lhs and rhs with the "direction" style of "normal"
        # (not subject to reversal)
        self.normal_lhs = self.operands[0]
        self.normal_rhs = self.operands[1]
        # The 'lhs' and 'rhs' attributes will access the respective
        # operands, but this is effected in __getattr__ because
        # they will be switched when the 'direction' style is
        # 'reversed'.

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to conclude the Relation by simplifying both
        sides.
        '''
        normal_lhs, normal_rhs = self.normal_lhs, self.normal_rhs
        try:
            normal_lhs_simplification = normal_lhs.simplification()
        except SimplificationError:
            normal_lhs_simplification = Equals(normal_lhs, normal_lhs).prove()
        try:
            normal_rhs_simplification = normal_rhs.simplification()
        except SimplificationError:
            normal_rhs_simplification = Equals(normal_rhs, normal_rhs).prove()
        simp_normal_lhs = normal_lhs_simplification.rhs
        simp_normal_rhs = normal_rhs_simplification.rhs
        if (simp_normal_lhs != normal_lhs) or (simp_normal_rhs != normal_rhs):
            # Prove the simplified version first.
            proven_simp_relation = self.__class__(
                    simp_normal_lhs, simp_normal_rhs,
                    styles=self.get_styles()).prove()
            # Substitute the originals back in.
            proven_relation = normal_lhs_simplification.sub_left_side_into(
                    proven_simp_relation.inner_expr().normal_lhs,
                    preserve_all=True)
            return normal_rhs_simplification.sub_left_side_into(
                    proven_relation.inner_expr().normal_rhs,
                    preserve_all=True)
        raise ProofFailure(self, defaults.assumptions,
                           "Unable to conclude %s"%self)

    def style_options(self):
        '''
        Returns the StyleOptions object for this Relation.
        '''
        options = Operation.style_options(self)
        options.add_option(
                name='direction', 
                description="Direction of the relation (normal or reversed)",
                default='normal',
                related_methods=('with_direction_reversed', 'is_reversed'))
        return options

    @staticmethod
    def reversed_operator_str(format_type):
        raise NotImplementedError(
                "'reversed_operator_str' must be implemented as a class/"
                "static method for a Relation class to support the "
                "'direction' style of 'reversed'.  It should take a "
                "'format_type' argument which may be 'latex' or 'string'.")

    def reversed(self):
        return self.with_direction_reversed()
    
    def is_reversed(self):
        return self.get_style("direction", "normal") == "reversed"
    
    def with_direction_reversed(self):
        if self.is_reversed():
            return self.with_styles(direction="normal")
        return self.with_styles(direction="reversed")
    
    def remake_constructor(self):
        if self.is_reversed():
            raise NotImplementedError("Must implement 'remake_constructor' for %s for "
                                      "the case when it is reversed."%self.__class__)
        return Operation.remake_constructor(self)
    
    def remake_arguments(self):
        '''
        The arguments may be reversed if is_reversed() is true.
        '''
        yield self.lhs # These account for a possible reversal.
        yield self.rhs

    def _formatted(self, format_type, **kwargs):
        '''
        Format the binary relation operation.  Note: it may
        be reversed if the "direction" style is "reversed".
        '''
        from proveit import ExprTuple
        wrap_positions=self.wrap_positions()
        justification=self.get_style('justification')
        fence =  kwargs.get('fence', False)
        subFence =  kwargs.get('subFence', True)
        operator_str = self.operator.formatted(format_type)
        operands = self.operands
        if self.is_reversed():
            operator_str = self.__class__.reversed_operator_str(format_type)
            operands = ExprTuple(*reversed(operands.entries))
        return Operation._formatted_operation(
                format_type, operator_str, operands,
                fence=fence, subFence=subFence, 
                wrap_positions=wrap_positions, 
                justification=justification)

    @prover
    def do_something_on_both_sides(self, **defaults_config):
        '''
        The entire purpose of this method is this docstring to be
        informative.  There may be on-the-fly methods created
        for this TransitiveRelation, dependent upon the type of
        transitive relation and any known set members of either
        side of the relation, that end in "both_sides".  If the
        desired method is not available, be sure to prove the
        membership of either side of the relation (under any
        assumption).
        '''
        raise Exception(self.do_something_on_both_sides.__doc__)
    
    @property
    def lhs(self):
        '''
        The left-hand side depends upon whether or not the relation
        is reversed in its style.
        '''
        if self.is_reversed():
            return self.normal_rhs
        else:
            return self.normal_lhs

    @property
    def rhs(self):
        '''
        The right-hand side depends upon whether or not the relation
        is reversed in its style.
        '''
        if self.is_reversed():
            return self.normal_lhs
        else:
            return self.normal_rhs

    def __getattr__(self, name):
        '''
        Methods that end in '_both_sides' (as in performing an operation
        on both sides) can be defined for the relation indirectly via
        any domain known to contain either the left or right side of the
        relation.  For example, if (x in Complex) is
        known, (x = y) will have methods called "left_mult_both_sides",
        "divide_both_sides" built from
        ComplexSet.left_mult_both_sides_of_equals and
        ComplexSet.divide_both_sides_of_equals respectively.
        The method in the domain class must end in
        "_both_sides_of_<lower-case-relation-class-name>" and match
        this attribute name up to "..._both_sides" as in these
        examples.  The corresponding @prover method is built on-the-fly
        for the TransitiveRelation class.
        '''
        both_sides_str = '_both_sides'
        if name[-len(both_sides_str):] == both_sides_str:
            from proveit.logic import InSet
            known_memberships = set()
            if self.lhs in InSet.known_memberships:
                known_memberships.update(InSet.known_memberships[self.lhs])
            elif self.rhs in InSet.known_memberships:
                known_memberships.update(InSet.known_memberships[self.rhs])
            # These classes may contain '_both_sides' methods that could
            # be applied via the Relation (also attach corresponding
            # domains as applicable):
            if self.lhs.__class__ == self.rhs.__class__:
                classes_and_domains = [(self.lhs.__class__, None)]
            else:
                classes_and_domains = [(self.lhs.__class__, None),
                                       (self.rhs.__class__, None)]
            _last_try_classes_and_domains = []
            for known_membership in known_memberships:
                # We don't require that the known_membership
                # is proven under the default assumptions, but
                # we will try those ones first.
                _domain = known_membership.domain
                _class = _domain.__class__
                if known_membership.is_applicable(defaults.assumptions):
                    classes_and_domains.append((_class, _domain))
                else:
                    _last_try_classes_and_domains.append((_class, _domain))
            classes_and_domains += _last_try_classes_and_domains
            methods_and_domains_to_try = []
            # Append the class name for the domain method name.
            method_name = name + '_of_' + self.__class__.__name__.lower()
            for (_class, _domain) in classes_and_domains:
                if hasattr(_class, method_name):
                    _class_attr = getattr(_class, method_name)
                    methods_and_domains_to_try.append((_class_attr, _domain))
            if len(methods_and_domains_to_try) == 0:
                raise AttributeError("'%s' object has no attribute '%s'"
                                     %(self.__class__, name))
            @prover
            @wraps(methods_and_domains_to_try[0][0])
            def transform_both_sides(*args, **defaults_config):
                _domain = None
                _err = None
                for _method, _domain in methods_and_domains_to_try:
                    try:
                        relation = _method(self, *args)
                        _err = None
                        break
                    except ProofFailure as _e:
                        if _err is None:
                            # We'll report the first error.
                            _err = _e
                        # Keep trying if there are more to try.
                if _err is not None:
                    raise _err
                # After doing the transformation, prove that one of
                # the sides (the left side, arbitrarily) is still in
                # the domain so it will have a known membership for
                # next time.
                if _domain is not None:
                    InSet(relation.lhs, _domain).prove()
                return relation
            # Use the doc string from the wrapped method 
            # (the first one).
            transform_both_sides.__doc__ = (
                methods_and_domains_to_try[0][0].__doc__)
            return transform_both_sides
        return self.__getattribute__(name)
    
    def __dir__(self):
        '''
        Include 'lhs', 'rhs', and the '_both_sides' methods dependent 
        upon the known memberships of the left/right sides of the 
        relation (see __getattr__).
        '''
        both_sides_str = '_both_sides'
        relation_name_str = '_of_' + self.__class__.__name__.lower()
        method_end_str = both_sides_str + relation_name_str
        print('method_end_str', method_end_str)
        both_sides_methods = []
        from proveit.logic import InSet
        known_memberships = set()
        if self.lhs in InSet.known_memberships:
            known_memberships.update(InSet.known_memberships[self.lhs])
        elif self.rhs in InSet.known_memberships:
            known_memberships.update(InSet.known_memberships[self.rhs])
        # These classes may contain '_both_sides' methods that could
        # be applied via the Relation:
        if self.lhs.__class__ == self.rhs.__class__:
            classes = [self.lhs.__class__]
        else:
            classes = [self.lhs.__class__, self.rhs.__class__]
        classes += [known_membership.domain.__class__ for known_membership
                    in known_memberships]
        for _class in classes:
            for name in dir(_class):
                if name[-len(method_end_str):] == method_end_str:
                    both_sides_methods.append(name[:-len(relation_name_str)])
        return sorted(set(dir(self.__class__) + list(self.__dict__.keys())
                          + both_sides_methods + ('lhs', 'rhs')))

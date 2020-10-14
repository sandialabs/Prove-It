from collections import deque
from proveit import Expression, Operation, OperationSequence, StyleOptions
from proveit import defaults, USE_DEFAULTS, KnownTruth, ProofFailure
from .sorter import TransitivitySorter

class Relation(Operation):
    r'''
    Base class for generic relations.  Examples
    are Equals, NotEquals, Less, Subset, etc.
    '''
    
    def __init__(self, operator, lhs, rhs):
        Operation.__init__(self,operator, (lhs, rhs), 
                           styles={"direction":"normal"})
        assert(len(self.operands)==2)
        # The 'lhs' and 'rhs' attributes will access the respective
        # operands, but this is effected in __getattr__ because
        # they will be switched when the 'direction' style is
        # 'reversed'.

    @staticmethod
    def reversedOperatorStr(formatType):
        raise NotImplementedError(
                "'reverseOperatorStr' must be implemented as a class/ "
                "static method for a Relation class to support the "
                "'direction' style of 'reversed'.  It should take a "
                "'formatType' argument which may be 'latex' or 'string'.")
    
    def _formatted(self, formatType, **kwargs):
        '''
        Format the binary relation operation.  Note: it may
        be reversed if the "direction" style is "reversed".
        '''
        wrapPositions=self.wrapPositions()
        justification=self.getStyle('justification')
        fence =  kwargs.get('fence', False)
        subFence =  kwargs.get('subFence', True)
        operator_str = self.operator.formatted(formatType)
        if self.getStyle("direction", "normal")=="reversed":
            operator_str = self.__class__.reversedOperatorStr(formatType)
        operands = self.operands
        return operands.formatted(formatType, 
                                  fence=fence, subFence=subFence, 
                                  operatorOrOperators=operator_str, 
                                  wrapPositions=wrapPositions, justification=justification)
    
    def reversed(self):
        return self.withReverseStyle()
    
    def withDirectionReversed(self):
        if self.getStyle("direction", "normal") == "reverse":
            return self.withStyles(direction="normal")
        return self.withStyles(direction="reversed")
    
    def styleOptions(self):
        options = StyleOptions(self)
        options.add('direction', ("Direction of the relation "
                                  "(normal or reversed)"))
        return options
        
    def _simplify_both_sides(self, *, simplify, assumptions=USE_DEFAULTS):
        '''
        Simplify both sides iff 'simplify' is True.
        '''
        if simplify: return self.simplify_both_sides(assumptions)
        return self
        
    def simplify_both_sides(self, assumptions=USE_DEFAULTS):
        '''
        Simplify both sides of the relation under the give assumptions
        and return the new relation.
        '''
        relation = self
        relation = relation.innerExpr().lhs.simplify(assumptions)
        relation = relation.innerExpr().rhs.simplify(assumptions)
        return relation
    
    def do_something_on_both_sides(self, assumptions=USE_DEFAULTS):
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
    
    def __getattr__(self, name):
        '''
        Methods that end in '_both_sides' (as in performing an operation
        on both sides) can be defined for the relation indirectly via
        any domain known to contain either the left or right side of the 
        relation.  For example, if (x in Complexes) is
        known, (x = y) will have methods called "left_mult_both_sides",
        "divide_both_sides" built from 
        ComplexSet.left_mult_both_sides_of_equals and
        ComplexSet.divide_both_sides_of_equals respectively.
        The method in the domain class must end in 
        "_both_sides_of_<lower-case-relation-class-name>" and match
        this attribute name up to "..._both_sides" as in these
        examples.  The corresponding method built on-the-fly
        for the TransitiveRelation class will take an extra optional 
        'simplify' argument, True by default, for automatically
        simplifying both sides of the new relation.
        
        Also, 'lhs' and 'rhs' attributes are implemented here
        because they will be reversed if the 'direction' style
        is 'reversed'.
        '''
        if name in ('lhs', 'rhs'):
            # For some reason, self.getStyleData('direction', None)
            # leads to errors, but 
            # self._styleData.styles.get('direction', None) is fine.
            if self._styleData.styles.get('direction', 'normal') == 'reversed':
                if name=='lhs': return self.operands[1]
                else: return self.operands[0]
            else:
                if name=='lhs': return self.operands[0]
                else: return self.operands[1]
        
        both_sides_str = '_both_sides'
        if name[-len(both_sides_str):] == both_sides_str:
            from proveit.logic import InSet
            known_memberships = set()
            if self.lhs in InSet.knownMemberships:
                known_memberships.update(InSet.knownMemberships[self.lhs])
            elif self.rhs in InSet.knownMemberships:
                known_memberships.update(InSet.knownMemberships[self.rhs])
            domain_methods = []
            # Append the class name for the domain method name.
            domain_method_name = name + '_of_' + self.__class__.__name__.lower()
            for known_membership in known_memberships:
                domain = known_membership.domain
                if hasattr(domain, domain_method_name):
                    domain_attr = getattr(known_membership.domain,
                                          domain_method_name)
                    # We don't require that the known_membership
                    # is proven under the default assumptions, but
                    # we will try those ones first (the ones at the
                    # end will be popped off first).
                    if known_membership.isSufficient(defaults.assumptions):
                        domain_methods.append((domain, domain_attr))
                    else:
                        domain_methods.insert(0, (domain, domain_attr))
            def transform_both_sides(*args, **kwargs):
                simplify = kwargs.get('simplify', True)
                assumptions =  kwargs.get('assumptions', 
                                          USE_DEFAULTS)
                kwargs.pop('simplify', None)
                while len(domain_methods) > 0:
                    domain, method = domain_methods.pop()
                    try:
                        relation = method(self, *args, **kwargs)
                    except TypeError as e:
                        if len(domain_methods) == 0:
                            raise e
                        # otherwise, there are other methods to try.
                if simplify:
                    relation = relation.innerExpr().lhs.simplify(
                            assumptions)
                    relation = relation.innerExpr().rhs.simplify(
                            assumptions)
                # After doing the transformation, prove that one of
                # the sides (the left side, arbitrarily) is still in 
                # the domain so it will have a known membership for
                # next time.
                InSet(relation.lhs, domain).prove(assumptions)
                return relation
            if len(domain_methods) == 0:
                raise AttributeError # Default behaviour
            # Use the doc string from the wrapped method (any of them), 
            # but append it with a message about 'simplify'.
            transform_both_sides.__doc__ = (
                    domain_methods[0][1].__doc__ + 
                    "The new relation will be simplified by default, unless\n"
                    "\t'simplify=False' is given as a keyword argument.")
            return transform_both_sides
        raise AttributeError # Default behaviour
    
    def __dir__(self):
        '''
        Include the '_both_sides' methods dependent upon the known
        memberships of the left/right sides of the relation
        (see __getattr__).
        '''
        both_sides_str = '_both_sides'
        relation_name_str = '_of_' +  self.__class__.__name__.lower()
        method_end_str = both_sides_str + relation_name_str
        print('method_end_str', method_end_str)
        both_sides_methods = []
        from proveit.logic import InSet
        known_memberships = set()
        if self.lhs in InSet.knownMemberships:
            known_memberships.update(InSet.knownMemberships[self.lhs])
        elif self.rhs in InSet.knownMemberships:
            known_memberships.update(InSet.knownMemberships[self.rhs])
        for known_membership in known_memberships:
            for name in dir(known_membership.domain):
                if name[-len(method_end_str):] == method_end_str:
                    both_sides_methods.append(name[:-len(relation_name_str)])
        return sorted(set(dir(self.__class__) + list(self.__dict__.keys()) 
                          + both_sides_methods))
    

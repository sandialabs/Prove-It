from proveit import prover, equality_prover, defaults, USE_DEFAULTS
from proveit.util import OrderedSet
from .transitivity import TransitiveRelation

class EquivRelation(TransitiveRelation):
    '''
    An EquivRelation is a relation that is transitive, reflexive, and
    symmetric.
    '''
    def __init__(self, operator, lhs, rhs, *, styles):
        return TransitiveRelation.__init__(self, operator, lhs, rhs, 
                                           styles=styles)

    def _record_as_proven(self, judgment):
        '''
        Store known left sides and known right sides
        in class member dictionaries: known_left_sides, known_right_sides
        which will enable transitivity searches.
        '''
        if (not hasattr(self.__class__, 'known_equivalences') 
                or not hasattr(self.__class__, 'known_equivalences')):
            raise NotImplementedError(
                "Expressions derived from EquivRelation should define "
                "'known_equivalences' as class variables")
        self.__class__.known_equivalences.setdefault(
            self.normal_lhs, OrderedSet()).add(judgment)
        self.__class__.known_equivalences.setdefault(
            self.normal_rhs, OrderedSet()).add(judgment)
    
    @classmethod
    def known_relations_from_left(RelationClass, expr, *, 
                                  assumptions=USE_DEFAULTS):
        '''
        For each Judgment that is an SetEquiv involving the given 
        expression on the left hand side, yield the Judgment and the 
        right hand side.
        '''
        for judgment in RelationClass.known_equivalences.get(expr, frozenset()):
            if judgment.lhs == expr:
                if judgment.is_applicable(assumptions):
                    yield (judgment, judgment.rhs)

    @staticmethod
    def known_relations_from_right(RelationClass, expr, *, 
                                   assumptions=USE_DEFAULTS):
        '''
        For each Judgment that is an SetEquiv involving the given 
        expression on the right hand side, yield the Judgment and the
        left hand side.
        '''
        for judgment in RelationClass.known_equivalences.get(expr, frozenset()):
            if judgment.rhs == expr:
                if judgment.is_applicable(assumptions):
                    yield (judgment, judgment.lhs)
    
    @prover
    def derive_reversed(self, **defaults_config):
        '''
        Derive the reverse of this EquivRelation.
        '''
        raise NotImplementedError(
                "%s.derive_reversed must be implemented"%type(self))

    @equality_prover("reversed", "reverse")
    def symmetrization(self, **defaults_config):
        '''
        Equate this EquivRelation with its reversed form.
        '''
        raise NotImplementedError(
                "%s.equate_with_reversed must be implemented"%type(self))

    def _build_canonical_form(self):
        '''
        Returns a form of this operation in which the lhs/rhs are 
        in a deterministically sorted order used to determine equal 
        expressions given the symmetry property of this relation.
        '''
        return type(self)(*sorted([operand.canonical_form() for operand 
                          in self.operands.entries], key=hash))

    @prover
    def _deduce_equality(self, equality, **defaults_config):
        '''
        Deduce EquivRelations are equal by having the same canonical
        form on the same side or opposite sides.
        '''
        if type(equality.rhs) == type(equality.lhs):
            lhs_eq, rhs_eq = equality.lhs, equality.rhs
            lhs_lhs_cf = lhs_eq.lhs.canonical_form()
            lhs_rhs_cf = lhs_eq.rhs.canonical_form()
            rhs_lhs_cf = rhs_eq.lhs.canonical_form()
            rhs_rhs_cf = rhs_eq.rhs.canonical_form()
            if (lhs_lhs_cf == rhs_lhs_cf) and (lhs_rhs_cf == rhs_rhs_cf):
                return equality.conclude_via_direct_substitution()
            if (lhs_lhs_cf == rhs_rhs_cf) and (lhs_rhs_cf == rhs_lhs_cf):
                return self.symmetrization()
        assert False, ("Canonical forms don't match so _deduce_equality "
                       "should not be called")

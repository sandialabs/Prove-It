from proveit import OperationOverInstances, KnownTruth
from proveit import Literal, Operation, ExprList, USE_DEFAULTS
from proveit._common_ import A, B, P, R, S, xx, yy, QQ

class Exists(OperationOverInstances):
    # operator of the Exists operation
    _operator_ = Literal(stringFormat='exists', latexFormat=r'\exists', context=__file__)

    def __init__(self, instanceVarOrVars, instanceExpr, domain=None, domains=None, conditions=tuple()):
        '''
        Create a exists (there exists) expression:
        exists_{instanceVars | condition} instanceExpr
        This expresses that there exists a value of the instanceVar(s) for which the optional condition(s)
        is/are satisfied and the instanceExpr is true.  The instanceVar(s) and condition(s) may be
        singular or plural (iterable).
        '''
        # nestMultiIvars=True will cause it to treat multiple instance variables as nested Exists operations internally
        # and only join them together as a style consequence.
        OperationOverInstances.__init__(self, Exists._operator_, instanceVarOrVars, instanceExpr, domain, domains, conditions, nestMultiIvars=True)

    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for an exists operations.
        '''
        # temporarily insert a return here, short-circuiting the yield
        # see related comments at
        # https://stackoverflow.com/questions/6266561/how-to-write-python-generator-
        # function-that-never-yields-anything
        return
        yield self.deriveNegatedForall # derive the negated forall form

    def negationSideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for a negated exists operation.
        '''
        yield self.deduceNotExists # derive the NotExists form.

    def deduceNotExists(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce notexists_{x | Q(x) P(x) assuming not(exists_{x | Q(x) P(x)),
        where self is exists_{x | Q(x) P(x).
        '''
        raise NotImplementedError("Need to update")
        from .not_exists import NotExists
        notExistsExpr = NotExists(self.instanceVars, self.instanceExpr, domain=self.domain, conditions=self.conditions)
        return notExistsExpr.concludeAsFolded(assumptions)

    def concludeViaExample(self, exampleInstance, assumptions=USE_DEFAULTS):
        '''
        Conclude and return this [exists_{..y.. in S | ..Q(..x..)..} P(..y..)] from P(..x..) and Q(..x..) and ..x.. in S, where ..x.. is the given exampleInstance.
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import existenceByExample
        from proveit.logic import InSet
        if len(self.instanceVars) > 1 and (not isinstance(exampleInstance, ExprList) or (len(exampleInstance) != len(self.instanceVars))):
            raise Exception('Number in exampleInstance list must match number of instance variables in the Exists expression')
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        # P(..x..) where ..x.. is the given exampleInstance
        exampleMapping = {instanceVar:exampleInstanceElem for instanceVar, exampleInstanceElem in zip(self.instanceVars, exampleInstance if isinstance(exampleInstance, ExpressionList) else [exampleInstance])}
        exampleExpr = self.instanceExpr.substituted(exampleMapping)
        # ..Q(..x..).. where ..x.. is the given exampleInstance
        exampleConditions = self.conditions.substituted(exampleMapping)
        if self.hasDomain():
            for iVar in self.instanceVars:
                exampleConditions.append(InSet(iVar, self.domain))
        # exists_{..y.. | ..Q(..x..)..} P(..y..)]
        return existenceByExample.specialize({P_op:P_op_sub, Q_op:Q_op_sub, S:self.domain}, assumptions=assumptions,
                                              relabelMap={xMulti:exampleInstance, yMulti:self.instanceVars}).deriveConsequent(assumptions=assumptions)

    def deriveNegatedForall(self, assumptions=USE_DEFAULTS):
        '''
        From [exists_{x | Q(x)} Not(P(x))], derive and return Not(forall_{x | Q(x)} P(x)).
        From [exists_{x | Q(x)} P(x)], derive and return Not(forall_{x | Q(x)} (P(x) != TRUE)).
        '''
        raise NotImplementedError("Need to update") # temporarily commented out for testing wdc 20190728
        from ._axioms_ import existsDef
        from ._theorems_ import existsNotImpliesNotForall
        from proveit.logic import Not
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if isinstance(self.instanceExpr, Not):
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr.operand
            return existsNotImpliesNotForall.specialize({P_op:P_op_sub, Q_op:Q_op_sub, S:self.domain}, assumptions=assumptions,
                                                        relabelMap={xMulti:self.instanceVars}).deriveConsequent(assumptions)
        else:
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            return existsDef.specialize({P_op:P_op_sub, Q_op:Q_op_sub, S:self.domain}, assumptions=assumptions,
                                        relabelMap={xMulti:self.instanceVars}).deriveRightViaEquivalence(assumptions)

    def substituteDomain(self, superset, assumptions=USE_DEFAULTS):
        '''
        Substitute the domain with a superset.
        From [exists_{x in A| Q(x)} P(x)], derive and return [exists_{x in B| Q(x)} P(x)]
        given A subseteq B.
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import existsInSuperset
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        return existsInSuperset.specialize({P_op:P_op_sub, Q_op:Q_op_sub, A:self.domain, B:superset}, assumptions=assumptions,
                                            relabelMap={xMulti:self.instanceVars, yMulti:self.instanceVars}).deriveConsequent(assumptions)

    def elimDomain(self, assumptions=USE_DEFAULTS):
        '''
        From [exists_{x in S | Q(x)} P(x)], derive and return [exists_{x | Q(x)} P(x)],
        eliminating the domain which is a weaker form.
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import existsInGeneral
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        return existsInGeneral.specialize({P_op:P_op_sub, Q_op:Q_op_sub, S:self.domain}, assumptions=assumptions,
                                           relabelMap={xMulti:self.instanceVars, yMulti:self.instanceVars}).deriveConsequent(assumptions)


    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce, then return, that this exists expression is in the set of BOOLEANS as
        all exists expressions are (they are taken to be false when not true).
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import existsInBool
        P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        return existsInBool.specialize({P_op:P_op_sub, Q_op:Q_op_sub, S:self.domain}, relabelMap={xMulti:self.instanceVars}, assumptions=assumptions)

    def substituteInstances(self, universality, assumptions=USE_DEFAULTS):
        '''
        Derive from this Exists operation, Exists_{..x.. in S | ..Q(..x..)..} P(..x..),
        one that substitutes instance expressions given some
        universality = forall_{..x.. in S | P(..x..), ..Q(..x..)..} R(..x..).
                                            or forall_{..x.. in S | ..Q(..x..)..} P(..x..) = R(..x..).
        Either is allowed in the context of the existential quantifier.
        Derive and return the following type of existential operation assuming universality:
        Exists_{..x.. in S | ..Q(..x..)..} R(..x..)
        Works also when there is no domain S and/or no conditions ..Q...
        '''
        raise NotImplementedError("Need to update")
        from ._theorems_ import existentialImplication, noDomainExistentialImplication
        from proveit import Etcetera
        from proveit.logic import Forall
        from proveit._generic_ import InstanceSubstitutionException
        from proveit._common_ import n, Qmulti, xMulti, yMulti, zMulti, S
        if isinstance(universality, KnownTruth):
            universality = universality.expr
        if not isinstance(universality, Forall):
            raise InstanceSubstitutionException("'universality' must be a forall expression", self, universality)

        if self.instanceExpr in universality.conditions:
            # map from the forall instance variables to self's instance variables
            iVarSubstitutions = {forallIvar:selfIvar for forallIvar, selfIvar in zip(universality.instanceVars, self.instanceVars)}
            firstCondition = universality.conditions[0].substituted(iVarSubstitutions)
            if firstCondition != self.instanceExpr:
                raise InstanceSubstitutionException("The first condition of the 'universality' must match the instance expression of the Exists operation having instances substituted", self, universality)
            if len(universality.instanceVars) != len(self.instanceVars):
                raise InstanceSubstitutionException("'universality' must have the same number of variables as the Exists operation having instances substituted", self, universality)
            if universality.domain != self.domain:
                raise InstanceSubstitutionException("'universality' must have the same domain as the Exists having instances substituted", self, universality)
            if ExpressionList(universality.conditions[1:]).substituted(iVarSubstitutions) != self.conditions:
                raise InstanceSubstitutionException("'universality' must have the same conditions as the Exists operation having instances substituted, in addition to the Exists instance expression", self, universality)
            P_op, P_op_sub = Operation(P, self.instanceVars), self.instanceExpr
            Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
            R_op, R_op_sub = Operation(R, self.instanceVars), universality.instanceExpr.substituted(iVarSubstitutions)
            if self.hasDomain():
                return existentialImplication.specialize({S:self.domain, P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub}, \
                                                        relabelMap={xMulti:universality.instanceVars, yMulti:self.instanceVars, zMulti:self.instanceVars}, assumptions=assumptions).deriveConsequent(assumptions).deriveConsequent(assumptions)
            else:
                return noDomainExistentialImplication.specialize({P_op:P_op_sub, Q_op:Q_op_sub, R_op:R_op_sub},
                                                                   relabelMap={xMulti:universality.instanceVars, yMulti:self.instanceVars, zMulti:self.instanceVars}, assumptions=assumptions).deriveConsequent(assumptions).deriveConsequent(assumptions)
        # Default to the OperationOverInstances version which works with universally quantified equivalences.
        return OperationOverInstances.substitute(self, universality, assumptions=assumptions)

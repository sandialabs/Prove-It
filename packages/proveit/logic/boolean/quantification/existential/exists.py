from proveit import Lambda, Conditional, OperationOverInstances, KnownTruth
from proveit import defaults, Literal, Operation, ExprTuple, USE_DEFAULTS
from proveit._common_ import n, A, B, P, Q, R, S, xx, yy, QQ

class Exists(OperationOverInstances):
    # operator of the Exists operation
    _operator_ = Literal(stringFormat='exists', latexFormat=r'\exists', context=__file__)

    # a dictionary to track Skolem constants chosen with the
    # Exists.choose() method
    skolem_consts_to_existential = dict()
    
    def __init__(self, instanceParamOrParams, instanceExpr, *, 
                 domain=None, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create a exists (there exists) expression:
        exists_{instanceParamOrParams | condition} instanceExpr
        This expresses that there exists a value of the instance parameters(s) 
        for which the optional condition(s) is/are satisfied and the 
        instanceExpr is true.  The instance parameter(s) and condition(s) may 
        be singular or plural (iterable).
        '''
        OperationOverInstances.__init__(
                self, Exists._operator_, instanceParamOrParams, instanceExpr, 
                domain=domain, domains=domains, condition=condition,
                conditions=conditions, _lambda_map=_lambda_map)

    def sideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for an exists operations.
        '''
        return
        yield self.deriveNegatedForall # derive the negated forall form

    def negationSideEffects(self, knownTruth):
        '''
        Side-effect derivations to attempt automatically for a negated exists operation.
        '''
        yield self.deduceNotExists # derive the NotExists form.

    def choose(self, *skolem_constants, print_message=True):
        '''
        From the existential expression
        self = exists_{x_1,...,x_n | Q(x_1,...,x_n)} P(x_1,...,x_n),
        generate Skolem constants a_1,...,a_n in correspondence with
        the instance params x_1,...,x_n. The process will:
        (1) add Q(a_1,...,a_n) and P(a_1,...,a_n) to the default
            assumptions;
        (2) register the Skolem constants a_1,...,a_n in the
            skolem_consts_to_existential dictionary so they can be
            eliminated later using the eliminate() method;
        (3) return the newly-generated assumptions Q(a_1,...,a_n) and
            P(a_1,...,a_n)
        '''
        # Register this particular collection of Skolem constants
        # in the dictionary as a key linking them to this Exists object
        Exists.skolem_consts_to_existential[skolem_constants]=self

        # build the Skolemized versions of the conditions Q and the
        # instance expression P
        repl_dict = {param:skolem_const for param, skolem_const
                     in zip(self.instanceParams, skolem_constants)}
        P_skolem = self.instanceExpr.replaced(repl_dict)
        Q_skolem = self.conditions.replaced(repl_dict)

        # Update the default assumptions with the Skolem versions
        # of the conditions and instance expression
        defaults.assumptions = (*defaults.assumptions, *Q_skolem, P_skolem)
        if print_message:
            print("Creating Skolem 'constant(s)': {0}.\n"
                  "Call the KnownTruth.eliminate{0} to complete the "
                  "Skolemization\n(when the 'constant(s)' are no longer needed).\n"
                  "Adding to defaults.assumptions:".
                  format(skolem_constants, (*Q_skolem)))

        return ExprTuple(*Q_skolem, P_skolem)

    @staticmethod
    def eliminate(skolem_constants, judgment, assumptions=USE_DEFAULTS):
        '''
        For the provided judgment of the form S |– alpha and the tuple
        of Skolem constants skolem_constants that had been specified
        earlier using the Exists.choose(), derive and return a new
        judgment S' |– alpha where all assumptions in S involving only
        the given skolem_constants are now eliminated.
        This process will only work if the provided skolem_constants
        exactly match a set of Skolem constants used earlier in an
        Exists.choose() method to produce the Skolem constant-based
        subset of assumptions you wish to eliminate from S.
        '''
        from proveit import Lambda
        from proveit._common_ import n, P, Q, alpha
        from proveit.logic import And
        from proveit.core_expr_types._common_ import (x_1_to_n, y_1_to_n)
        from proveit.logic.boolean.quantification.existential._theorems_ import (
                skolemElim)
        if skolem_constants not in Exists.skolem_consts_to_existential:
            raise KeyError("In calling Exists.eliminate(), the Skolem "
                           "constants provided were: {}, but you can only "
                           "eliminate Skolem constants that were chosen "
                           "earlier when using Exists.choose() and the "
                           "Skolem constants to be eliminated must appear "
                           "exactly as specified in the original "
                           "Exists.choose() method.".format(skolem_constants))
        existential = Exists.skolem_consts_to_existential[skolem_constants]
        skolem_assumptions = set(existential.choose(
                *skolem_constants, print_message=False))
        assumptions = defaults.checkedAssumptions(assumptions)
        assumptions = [assumption for assumption in assumptions
                       if assumption not in skolem_assumptions]

        _P = Lambda(
                existential.instanceParams, existential.instanceExpr)
        if hasattr(existential, 'condition'):
            _Q = Lambda(existential.instanceParams, existential.condition)
        else:
            # there is no condition but we still need to provide
            # something for _Q so we provide an empty conjunction And()
            _Q = Lambda(
                    existential.instanceParams, And())
        _alpha = judgment
        _n = existential.instanceParams.length(assumptions)
        x_1_to__n = ExprTuple(x_1_to_n.replaced({n:_n}))
        y_1_to__n = ExprTuple(y_1_to_n.replaced({n:_n}))

        # express the judgment as an implication to match details of
        # the skolemElim theorem being instantiated further below
        P_implies_alpha = _alpha.asImplication(
                hypothesis=_P.apply(*skolem_constants))
        # the generalization to further match theorem details
        # can be handled through automation
        # P_implies_alpha.generalize(
        #         skolem_constants,
        #         conditions=[_Q.apply(*skolem_constants)])

        return skolemElim.instantiate(
                {n:_n, P:_P, Q:_Q, alpha:_alpha,
                 x_1_to__n:skolem_constants,
                 y_1_to__n:existential.instanceParams},
                assumptions=assumptions).deriveConsequent(assumptions)
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From this existential quantifier, derive the "unfolded"
        version according to its definition (the negation of
        a universal quantification).
        '''
        from proveit.logic.boolean.quantification.existential._theorems_ \
            import existsUnfolding
        _n = self.instanceParams.length(assumptions)
        _P = Lambda(self.instanceParams, self.operand.body.value)
        _Q = Lambda(self.instanceParams, self.operand.body.condition)
        return existsUnfolding.instantiate(
                {n:_n, P:_P, Q:_Q}, assumptions=assumptions). \
                deriveConsequent(assumptions)
    
    def definition(self, assumptions=USE_DEFAULTS):
        '''
        Return definition of this existential quantifier as an
        equation with this existential quantifier on the left
        and a negated universal quantification on the right.
        '''
        from proveit.logic.boolean.quantification.existential._axioms_ \
            import existsDef
        _n = self.instanceParams.length(assumptions)
        _P = Lambda(self.instanceParams, self.operand.body.value)
        _Q = Lambda(self.instanceParams, self.operand.body.condition)
        return existsDef.instantiate({n:_n, P:_P, Q:_Q}, assumptions=assumptions)
        
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
        if len(self.instanceVars) > 1 and (not isinstance(exampleInstance, ExprTuple) or (len(exampleInstance) != len(self.instanceVars))):
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
        raise NotImplementedError("Need to update")
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
            
            

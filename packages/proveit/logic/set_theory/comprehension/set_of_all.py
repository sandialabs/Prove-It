from proveit import Literal, OperationOverInstances, Operation, ExprTuple, singleOrCompositeExpression, USE_DEFAULTS
from proveit._common_ import x, y, f, P, Q, QQ, S, yy

class SetOfAll(OperationOverInstances):
    # operator of the SetOfAll operation
    _operator_ = Literal(stringFormat='Set', context=__file__)
    _init_argname_mapping_ = {'instanceElement':'instanceExpr'}

    def __init__(self, instanceVarOrVars, instanceElement, domain=None,
                 domains=None, conditions=tuple(), _lambda_map=None):
        '''
        Create an expression representing the set of all
        instanceElement for instanceVar(s) such that the conditions
        are satisfied:
        {instanceElement | conditions}_{instanceVar(s) \in S}
        '''
        # nestMultiIvars=False will ensure it does NOT treat multiple
        # instance variables as nested SetOfAll operations -- that
        # would not make sense (unlike forall, exists, summation, and
        # product where it does make sense).
        OperationOverInstances.__init__(self, SetOfAll._operator_,
                                        instanceVarOrVars, instanceElement,
                                        domain=domain, conditions=conditions,
                                        nestMultiIvars=False,
                                        _lambda_map=_lambda_map)
        self.instanceElement = self.instanceExpr
        if hasattr(self, 'instanceVar'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instanceVars'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires a domain(s)")
        else:
            assert False, ("Expecting either 'instanceVar' or 'instanceVars' "
                           "to be set")

    def _formatted(self, formatType, fence=False, **kwargs):
        outStr = ''
        explicit_conditions = ExprTuple(*self.explicitConditions())
        inner_fence = (len(explicit_conditions) > 0)
        formatted_instance_element = self.instanceElement.formatted(formatType, fence=inner_fence)
        explicit_domains = self.explicitDomains()
        domain_conditions = ExprTuple(*self.domainConditions())
        if formatType == 'latex': outStr += r"\left\{"
        else: outStr += "{"
        outStr += formatted_instance_element
        if len(explicit_conditions) > 0:
            formatted_conditions = explicit_conditions.formatted(
                    formatType, fence=False)
            if formatType == 'latex': outStr += r'~|~'
            else: outStr += ' s.t. ' # such that
            outStr += formatted_conditions
        if formatType == 'latex': outStr += r"\right\}"
        else: outStr += "}"
        outStr += '_{'
        outStr += domain_conditions.formatted(formatType,
                                              operatorOrOperators=',')
        outStr += '}'
        return outStr

    """
    # The below must be updated

    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From (x in {y | Q(y)})_{y in S}, derive and return [(x in S) and Q(x)], where x is meant as the given element.
        From (x in {y | ..Q(y)..})_{y in S}, derive and return [(x in S) and ..Q(x)..], where x is meant as the given element.
        From (x in {f(y) | ..Q(y)..})_{y in S}, derive and return exists_{y in S | ..Q(y)..} x = f(y).
        Also derive x in S, but this is not returned.
        '''
        from ._theorems_ import unfoldComprehension, unfoldBasicComprehension, unfoldBasic1CondComprehension, inSupersetIfInComprehension
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVar), self.conditions
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0]:
            inSupersetIfInComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions) # x in S side-effect
            if len(self.conditions) == 1:
                Q_op, Q_op_sub = Operation(Q, self.instanceVars), self.conditions[0]
                return unfoldBasic1CondComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element},  {y:self.instanceVars[0]}, assumptions=assumptions)
            else:
                return unfoldBasicComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return unfoldComprehension.specialize({S:self.domain,  Q_op:Q_op_sub, f_op:f_sub, x:element}, {yMulti:self.instanceVars}).deriveConclusion(assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From P(x), derive and return (x in {y | P(y)}), where x is meant as the given element.
        '''
        from ._theorems_ import foldComprehension, foldBasicComprehension
        Q_op, Q_op_sub = Operation(Qmulti, self.instanceVars), self.conditions
        if len(self.instanceVars) == 1 and self.instanceElement == self.instanceVars[0] and len(self.conditions) == 1:
            Pop, Psub = Operation(P, self.instanceVars), self.conditions[0]
            return foldBasicComprehension.specialize({S:self.domain, Q_op:Q_op_sub, x:element}, {y:self.instanceVars[0]}, assumptions=assumptions)
        else:
            f_op, f_sub = Operation(f, self.instanceVars), self.instanceElement
            return foldComprehension.specialize({S:self.domain, Q_op:Q_op_sub, f_op:f_sub, x:element}, {yMulti:self.instanceVars}).deriveConclusion(assumptions)
    """

from proveit import (Literal, OperationOverInstances, Operation, ExprTuple,
                     singleOrCompositeExpression, USE_DEFAULTS)
from proveit._common_ import x, y, f, P, Q, QQ, S, yy

class SetOfAll(OperationOverInstances):
    # operator of the SetOfAll operation
    _operator_ = Literal(stringFormat='SetOfAll',
                         latexFormat=r'\textrm{SetOfAll}', context=__file__)
    _init_argname_mapping_ = {'instanceElement':'instanceExpr'}

    # MAYBE ONLY ALLOW A SINGLE PARAMETER??
    def __init__(self, instanceParamOrParams, instanceElement,
                 domain=None, *, domains=None, condition=None,
                 conditions=None, _lambda_map=None):
        '''
        Create an expression representing the set of all
        instanceElement for instance parameter(s) such that the conditions
        are satisfied:
        {instanceElement | conditions}_{instanceParamOrParams \in S}
        '''
        OperationOverInstances.__init__(
                self, SetOfAll._operator_, instanceParamOrParams,
                instanceElement, domain=domain, domains=domains,
                condition=condition, conditions=conditions, _lambda_map=_lambda_map)
        self.instanceElement = self.instanceExpr
        if hasattr(self, 'instanceParam'):
            if not hasattr(self, 'domain'):
                raise ValueError("SetOfAll requires a domain")
        elif hasattr(self, 'instanceParams'):
            if not hasattr(self, 'domains') or None in self.domains:
                raise ValueError("SetOfAll requires a domain(s)")
        else:
            assert False, ("Expecting either 'instanceParam' or 'instanceParams' "
                           "to be set")

    def _formatted(self, formatType, fence=False, **kwargs):
        outStr = ''
        explicit_conditions = ExprTuple(*self.explicitConditions())
        inner_fence = (len(explicit_conditions) > 0)
        formatted_instance_element = self.instanceElement.formatted(
                formatType, fence=inner_fence)
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
        instance_param_or_params = self.instanceParamOrParams
        if explicit_domains == [explicit_domains[0]]*len(explicit_domains):
            # all in the same domain
            outStr += instance_param_or_params.formatted(formatType,
                                                         operatorOrOperators=',',
                                                         fence=False)
            outStr += r' \in ' if formatType=='latex' else ' in '
            outStr += explicit_domains[0].formatted(formatType)
        else:
            outStr += domain_conditions.formatted(formatType,
                                                operatorOrOperators=',',
                                                fence=False)
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

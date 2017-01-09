from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.basiclogic import Equals
from proveit.basiclogic.genericOps import AssociativeOperation
from proveit.common import f, x, y, aEtc, xEtc, yEtc, zEtc, alpha, S
from proveit.linalg.matrixOps import ScalarProd

pkg = __package__

class TensorProd(AssociativeOperation):
    def __init__(self, *operands):
        r'''
        Tensor product of any number of operands.
        '''
        AssociativeOperation.__init__(self, TENSOR_PROD, *operands)
        self.factors = self.operands

    def factor(self, scalar):
        '''
        Factor the given scalar from one of the tensor product scalars.
        '''
        from theorems import factorScalarFromTensorProd
        for k, operand in enumerate(self.operands):
            if isinstance(operand, ScalarProd) and operand.scalar == scalar:
                return factorScalarFromTensorProd.specialize({xEtc:self.operands[:k], y:operand.scaled, zEtc:self.operands[k+1:]}).specialize({alpha:scalar})
        raise ValueError('Scalar not found in any of the tensor product factors')

    def distribute(self, factorIdx):
        '''
        Distribute over the factor at the given index.
        '''
        from theorems import distributeTensorProdOverSum, distributeTensorProdOverSummation
        from proveit.number import Add, Sum
        factor = self.factors[factorIdx]
        if isinstance(factor, Add):
            return distributeTensorProdOverSum.specialize({xEtc:self.factors[:factorIdx], yEtc:factor.terms, zEtc:self.factors[factorIdx+1:]})
        elif isinstance(factor, Sum):
            domain = factor.domain
            summand = factor.summand
            index = factor.index
            return distributeTensorProdOverSummation.specialize({xEtc:self.factors[:factorIdx], Operation(f, index):summand, S:domain, y:index, zEtc:self.factors[factorIdx+1:]})            
        else:
            raise Exception("Don't know how to distribute tensor product over " + str(factor.__class__) + " factor")

    def equateFactors(self, tensorEquality):
        from theorems import tensorProdEquivByElimination
        if not isinstance(tensorEquality, Equals):
            raise ValueError('tensorEquality should be an Equals expression')
        if not isinstance(tensorEquality.lhs, TensorProd) or not isinstance(tensorEquality.rhs, TensorProd):
            raise ValueError("tensorEquality should be an Equals expression of tensor products")
        if len(tensorEquality.lhs.factors) != len(tensorEquality.rhs.factors):
            raise ValueError("tensorEquality should be an Equals expression of tensor products with the same number of factors")
        if self == tensorEquality.rhs:
            # reverse the equality so "self" is on the left
            tensorEquality = tensorEquality.deriveReversed()
        if not self == tensorEquality.lhs:
            raise ValueError("tensorEquality should be an Equals expression of tensor products with 'self' on one side of the equality")
        for k, (factor1, factor2) in enumerate(zip(tensorEquality.lhs.factors, tensorEquality.rhs.factors)):
            if factor1 != factor2:
                if tensorEquality.lhs.factors[:k] != tensorEquality.rhs.factors[:k] or tensorEquality.lhs.factors[k+1:] != tensorEquality.rhs.factors[k+1:]:
                    raise ValueError("tensorEquality should be an Equals expression of tensor products that are the same except for only one factor")
                return tensorProdEquivByElimination.specialize({aEtc:tensorEquality.lhs.factors[:k], x:factor1, y:factor2, zEtc:tensorEquality.lhs.factors[k+1:]})

TENSOR_PROD = Literal(pkg, 'TENSOR_PROD', {STRING: r'otimes', LATEX: r'\otimes'}, operationMaker = lambda operands : TensorProd(*operands))

class TensorExp(Operation):
    def __init__(self, base, exponent):
        r'''
        Tensor exponentiation to any natural number exponent.
        '''
        Operation.__init__(self, TENSOR_EXP, (base, exponent))
        self.base = self.operands[0]
        self.exponent = self.operands[1]
    
    def formatted(self, formatType, fence=True):
        formattedBase = self.base.formatted(formatType, fence=True)
        formattedExp = self.exponent.formatted(formatType, fence=True)
        if formatType == LATEX:
            return formattedBase + '^{\otimes ' + formattedExp + '}'
        elif formatType == STRING:
            return formattedBase + '^{otimes ' + formattedExp + '}'

    def simplification(self, assumptions=frozenset()):
        '''
        For the trivial cases of a one exponent, derive and return this tensor-exponentiated
        expression equated with a simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        from proveit.number.common import zero, one
        from axioms import tensorExpOne
        if self.exponent == one:
            return tensorExpOne.specialize({x:self.base})
            raise ValueError('Only trivial simplification is implemented (tensor exponent of one)')

    def simplified(self, assumptions=frozenset()):
        '''
        For trivial cases, a zero or one exponent or zero or one base,
        derive this exponential expression equated with a simplified form
        and return the simplified form.
        Assumptions may be necessary to deduce necessary conditions for the simplification.
        '''
        return self.simplification(assumptions).rhs
    
TENSOR_EXP = Literal(pkg, 'TENSOR_EXP', {STRING: r'^otimes', LATEX: r'^{\otimes}'}, operationMaker = lambda operands : TensorExp(*operands))

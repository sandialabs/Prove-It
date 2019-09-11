from proveit import USE_DEFAULTS

class CommutativeInnerExprMixin:
    def commutation(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        return self.expr.commutation(initIdx, finalIdx, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)
        
    def commute(self, initIdx=None, finalIdx=None, assumptions=USE_DEFAULTS):
        return self.expr.commutation(initIdx, finalIdx, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)

class AssociativeInnerExprMixin:
    def association(self, startIdx, length, assumptions=USE_DEFAULTS):
        return self.expr.association(startIdx, length, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)

    def associate(self, startIdx, length, assumptions=USE_DEFAULTS):
        return self.expr.association(startIdx, length, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        return self.expr.disassociation(idx, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)

    def disassociate(self, idx, assumptions=USE_DEFAULTS):
        return self.expr.disassociation(idx, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)


class CommutativeAndAssociativeInnerExprMixin(CommutativeInnerExprMixin, AssociativeInnerExprMixin):
    '''
    In addition to the CommutativeInnerExprMixin methods and AssociativeInnerExprMixin methods,
    this will add groupCommutation and groupCommute which rely on commutativity and associativity.
    '''
    def groupCommutation(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        return self.expr.groupCommutation(initIdx, finalIdx, length, disassociate=disassociate, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)

    def groupCommute(self, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
        return self.expr.groupCommutation(initIdx, finalIdx, length, disassociate=disassociate, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)

class DistributiveInnerExprMixin:
    def distribution(self, idx, assumptions=USE_DEFAULTS):
        return self.addition.distribution(idx, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)
    
    def distribute(self, idx, assumptions=USE_DEFAULTS):
        return self.addition.distribution(idx, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)
        
    def factorization(self, theFactor, pull="left", groupFactor=True, assumptions=USE_DEFAULTS):
        return self.addition.factorization(theFactor, pull, groupFactor, assumptions=assumptions).substitution(self.innerExpr, assumptions=assumptions)
    
    def factorize(self, theFactor, pull="left", groupFactor=True, assumptions=USE_DEFAULTS):
        return self.addition.factorization(theFactor, pull, groupFactor, assumptions=assumptions).subRightSideInto(self.innerExpr, assumptions=assumptions)

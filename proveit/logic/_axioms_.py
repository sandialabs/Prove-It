
# coding: utf-8

# In[1]:

from proveit.logic import OperationOverInstances, Forall, Equals, Implies, In
from proveit.common import n, Qetc, xEtc, yEtc, zEtc, etc_QxEtc, etc_QyEtc, etc_QzEtc, f, g, fxEtc, fyEtc, gxEtc, gzEtc, Upsilon, S
from proveit.number.common import Naturals
from proveit.logic.common import n_of_xEtc, n_of_yEtc, n_of_zEtc


# instanceSubstition: For any OperationOverInstance operator $\Upsilon$, such as $\forall$ or $\sum$ or $\prod$, we may substitute an instance expression that is equivalent for all relevant instances with respect to the domain $S$ and conditions $..Q..$.  This could not be implemented with normal substitution in proveit.logic.equals.axioms because that would violate scope restrictions with respect to the instance variables.

# In[3]:

instanceSubstitution =     Forall((Upsilon, Qetc, f, g, S), 
                     Implies(Forall(xEtc, Equals(fxEtc, gxEtc), domain=S, conditions=etc_QxEtc),
                             Equals(OperationOverInstances(Upsilon, yEtc, fyEtc, domain=S, conditions=etc_QyEtc),
                                    OperationOverInstances(Upsilon, zEtc, gzEtc, domain=S, conditions=etc_QzEtc))))
instanceSubstitution

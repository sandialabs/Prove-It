from proveit import Operation, Function, Literal
from proveit.logic import SetMembership

class LinMap(Function):
    '''
    A linear map expression represents the set of linear mappings
    from on vector space to another vector space.
    '''
    
    _operator_ = Literal(string_format=r'LINMAP', 
                         latex_format=r'\mathcal{L}',
                         theory=__file__)

    # Map elements to their known memberships as linear maps.
    known_memberships = dict()

    def __init__(self, from_vspace, to_vspace, *, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, LinMap._operator_, 
                          (from_vspace, to_vspace),
                          styles=styles)
        self.from_vspace = from_vspace
        self.to_vspace = to_vspace

    def membership_object(self, element):
        return LinMapMembership(element, self)


class LinMapMembership(SetMembership):
    '''
    Defines methods that apply to InSet(element, LinMap(X, Y))
    objects via InClass.__getattr__ which calls 
    LinMap.membership_object(element)
    to return a LinMapMembership object.    
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)
        
    def side_effects(self, judgment):
        LinMap.known_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield

        
class LinMapAdd(Operation):
    '''
    Express the addition of linear maps which is defined via
    (S + T)(v) = S(v) + T(v)
    where S, T in LinMap(V, W) and v in V.
    
    We use the same symbol as number addition, but we treat it as
    it's own operation with it's own definition.
    '''

    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, LinMapAdd._operator_, operands,
                          styles=styles)

'''
Generic utilities for Expression, KnownTruth, and Proof objects --
the standard Prove-It objects that are stored and have dependencies
between them.
'''


class _MeaningData:
    '''
    Data to store information for Expression, KnownTruth, and Proof objects
    that can be shared among different instances that have the same "meaning"
    -- same structure independent of style.
    '''
    unique_id_map = dict() # map _unique_id's to UniqueData objects
                        
    def __init__(self, unique_id, unique_rep):
        self._unique_id = unique_id
        self._unique_rep = unique_rep


class _StyleData:
    '''
    Data to store information for Expression, KnownTruth, and Proof objects
    that can be shared among different instances that have the same style as
    well as meaning.  Stores parent-child relationships that can be used to
    update the style of an inner Expression to be reflected in a containing
    Expression, KnownTruth, or Proof.
    '''
    
    unique_id_map = dict() # map _unique_id's to UniqueData objects

    # map object ids to the list of ids
    # that contain it as a direct dependent for the purpose of updating
    # styles (which is why they are stored with ids because different 
    # styles of the same object, in meaning, will have the same hash and 
    # be considered equal).
    parent_map = dict()

    def __init__(self, unique_id, unique_rep):
        self._unique_id = unique_id
        self._unique_rep = unique_rep
    
    def __hash__(self):
        return self._unique_id
    
    def addChild(self, obj, child):
        assert obj._styleData == self # obj style data should correspond with this data
        _StyleData.parent_map.setdefault(id(child), list()).append((obj, id(obj)))    
    
    def updateStyles(self, expr, styles):
        '''
        Update _styles_rep and _styles_id and remove the png and png_path for this Expression object,
        its parent(s), their parent(s), etc (all ancestors whose overall styles will be affected).
        '''
        to_update = [(expr, id(expr))]
        while len(to_update) > 0:
            obj, obj_id = to_update.pop()
            to_update.extend(_StyleData.parent_map.get(id(obj), list())) # its parents must also be updated
            if hasattr(obj._styleData, 'styles'):
                if styles is None:
                    styles = dict(obj._styleData.styles)
                style_rep = obj._generate_unique_rep(lambda o : hex(o._style_id), styles=styles)
            else:
                # styles only apply to Expression objects
                style_rep = obj._generate_unique_rep(lambda o : hex(o._style_id))
            style_data = styleData(style_rep)
            if styles is not None:
                style_data.styles = styles
            styles=None # only use these styles as the base level
            obj.__dict__['_styleData'] = style_data
            obj.__dict__['_style_id'] = style_data._unique_id
            obj.__dict__.pop('png', None) # the png is must be updated to correspond with the new styles
            obj.__dict__.pop('png_path', None)

def uniqueData(DataClass, unique_rep):
    '''
    Find or create unique data that has the given unique representation.
    '''
    unique_id = hash(unique_rep)
    while unique_id in DataClass.unique_id_map and DataClass.unique_id_map[unique_id]._unique_rep != unique_rep:
        unique_id += 1
    if unique_id in DataClass.unique_id_map:
        unique_data = DataClass.unique_id_map[unique_id]
        assert unique_data._unique_rep == unique_rep
        return unique_data # return an existing UniqueData object for the unique_rep
    # create new UniqueData object for the unique_rep
    unique_data = DataClass(unique_id, unique_rep)
    DataClass.unique_id_map[unique_id] = unique_data
    return unique_data

def meaningData(unique_rep):
    return uniqueData(_MeaningData, unique_rep)

def styleData(unique_rep):
    return uniqueData(_StyleData, unique_rep)

def clear_unique_data():
    _MeaningData.unique_id_map.clear()
    _StyleData.unique_id_map.clear()
    _StyleData.parent_map.clear()
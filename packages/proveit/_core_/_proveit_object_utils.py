'''
Generic utilities for Expression, KnownTruth, and Proof objects --
the standard Prove-It objects that are stored and have dependencies
between them.
'''

unique_id_map = dict() # map _unique_id's to _unique_rep's

def makeUniqueId(unique_rep):
    '''
    Generate unique id's from unique representation strings.  This is done
    by hashing the string but we also make sure this hash is globally
    unique by tracking of the generated id's and their associated representation
    strings.  When collisions occur (which should be extremely rare), we simply 
    increment the id until we come to a match or an unused id.
    '''
    unique_id = hash(unique_rep)
    while unique_id in unique_id_map and unique_id_map[unique_id] != unique_rep:
        unique_id += 1
    unique_id_map[unique_id] = unique_rep
    return unique_id


parent_map = dict() # map object ids to the set of objects (with ids) 
                    # that contain it as a direct dependent for the purpose of updating styles 
                    # (which is why they are stored with ids because different styles 
                    # of the same object, in meaning, will have the same hash and 
                    # be considered equal).

def addParent(obj, parent):
    parent_map.setdefault(id(obj), set()).add((parent, id(parent)))    

def updateStyles(expr):
    '''
    Update _styles_rep and _styles_id and remove the png and png_path for this Expression,
    its parent(s), their parent(s), etc (all ancestors whose overall styles will be affected).
    '''
    set_to_update = {(expr, id(expr))}
    while len(set_to_update) > 0:
        obj, obj_id = set_to_update.pop()
        set_to_update.update(parent_map.get(id(obj), set())) # its parents must also be updated
        obj.__dict__['_style_rep'] = obj._generate_unique_rep(lambda o : hex(o._style_id), includeStyle=True)
        obj.__dict__['_style_id'] = makeUniqueId(obj._style_rep)
        obj.__dict__.pop('png', None) # the png is must be updated to correspond with the new styles
        obj.__dict__.pop('png_path', None)

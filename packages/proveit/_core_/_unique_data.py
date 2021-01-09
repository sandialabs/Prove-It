'''
Generic utilities for Expression, Judgment, and Proof objects --
the standard Prove-It objects that are stored and have dependencies
between them.
'''


class _MeaningData:
    '''
    Data to store information for Expression, Judgment, and Proof objects
    that can be shared among different instances that have the same "meaning"
    -- same structure independent of style.
    '''
    unique_id_map = dict()  # map _unique_id's to UniqueData objects

    def __init__(self, unique_id, unique_rep):
        self._unique_id = unique_id
        self._unique_rep = unique_rep


class _StyleData:
    '''
    Data to store information for Expression, Judgment, and Proof objects
    that can be shared among different instances that have the same style as
    well as meaning.  Stores parent-child relationships that can be used to
    update the style of an inner Expression to be reflected in a containing
    Expression, Judgment, or Proof.
    '''

    unique_id_map = dict()  # map _unique_id's to UniqueData objects

    def __init__(self, unique_id, unique_rep):
        self._unique_id = unique_id
        self._unique_rep = unique_rep
        self.styles = dict()

    def __hash__(self):
        return self._unique_id


def unique_data(DataClass, unique_rep):
    '''
    Find or create unique data that has the given unique representation.
    '''
    unique_id = hash(unique_rep)
    while unique_id in DataClass.unique_id_map and DataClass.unique_id_map[
            unique_id]._unique_rep != unique_rep:
        unique_id += 1
    if unique_id in DataClass.unique_id_map:
        unique_data = DataClass.unique_id_map[unique_id]
        assert unique_data._unique_rep == unique_rep
        return unique_data  # return an existing UniqueData object for the unique_rep
    # create new UniqueData object for the unique_rep
    unique_data = DataClass(unique_id, unique_rep)
    DataClass.unique_id_map[unique_id] = unique_data
    return unique_data


def meaning_data(unique_rep):
    return unique_data(_MeaningData, unique_rep)


def style_data(unique_rep):
    return unique_data(_StyleData, unique_rep)


def clear_unique_data():
    _MeaningData.unique_id_map.clear()
    _StyleData.unique_id_map.clear()

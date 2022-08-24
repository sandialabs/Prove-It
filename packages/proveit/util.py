import collections

# Modified from https://stackoverflow.com/questions/1653970/does-python-have-an-ordered-set
class OrderedSet(collections.OrderedDict, collections.MutableSet):
    '''
    An ordered set that iterates in the order things are added
    but doesn't add duplicates.  This is specially designed to allow
    additions during an iteration, and include those additions in the
    iteration, which is useful for our purposes.
    '''
    def __init__(self):
        self._lock_count = 0
        self._to_add = []

    def update(self, *args, **kwargs):
        if kwargs:
            raise TypeError("update() takes no keyword arguments")

        for s in args:
            for e in s:
                 self.add(e)

    def __len__(self):
        return collections.OrderedDict.__len__(self) + len(self._to_add)

    def __iter__(self):
        '''
        Iterate through the set in a way that allows additions as we
        go.  We yield the additions as well and add them properly
        when we finish iterating.
        '''
        if self._lock_count == 0:
            assert len(self._to_add) == 0, "Failed sanity check"
        try:
            yielded = set()
            self._lock_count += 1
            for _x in self.keys():
                yielded.add(_x)
                yield _x
            for _x in self._to_add:
                if _x not in yielded:
                    yielded.add(_x)
                    yield _x
        finally:
            self._lock_count -= 1
            if self._lock_count == 0:
                for _x in self._to_add:
                    self.add(_x)
                self._to_add.clear()

    def add(self, elem):
        if self._lock_count > 0:
            # We are iterating through the elements, so we can't add
            # directly to the set; instead we add them to a temporary
            # holding area.
            self._to_add.append(elem)
        else:
            self[elem] = None

    def __contains__(self, elem):
        '''
        Return True if the element is in the Ordered set, including
        additions that may be in a temporary holding area (if elements
        were added while iterating).
        '''
        if len(self._to_add) > 0:
            assert self._lock_count > 0, "Failed sanity check"
            return (collections.OrderedDict.__contains__(self, elem)
                    or elem in self._to_add)
        return collections.OrderedDict.__contains__(self, elem)
    
    def pop(self):
        if self._lock_count > 0:
            raise NotImplementedError(
                    "Cannot remove an element while iterating over "
                    "an OrderedDict (but adding is allowed)")
        elem = next(iter(self))
        collections.OrderedDict.pop(self, elem)
        return elem

    def discard(self, elem):
        if self._lock_count > 0:
            raise NotImplementedError(
                    "Cannot remove an element while iterating over "
                    "an OrderedDict (but adding is allowed)")
        self.pop(elem, None)

    def __le__(self, other):
        return all(e in other for e in self)

    def __lt__(self, other):
        return self <= other and self != other

    def __ge__(self, other):
        return all(e in self for e in other)

    def __gt__(self, other):
        return self >= other and self != other

    def __repr__(self):
        return 'OrderedSet([%s])' % (', '.join(map(repr, iter(self))))

    def __str__(self):
        return '{%s}' % (', '.join(map(repr, self.keys())))
    
    difference = property(lambda self: self.__sub__)
    difference_update = property(lambda self: self.__isub__)
    intersection = property(lambda self: self.__and__)
    intersection_update = property(lambda self: self.__iand__)
    issubset = property(lambda self: self.__le__)
    issuperset = property(lambda self: self.__ge__)
    symmetric_difference = property(lambda self: self.__xor__)
    symmetric_difference_update = property(lambda self: self.__ixor__)
    union = property(lambda self: self.__or__)

import collections

# Inspired by https://stackoverflow.com/questions/1653970/does-python-have-an-ordered-set
class OrderedSet(collections.MutableSet):
    '''
    An ordered set that iterates in the order things are added
    but doesn't add duplicates.  This is specially designed to allow
    additions during an iteration, and include those additions in the
    iteration, which is useful for our purposes.  We can index into it as
    if it were a list/tuple and we can make it mutable or not.
    '''
    def __init__(self, iterable=None, *, mutable=True):
        self._lst = list()
        self._set = set()
        if iterable is not None:
            self.update(iterable)
        if not mutable:
            self._lst = tuple(self._lst)

    @property
    def mutable(self):
        return isinstance(self._lst, list)

    def update(self, *args):
        if not self.mutable:
            raise TypeError("Cannot update an OrderedSet that is immutable")

        for s in args:
            for e in s:
                if e not in self._set:
                    self._lst.append(e)
                    self._set.add(e)

    def __len__(self):
        return len(self._lst)

    def __iter__(self):
        '''
        Iterate through the set in a way that allows additions as we
        go.  We yield the additions as well and add them properly
        when we finish iterating.
        '''
        return iter(self._lst)

    def add(self, elem):
        if not self.mutable:
            raise TypeError("Cannot add to an OrderedSet that is immutable")
        _set = self._set
        if elem not in _set:
            self._lst.append(elem)
            _set.add(elem)
    
    def __add__(self, other):
        '''
        Concatenate with any other iterable.
        '''
        combined = OrderedSet(self)
        combined.update(other)
        return combined

    def __getitem__(self, idx):
        return self._lst[idx]

    def __contains__(self, elem):
        '''
        Return True if the element is in the Ordered set, including
        additions that may be in a temporary holding area (if elements
        were added while iterating).
        '''
        return elem in self._set
    
    def discard(self, elem):
        if not self.mutable:
            raise TypeError("Cannot discard an element from an OrderedSet "
                            "that is immutable")
        self._set.discard(elem)
        self._lst.remove(elem)

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
        return '{%s}' % (', '.join(map(repr, iter(self))))
    
    difference = property(lambda self: self.__sub__)
    difference_update = property(lambda self: self.__isub__)
    intersection = property(lambda self: self.__and__)
    intersection_update = property(lambda self: self.__iand__)
    issubset = property(lambda self: self.__le__)
    issuperset = property(lambda self: self.__ge__)
    symmetric_difference = property(lambda self: self.__xor__)
    symmetric_difference_update = property(lambda self: self.__ixor__)
    union = property(lambda self: self.__or__)

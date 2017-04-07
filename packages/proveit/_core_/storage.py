import hashlib, os
import re

class Storage:
    def __init__(self, directory='', refCounted=False):
        self.directory = directory
        if directory != '' and not os.path.isdir(self.directory):
            # make the directory for the storage
            os.makedirs(directory)
        self.refCounted = refCounted
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    def _retrieve_png(self, proveItObject, latex, configLatexToolFn, distinction=''):
        '''
        Find the .png file for the stored Expression or KnownTruth.
        If distinction is provided, this is an extra string that decorates
        the filename to distinguish it from the basic png of an Expression
        ['info' for exprInfo() png, 'details' for exprInfo(details=True) png].
        Create it if it did not previously exist using _generate_png.
        Return the png data and path where the png is stored (or None
        if self.directory is None such that it is not stored).
        '''
        if self.directory is None:
            return self._generate_png(latex, configLatexToolFn), None # don't do any storage
        pv_it_filename = self._retrieve(proveItObject)
        # generate the latex and png file paths, from pv_it_filename and the distinction 
        latex_path = os.path.join(self.directory, '_pv_it_', pv_it_filename[:-6] + distinction + '.latex')
        png_path = os.path.join(self.directory, '_pv_it_', pv_it_filename[:-6] + distinction + '.png')
        # check if the latex file exists, is consistent with the given latex string, and if the png
        # file exists.
        if os.path.isfile(latex_path):
            # latex file exists.  read it ans see if it the same as the given latex string
            with open(latex_path) as latex_file:
                if latex_file.read() == latex:
                    # the latex files are the same, try to read the png file
                    if os.path.isfile(png_path):                        
                        # png file exists.  read and return the data.
                        with open(png_path, 'rb') as png_file:
                            return png_file.read(), png_path
        # store the latex string in the latex file
        with open(latex_path, 'wb') as latex_file:
            latex_file.write(latex)
        # generate, store and return the png file
        png = self._generate_png(latex, configLatexToolFn)
        with open(png_path, 'wb') as png_file:
            png_file.write(png)
        return png, png_path
    
    def _generate_png(self, latex, configLatexToolFn):
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        png = latex_to_png(latex, backend='dvipng', wrap=True)
        if png is None:
            raise Exception("Unable to use 'dvipng' backend to compile LaTeX.  Be sure a LaTeX distribution is installed.")
        return png
       
    def _proveItObjId(self, proveItObject):
        '''
        Retrieve a unique id for the Prove-It object based upon its pv_it filename from calling _retrieve.
        '''
        # Retrieve pv_it files for the list of objects
        pv_it_filename = self._retrieve(proveItObject)
        # (replace os.path.sep within pv_it file paths with '/' to make this OS neutral just in case)
        return '/'.join(pv_it_filename.split(os.path.sep))
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It object.
        '''
        from proveit import Expression, KnownTruth, Proof
        prefix = None
        if isinstance(proveItObject, Expression):
            prefix = '' # No prefix for Expressions
        elif isinstance(proveItObject, KnownTruth):
            prefix = 'KnownTruth:' # prefix to indicate that it is a KnownTruth
        elif isinstance(proveItObject, Proof):
            prefix = 'Proof:' # prefix to indicate that it is a Proof
        else:
            raise NotImplementedError('Strorage only implemented for Expressions, Statements (effectively), and Proofs')
        # generate a unique representation using Prove-It object ids for this storage to
        # represent other referenced Prove-It objects 
        return prefix + proveItObject._generate_unique_rep(self._proveItObjId)
    
    def _extractReferencedObjIds(self, unique_rep):
        '''
        Given a unique representation string, returns the list of Prove-It objects
        that are referenced.
        '''
        from proveit import Expression, KnownTruth, Proof
        if unique_rep[:6] == 'Proof:':
            return Proof._extractReferencedObjIds(unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            return KnownTruth._extractReferencedObjIds(unique_rep[11:])
        else:
            # Assumed to be an expression then
            return Expression._extractReferencedObjIds(unique_rep)

    def _addReference(self, proveItObjId):
        '''
        Increment the reference count of the prove-it object with the given
        storage identifier.  The .pv_it file is  updated with the new 
        reference count.
        '''
        if not self.refCounted:
            raise Exception("Cannot add a reference if reference counted wasn't enabled")
        # replace '/' with os.path.sep within the Prove-It object id to object the filename
        pv_it_filename = os.path.sep.join(proveItObjId.split('/'))
        pv_it_dir = os.path.join(self.directory, '_pv_it_')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            refCount = int(refCount)
            refCount += 1
            # change the reference count in the file
            with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f2:
                f2.write(str(refCount)+'\n')
                f2.write(str(rep))
                        
    def _removeReference(self, proveItObjId):
        '''
        Decrement the reference count of the prove-it object with the given
        storage identifier.  If the reference count goes down to zero, then
        the files storing this prove-it object's data will be deleted
        (and the directory if nothing else is in it).  Otherwise, the
        .pv_it file is simply updated with the new reference count.
        '''
        if not self.refCounted:
            raise Exception("Cannot remove a reference if reference counted wasn't enabled")
        # replace '/' with os.path.sep within the Prove-It object id to object the filename
        pv_it_filename = os.path.sep.join(proveItObjId.split('/'))
        pv_it_dir = os.path.join(self.directory, '_pv_it_')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            refCount = int(refCount)
            refCount -= 1
        if refCount == 0:
            # Reference count down to zero.  Remove references to
            # referenced objects and then delete this prove-it object
            # and everything associated with it.
            for objId in self._extractReferencedObjIds(rep):
                self._removeReference(objId)
            # remove all files associated with this prove-it object 
            # and perhaps the entire directory.
            relpath, filename = os.path.split(pv_it_filename)
            fileroot = filename[:-6]
            for filename in os.listdir(os.path.join(pv_it_dir, relpath)):
                if filename[:len(fileroot)] == fileroot:
                    os.remove(os.path.join(pv_it_dir, relpath, filename))
            if len(os.listdir(os.path.join(pv_it_dir, relpath))) == 0:
                # the directory is now empty.  remove it.
                os.rmdir(os.path.join(pv_it_dir, relpath))
        else:
            # change the reference count in the file
            with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f:
                f.write(str(refCount)+'\n')
                f.write(str(rep))

    
    def _retrieve(self, proveItObject):
        '''
        Find the .pv_it file for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the .pv_it filename, relative to
        the .pv_it directory.
        '''
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        pv_it_dir = os.path.join(self.directory, '_pv_it_')
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        if not os.path.exists(pv_it_dir):
            os.mkdir(pv_it_dir)
        hash_path = os.path.join(pv_it_dir, rep_hash)
        if not os.path.exists(hash_path):
            os.mkdir(hash_path)
        # check for existing files in this hash value sub-directory to see if the right one is there
        for expr_file in os.listdir(hash_path):
            if expr_file[-6:] == '.pv_it':
                pv_it_filename = os.path.join(rep_hash, expr_file)
                with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
                    contents = f.read()
                    if self.refCounted:
                        refCount, rep = contents.split('\n') 
                    else: rep = contents
                    if rep == unique_rep:
                        # an existing file contains the exported expression
                        self._pv_it_filename = pv_it_filename
                        # remember this for next time
                        self._proveItObjects[proveItObject] = pv_it_filename
                        return pv_it_filename
        # does not exist, create a new file (checking against an unlikely collision)
        index = 0
        while os.path.exists(os.path.join(hash_path, str(index) + '.pv_it')):
            index += 1
        pv_it_filename = os.path.join(rep_hash, str(index) + '.pv_it')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f:
            if self.refCounted:
                # first write a reference count of 0 (until a reference is added)
                f.write(str(0) + '\n')
            f.write(unique_rep) # write the unique representation to a file
        # increment reference counts of the referenced objects
        # (if reference counting is enabled)
        if self.refCounted:
            for objId in self._extractReferencedObjIds(unique_rep):
                self._addReference(objId)
        # remember this for next time
        self._proveItObjects[proveItObject] = pv_it_filename
        return pv_it_filename
    
    def makeExpression(self, exprId):
        import importlib
        exprClassMap = dict() # map expression class strings to Expression class objects
        def importFn(exprClassStr):
            splitExprClass = exprClassStr.split('.')
            module = importlib.import_module('.'.join(splitExprClass[:-1]))
            exprClassMap[exprClassStr] = getattr(module, splitExprClass[-1])
        def exprBuilderFn(exprClassStr, exprInfo, subExpressions):
            return exprClassMap[exprClassStr].make(exprInfo, subExpressions)
        return self._makeExpression(exprId, importFn, exprBuilderFn)
    
    def _makeExpression(self, exprId, importFn, exprBuilderFn):
        # (replace '/' within exprId with os.path.sep to convert it to a file name
        # regardless of OS).
        from proveit import Expression
        from _dependency_graph import orderedDependencyNodes
        pv_it_dir = os.path.join(self.directory, '_pv_it_') 
        exprClassStrs = dict() # map expr-ids to Expression class string representations
        coreInfoMap = dict() # map expr-ids to core information
        subExprIdsMap = dict() # map expr-ids to list of sub-expression ids 
        masterExprId = exprId
        def getSubExprIds(exprId):
            pv_it_filename = os.path.sep.join(exprId.split('/'))
            with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
                # extract the unique representation from the pv_it file
                contents = f.read()
                if self.refCounted:
                    refCount, unique_rep = contents.split('\n') 
                else: unique_rep = contents
                # extract the Expression class from the unique representation 
                exprClassStrs[exprId] = Expression._extractExprClass(unique_rep)
                # extract the Expression "core information" from the unique representation
                coreInfoMap[exprId] = Expression._extractCoreInfo(unique_rep)
                # get the sub-expressions all sub-expressions
                subExprIdsMap[exprId] = Expression._extractReferencedObjIds(unique_rep)
                return subExprIdsMap[exprId]
        exprIds = orderedDependencyNodes(exprId, getSubExprIds)
        for exprId in reversed(exprIds):
            importFn(exprClassStrs[exprId])
        builtExprMap = dict() # map expr-ids to "built" expressions (whatever exprBuilderFn returns)
        for exprId in reversed(exprIds):
            subExpressions =  [builtExprMap[subExprId] for subExprId in subExprIdsMap[exprId]]
            builtExprMap[exprId] = exprBuilderFn(exprClassStrs[exprId], coreInfoMap[exprId], subExpressions)
        return builtExprMap[masterExprId]
    """
            
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            # extract the unique representation from the pv_it file
            contents = f.read()
            if self.refCounted:
                refCount, unique_rep = contents.split('\n') 
            else: unique_rep = contents
            # extract the Expression class from the unique representation 
            exprClass = Expression._exprClass(unique_rep)
            # determine the appropriate path for the Expression class
            exprClassPaths[exprClass] = ...
            # recurse for all sub-expressions
            for objId in self._referencedObjIds(unique_rep):
                exprClassPaths(objId, exprClassPaths)
        return 
    """ 
        
    
    def clear(self):
        '''
        Clear the .pvit subdirectory of the storage directory.
        The effect is that expression images will need to be
        regenerated.
        '''
        self._proveItObjects.clear()
        pv_it_dir = os.path.join(self.directory, '_pv_it_')
        if not os.path.isdir(pv_it_dir): return
        for hash_dir in os.listdir(pv_it_dir):
            hash_path = os.path.join(pv_it_dir, hash_dir)
            for pv_it_file in os.listdir(hash_path):
                os.remove(os.path.join(hash_path, pv_it_file))
            os.rmdir(hash_path)
        os.rmdir(pv_it_dir)
    
    def __setattribute__(self, item, value):
        if item == 'storage' and value != self.storage:
            # if the storage is change, _expr_pv_its becomes obsolete
            self._expr_pv_its.clear() # start fresh
        self.__setattr__(item, value)
    
storage = Storage()

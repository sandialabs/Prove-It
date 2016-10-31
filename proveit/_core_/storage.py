import hashlib, os
import re

class Storage:
    def __init__(self, directory='', refCounted=False):
        self.directory = directory
        if directory != '' and not os.path.isdir(self.directory):
            # make the directory for the storage
            os.makedirs(directory)
        self.refCounted = True
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    def _retrieve_png(self, proveItObj, latex, configLatexToolFn, distinction=''):
        '''
        Find the .png file for the stored Expression, KnownTruth, or Proof.
        If distinction is provided, this is an extra string that decorates
        the filename to distinguish it from the basic png of an Expression
        ['info' for exprInfo() png, 'details' for exprInfo(details=True) png].
        Create it if it did not previously exist using pngGenFn.
        If it existed or was generated, read the .png file; otherwise return None.
        '''
        if self.directory is None:
            return self._generate_png(latex, configLatexToolFn) # don't do any storage
        pv_it_filename = self._retrieve(proveItObj)
        # generate the latex and png file paths, from pv_it_filename and the distinction 
        latex_path = os.path.join(self.directory, '.pv_it', pv_it_filename[:-6] + distinction + '.latex')
        png_path = os.path.join(self.directory, '.pv_it', pv_it_filename[:-6] + distinction + '.png')
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
                            return png_file.read()
        # store the latex string in the latex file
        with open(latex_path, 'wb') as latex_file:
            latex_file.write(latex)
        # generate, store and return the png file
        png = self._generate_png(latex, configLatexToolFn)
        with open(png_path, 'wb') as png_file:
            png_file.write(png)
        return png
    
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
        # (replace os.path.sep within pv_it file paths with ':' to make this OS neutral just in case)
        return ':'.join(pv_it_filename.split(os.path.sep))
    
    def _proveItObjUniqueRep(self, proveItObject):
        '''
        Generate a unique representation string for the given Prove-It object.
        '''
        from proveit import Expression, KnownTruth, Proof
        if isinstance(proveItObject, KnownTruth):
            # To uniquely identify a KnownTruth for displaying purposes, we need its Expression and list of assumptions
            knownTruth = proveItObject
            assumptions = knownTruth.assumptions
            return 'KnownTruth:' + self._proveItObjId(knownTruth.expr) + '[' + ','.join(self._proveItObjId(assumption) for assumption in assumptions) + ']'          
        elif isinstance(proveItObject, Expression):
            # This unique_rep differs from expr._unique_rep because it is designed to avoid
            # collisions in storage which may differ from in-memory collisions (collisions are unlikely, but let's stay safe).
            expr = proveItObject
            return str(expr.__class__) + '[' + ','.join(expr._coreInfo) + '];[' + ','.join(self._proveItObjId(subExpr) for subExpr in expr.subExprIter()) + ']'
        elif isinstance(proveItObject, Proof):
            # The Proof is uniquely identified by its provenTruth and its requiredProofs (recursively)
            proof = proveItObject
            return 'Proof:' + self._proveItObjId(proof.provenTruth) + '[' + ','.join(self._proveItObjId(requiredProof) for requiredProof in proof.requiredProofs) + ']'
        else:
            raise NotImplementedError('Strorage only implemented for Expressions, Statements (effectively), and Proofs')
    
    def _referencedObjIds(self, unique_rep):
        '''
        Given a unique representation string, returns the list of Prove-It objects
        that are referenced.
        '''
        if unique_rep[:6] == 'Proof:':
            return re.split("\[|,|\]",unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            return re.split("\[|,|\]",unique_rep[11:])
        else:
            # Assumed to be an expression then
            subExprs = unique_rep.split(';')[-1]
            return re.split("\[|,|\]",subExprs)            
            
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
        # replace ':' with os.path.sep within the Prove-It object id to object the filename
        pv_it_filename = os.path.sep.join(proveItObjId.split(':'))
        pv_it_dir = os.path.join(self.directory, '.pv_it')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'r') as f:
            contents = f.read()
            refCount, rep = contents.split('\n') 
            refCount = int(refCount)
            refCount -= 1
            if refCount == 0:
                # Reference count down to zero.  Remove references to
                # referenced objects and then delete this prove-it object
                # and everything associated with it.
                for objId in self._referencedObjIds(rep):
                    self._removeReference(objId)
                # remove all files associated with this prove-it object 
                # and perhaps the entire directory.
                relpath, filename = os.path.split(pv_it_filename)
                fileroot = filename[:-6]
                for filename in os.listdir(os.path.join(pv_it_dir, relpath)):
                    if filename[:len(fileroot)] == fileroot:
                        os.remove(os.path.join(pv_it_dir, relpath, filename))
                if len(os.listdir(pv_it_dir, relpath)) == 0:
                    # the directory is now empty.  remove it.
                    os.rmdir(os.path.join(pv_it_dir, relpath))
            else:
                # change the reference count in the file
                with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f2:
                    f2.write(str(refCount+1)+'\n')
                    f2.write(str(rep))
    
    def _retrieve(self, proveItObject):
        '''
        Find the .pv_it file for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the .pv_it filename, relative to
        the .pv_it directory.
        '''
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        pv_it_dir = os.path.join(self.directory, '.pv_it')
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
                    rep = contents = f.read()
                    if self.refCounted:
                        refCount, rep = contents.split('\n') 
                        refCount = int(refCount)
                    if rep == unique_rep:
                        # an existing file contains the exported expression
                        self._pv_it_filename = pv_it_filename
                        if self.refCounted:
                            # update the reference counter in the file
                            with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f2:
                                f2.write(str(refCount+1)+'\n')
                                f2.write(str(rep))
                        return pv_it_filename
        # does not exist, create a new file (checking against an unlikely collision)
        index = 0
        while os.path.exists(os.path.join(hash_path, str(index) + '.pv_it')):
            index += 1
        pv_it_filename = os.path.join(rep_hash, str(index) + '.pv_it')
        with open(os.path.join(pv_it_dir, pv_it_filename), 'w') as f:
            if self.refCounted:
                # first write a reference count of 1
                f.write(str(1) + '\n')
            f.write(unique_rep) # write the unique representation to a file
        # remember this for next time
        self._proveItObjects[proveItObject] = pv_it_filename
        return pv_it_filename
        
    
    def clear(self):
        '''
        Clear the .pvit subdirectory of the storage directory.
        The effect is that expression images will need to be
        regenerated.
        '''
        self._proveItObjects.clear()
        pv_it_dir = os.path.join(self.directory, '.pv_it')
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

import hashlib, os
import shutil
import sys
import importlib
import itertools
import json
import re

class Storage:
    '''
    Manages the __pv_it directory of a Context, the distributed database
    of expressions, axioms, theorems, and proofs.
    '''
    
    def __init__(self, context, directory):
        from .context import Context, ContextException
        if not isinstance(context, Context):
            raise ContextException("'context' should be a Context object")
        self.context = context
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '__pv_it')
        if not os.path.isdir(self.pv_it_dir):
            # make the directory for the storage
            os.makedirs(self.pv_it_dir)
        
        if self.context.isRoot():
            # If this is a root context, let's add the directory above the root
            # to sys.path if it is needed.
            # try to import the root context; if it fails, we
            # need to add the path
            add_path = True # may set to False below
            try:
                if os.path.relpath(os.path.split(importlib.import_module(self.context.name).__file__)[0], self.directory) == '.':
                    add_path = False
            except:
                pass # keep add_path as True
            if add_path: # add the path to sys.path
                root_package_path = os.path.abspath(os.path.join(self.directory, '..'))
                sys.path.insert(1, root_package_path)
            # indicate whether or not we needed to add the path to sys.path
            self.addedPath = add_path             
            
            # set of context root names that are referenced
            self.referencedContextRoots = set()
            # associate the context name with the directory
            Context.setRootContextPath(context.name, directory)
            # map context names to paths for other known root contexts in paths.txt
            self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
            if os.path.isfile(self.pathsFilename):
                with open(self.pathsFilename) as pathsFile:
                    for pathLine in pathsFile.readlines():
                        contextName, path = pathLine.split()
                        if contextName == '.':
                            if path != directory:
                                # the directory of the context associated with 
                                # this storage object has changed.
                                self._updatePath()
                        else:
                            Context.setRootContextPath(contextName, path)
                            self.referencedContextRoots.add(contextName)
            else:
                with open(self.pathsFilename, 'w') as pathsFile:
                    # the first entry indicates the directory of this path
                    pathsFile.write('. ' + directory + '\n')

        # map expression objects to special expression kind and name
        # for the associated context (the kind is 'common', 'axiom', or 'theorem').
        self.specialExpressions = dict()
                        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    def _updatePath(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Context's.
        '''
        from .context import Context
        myContextName = self.context.name
        # update the local paths.txt
        self._changePath('.', self.directory)
        # update the paths.txt wherever there is a mutual reference
        self.pathsFilename = os.path.join(self.pv_it_dir, 'paths.txt')
        with open(self.pathsFilename) as pathsFile:
            for pathLine in pathsFile.readlines():
                contextName, path = pathLine.split()
                if contextName != '.':
                    Context.getContext(contextName)._storage._changePath(myContextName, self.directory)
    
    def _changePath(self, movedContextName, newPath):
        '''
        Change the path of the movedContextName to the newPath.
        '''
        # read in the paths.txt
        with open(self.pathsFilename) as pathsFile:
           prevLines = pathsFile.readlines()
        # re-write the paths.txt with one of the contexts' path changed
        with open(self.pathsFilename, 'w') as pathsFile:
            for pathLine in prevLines:
                contextName, path = pathLine.split()
                if contextName == movedContextName:
                    path = newPath
                pathsFile.write(contextName + ' ' + path + '\n')
        
    def includeReference(self, otherStorage):
        '''
        Include a path reference from a root Context to another root Context,
        both in the referencedContextRoots set and in the paths.txt file. 
        '''
        otherContextName = otherStorage.context.name
        if otherContextName not in self.referencedContextRoots:
            with open(self.pathsFilename, 'a') as pathsFile:
                pathsFile.write(otherContextName + ' ' + otherStorage.directory + '\n')
            self.referencedContextRoots.add(otherContextName)
        
    def retrieve_png(self, expr, latex, configLatexToolFn):
        '''
        Find the expr.png file for the stored Expression.
        Create it if it did not previously exist using _generate_png.
        Return the png data and path where the png is stored as a tuple.
        '''
        from proveit import Expression
        if expr in Expression.contexts and Expression.contexts[expr] != self.context:
            return Expression.contexts[expr]._stored_png(expr, latex, configLatexToolFn)
        (context, hash_directory) = self._retrieve(expr)
        assert context==self.context, "How did the context end up different from expected??"
        # generate the latex and png file paths, from pv_it_filename and the distinction 
        latex_path = os.path.join(self.pv_it_dir, hash_directory, 'expr.latex')
        png_path = os.path.join(self.pv_it_dir, hash_directory, 'expr.png')
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
        '''
        Generate the png image for the given latex using the given latex
        configuration function.
        '''
        from IPython.lib.latextools import latex_to_png, LaTeXTool
        LaTeXTool.clear_instance()
        lt = LaTeXTool.instance()
        lt.use_breqn = False
        png = latex_to_png(latex, backend='dvipng', wrap=True)
        if png is None:
            raise Exception("Unable to use 'dvipng' backend to compile LaTeX.  Be sure a LaTeX distribution is installed.")
        return png
       
    def _proveItStorageId(self, proveItObjectOrId):
        '''
        Retrieve a unique id for the Prove-It object based upon its pv_it filename from calling _retrieve.
        '''
        if isinstance(proveItObjectOrId, str):
            return proveItObjectOrId
        else:
            (context, hash_directory) = self._retrieve(proveItObjectOrId)
            if context != self.context:
                self.context._includeMutualReferences(context)
                return context.name + '.' + hash_directory
            else:
                return hash_directory
    
    def _split(self, proveItStorageId):
        '''
        Split the given storage-id into a context name and the hash directory.
        The context may be implicit (if in the same context it is referenced),
        in which case the context name will be empty.
        '''
        if '.' in proveItStorageId:
            # in a different context
            splitId = proveItStorageId.split('.')
            context_name, hash_directory = '.'.join(splitId[:-1]), splitId[-1]
            return context_name, hash_directory
        return '', proveItStorageId
            
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with the given
        storage id.
        '''
        from .context import Context
        context_name, hash_directory = self._split(proveItStorageId)
        if context_name == '':
            return os.path.join(self.context._storage.pv_it_dir, hash_directory)
        else:            
            pv_it_dir = Context.getContext(context_name)._storage.pv_it_dir
            return os.path.join(pv_it_dir, hash_directory)
    
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
        return prefix + proveItObject._generate_unique_rep(self._proveItStorageId)
    
    def _extractReferencedStorageIds(self, unique_rep, context_name=''):
        '''
        Given a unique representation string, returns the list of Prove-It
        storage ids of objects that are referenced.  A context_name may be
        given; if the Context is the one associated with this Storage object
        then the default may be used.
        '''
        from proveit import Expression, KnownTruth, Proof
        if unique_rep[:6] == 'Proof:':
            storage_ids = Proof._extractReferencedObjIds(unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            storage_ids = KnownTruth._extractReferencedObjIds(unique_rep[11:])
        else:
            # Assumed to be an expression then
            storage_ids = Expression._extractReferencedObjIds(unique_rep)
        def relativeToExplicitPrefix(exprId, contextName):
            # if the exprId is relative to the context it is in, make the context explicit
            if '.' in exprId: return exprId # already has an explicit context
            return contextName + '.' + exprId
        if context_name != '':
            return [relativeToExplicitPrefix(storage_id, context_name) for storage_id in storage_ids]
        return storage_ids

    def _addReference(self, proveItStorageId):
        '''
        Increment the reference count of the prove-it object with the given
        storage identifier.  The ref_count.txt file is updated with the new 
        reference count.
        '''        
        hash_path = self._storagePath(proveItStorageId)
        file_path = os.path.join(hash_path, 'ref_count.txt')
        with open(file_path, 'r') as f:
            # read the current reference count
            refCount = int(f.read().strip()) + 1
            # change the reference count in the file
            with open(file_path, 'w') as f2:
                f2.write(str(refCount) + '\n')

    def _getRefCount(self, proveItStorageId):
        '''
        Return the reference coult of the prove-it object with the given
        storage identifier.
        '''        
        hash_path = self._storagePath(proveItStorageId)
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            return int(f.read().strip())
           
    def _removeReference(self, proveItStorageId, removingSpecialExpr=False):
        '''
        Decrement the reference count of the prove-it object with the given
        storage identifier.  If the reference count goes down to zero, then
        the files storing this prove-it object's data will be deleted
        (and the directory if nothing else is in it).  Otherwise, the
        ref_count.txt file is simply updated with the new reference count.
        Return the new reference count and path to the hash directory.
        '''
        context_name, hash_directory = self._split(proveItStorageId)
        hash_path = self._storagePath(proveItStorageId)
        if not os.path.isdir(hash_path):
            print "WARNING: Referenced '__pv_it' path, for removal, does not exist: %s"%hash_path
            return # not there -- skip it
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            ref_count = int(f.read().strip()) - 1
        if ref_count <= 0:
            # Reference count down to zero (or less).  Remove references to
            # referenced objects and then delete this prove-it object from
            # storage and everything associated with it.
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                rep = f.read()
            for objId in self._extractReferencedStorageIds(rep, context_name):
                self._removeReference(objId)
            # remove the entire directory storing this prove-it object
            self._erase_hash_directory(hash_path)
        else:
            # change the reference count in the file
            with open(os.path.join(hash_path, 'ref_count.txt'), 'w') as f:
                f.write(str(ref_count)+'\n')
            if removingSpecialExpr:
                # there are other references to the expression, but it is no
                # longer a special expression (presumably)
                name_path = os.path.join(hash_path, 'name.txt')
                if os.path.isfile(name_path):
                    os.remove(name_path)
    
    def _erase_hash_directory(self, hash_path):
        '''
        Remove the entire directory storing this prove-it object.
        '''
        for filename in os.listdir(hash_path):
            path = os.path.join(hash_path, filename)
            if os.path.isdir(path):
                for sub_filename in os.listdir(path):
                    os.remove(os.path.join(path, sub_filename))
                os.rmdir(path)
            else:
                os.remove(path)
        os.rmdir(hash_path)
        
    
    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the (context, hash_directory)
        pair, where the hash_directory is the directory name (within the context's
        __pv_it directory) based upon a hash of the unique representation.
        '''
        from proveit import Expression
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        if isinstance(proveItObject, Expression):
            expr = proveItObject
            if expr in Expression.contexts and Expression.contexts[expr] != self.context:                
                # stored in a different context
                return Expression.contexts[expr]._storage._retrieve(proveItObject)
        elif hasattr(proveItObject, 'context') and proveItObject.context != self.context:
            # stored in a different context
            return proveItObject.context._storage._retrieve(proveItObject)
        pv_it_dir = self.pv_it_dir
        unique_rep = self._proveItObjUniqueRep(proveItObject)
        # hash the unique representation and make a sub-directory of this hash value
        rep_hash = hashlib.sha1(unique_rep).hexdigest()
        if not os.path.exists(pv_it_dir):
            os.mkdir(pv_it_dir)
        hash_path = os.path.join(pv_it_dir, rep_hash)
        # append the hash value with an index, avoiding collisions (that should
        # be astronomically rare, but let's not risk it).
        index = 0
        while os.path.exists(hash_path + str(index)):
            indexed_hash_path = hash_path + str(index)
            unique_rep_filename = os.path.join(indexed_hash_path, 'unique_rep.pv_it')
            if not os.path.isfile(unique_rep_filename):
                # folder does not contain a unique_rep.pv_it file;
                # assume it was not erased properly a previous time 
                # and try to remove it again.
                self._erase_hash_directory(indexed_hash_path)
                break
            with open(unique_rep_filename, 'r') as f:
                rep = f.read()
                if rep == unique_rep: # found a match; it is already in storage
                    # remember this for next time
                    result = (self.context, rep_hash+str(index))
                    self._proveItObjects[proveItObject] = result
                    return result
            index += 1
        indexed_hash_path = hash_path + str(index)
        # store the unique representation in the appropriate file
        os.mkdir(indexed_hash_path)
        with open(os.path.join(indexed_hash_path, 'unique_rep.pv_it'), 'w') as f:
            f.write(unique_rep) 
        # write a reference count of zero (initially)
        with open(os.path.join(indexed_hash_path, 'ref_count.txt'), 'w') as f:
            f.write("0\n") 
        # increment reference counts of the referenced objects
        for objId in self._extractReferencedStorageIds(unique_rep):
            self._addReference(objId)
        # remember this for next time
        result = (self.context, rep_hash+str(index))
        self._proveItObjects[proveItObject] = result
        return result
    
    def expressionNotebook(self, expr, unofficialNameKindContext=None):
        '''
        Return the path of the expression notebook, creating it if it
        does not already exist.  If 'unofficialNameKindContext' is provided,
        it should be the (name, kind, context) for a special expression
        that is not-yet-official (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        import proveit
        from proveit import Expression, expressionDepth
        from .context import Context
        
        if not isinstance(expr, Expression):
            raise ValueError("'expr' should be an Expression object")

        context, hash_directory = self._retrieve(expr)
        if context != self.context:
            return context._storage.expressionNotebook(expr)
        
        # If the expression is a special expression (common expression, axiom,
        # or theorem) mark the name in 'name.txt'.
        # That way we will know whether or not the notebook needs to be
        # re-written (if we did not know it was a special expression before).
        try:
            expr_address = self.context.specialExprAddress(expr)
        except KeyError:
            expr_address = None
        needs_rewriting = False
        if expr_address is not None:
            special_expr_name_filename = os.path.join(self.pv_it_dir, hash_directory, 'name.txt')
            if not os.path.isfile(special_expr_name_filename):
                needs_rewriting = True
                with open(special_expr_name_filename, 'w') as nameFile:
                    nameFile.write(expr_address[-1])
        filename = os.path.join(self.pv_it_dir, hash_directory, 'expr.ipynb')
        if not needs_rewriting and os.path.isfile(filename):
            return filename # return the existing proof file
        elif os.path.isfile(filename):
            special_name = expr_address[-1].split('.')[0] # strip of ".expr"
            # Store the original version as orig_expr.ipynb.  It will be
            # resurrected if the expression is no longer "special" but still used.
            os.rename(filename, os.path.join(self.pv_it_dir, hash_directory, 'orig_expr.ipynb'))
            print "%s expression notebook is being updated"%special_name
        expr_classes = set()
        unnamed_subexpr_occurences = dict()
        named_subexpr_addresses = dict()
        # maps each class name or special expression name to a list of objects being represented; that
        # way we will know whether we can use the abbreviated name or full address.
        named_items = dict() 
        self._exprBuildingPrerequisites(expr, expr_classes, unnamed_subexpr_occurences, named_subexpr_addresses, named_items, isSubExpr=False)
        # find sub-expressions that are used multiple times, these ones will be assigned to a variable
        multiuse_subexprs = [sub_expr for sub_expr, count in unnamed_subexpr_occurences.iteritems() if count > 1]
        # sort the multi-use sub-expressions so that the shallower ones come first
        multiuse_subexprs = sorted(multiuse_subexprs, key = lambda expr : expressionDepth(expr))
        
        # map modules to lists of objects to import from the module
        from_imports = dict()
        # set of modules to import directly
        direct_imports = set()
        # map from expression classes or special expressions to their names (abbreviated if there is no
        # ambiguity, otherwise using the full address).
        item_names = dict() 
        
        # populate fromImports, directImports, and itemNames
        for expr_class in expr_classes:
            class_name = self.className(expr_class)
            module_name = self._moduleAbbreviatedName(expr_class.__module__, class_name)
            is_unique = (len(named_items[class_name]) == 1)
            if is_unique:
                from_imports.setdefault(module_name, []).append(class_name)
                item_names[expr_class] = class_name
            else:
                direct_imports.add(module_name)
                item_names[expr_class] = module_name+'.'+class_name
        for namedExpr, namedExprAddress in named_subexpr_addresses.iteritems():
            if isinstance(namedExprAddress[0], str):
                # Must be a special expression (axiom, theorem, or common expression)
                module_name = namedExprAddress[0]
                item_names[namedExpr] = itemName = namedExprAddress[-1]
                objName = itemName.split('.')[0] # split of '.expr' part if it is a Theorem or Axiom KnownTruth
                module_name = self._moduleAbbreviatedName(module_name, objName)
                is_unique = (len(named_items[itemName]) == 1)
                from_imports.setdefault(module_name, []).append(objName)
            else:
                # Expression must be an attribute of a class (e.g., '_operator_')
                item_names[namedExpr] = item_names[namedExprAddress[0]] + '.' + namedExprAddress[1]
        
        # see if we need to add anything to the sys.path
        needs_root_path = False # needs the root of this context added
        needs_local_path = False # needs the local path added
        # first, see if we even need to import a module with the same root as our context
        root_context = self.context.rootContext
        context_root_name = root_context.name
        for module_name in itertools.chain(direct_imports, from_imports.keys()):
            if module_name.split('.')[0] == context_root_name:
                # If we needed to add a path to sys.path for the directory above the root context,
                # we'll need to do that explicitly in our expression notebook.
                needs_root_path = root_context._storage.addedPath
                break
            else:
                module = importlib.import_module(module_name)
                if not os.path.isabs(module.__file__):
                    needs_local_path = True
        
        # generate the imports that we need (appending to sys.path if necessary).
        import_stmts = []
        if needs_root_path or needs_local_path:
            # add to the sys path
            import_stmts = ['import sys']
            rel_paths = set()
            if needs_local_path:
                # go up 2 levels, where the local directory is
                rel_paths.add(os.path.relpath('.', start=os.path.join(self.pv_it_dir, hash_directory)))
            if needs_root_path:
                # go up enough levels to the context root;
                # 2 levels to get out of the '__pv_it' folder and at least
                # 1 more to get above the root context.
                rel_paths.add(os.path.join(*(['..']*(self.context.name.count('.')+3))))
            for rel_path in rel_paths:
                import_stmts.append(json.dumps('sys.path.insert(1, "%s")'%rel_path).strip('"'))
        # direct import statements
        import_stmts += ['import %s'%module_name for module_name in sorted(direct_imports)]
        # from import statements
        import_stmts += ['from %s import '%module_name + ', '.join(sorted(from_imports[module_name])) for module_name in sorted(from_imports.keys())]
        # code to perform the required imports
        import_code = '\\n",\n\t"'.join(import_stmts)
        
        # generate the code for building the expression
        expr_code = ''
        idx = 0
        for sub_expr in multiuse_subexprs:
            if hasattr(sub_expr, 'context') and sub_expr.context is not None:
                continue # this expression is pulled from a context and does not need to be built
            idx += 1
            sub_expr_name = 'subExpr%d'%idx
            expr_code += sub_expr_name + ' = ' + json.dumps(self._exprBuildingCode(sub_expr, item_names, isSubExpr=True)).strip('"') + '\\n",\n\t"'
            item_names[sub_expr] = sub_expr_name
        expr_code += 'expr = ' + json.dumps(self._exprBuildingCode(expr, item_names, isSubExpr=False)).strip('"')
        
        # read the template and change the contexts as appropriate
        proveit_path = os.path.split(proveit.__file__)[0]
        if unofficialNameKindContext is not None:
            template_name = '_unofficial_special_expr_template_.ipynb'
            name, kind, context = unofficialNameKindContext
        elif expr_address is not None:
            template_name = '_special_expr_template_.ipynb'
            kind, name = self.context.specialExpr(expr)
        else:
            template_name = '_expr_template_.ipynb'
        with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
            nb = template.read()
            if template_name != '_special_expr_template_.ipynb':
                nb = nb.replace('#EXPR#', expr_code)
            nb = nb.replace('#IMPORTS#', import_code)
            nb = nb.replace('#CONTEXT#', context.name)
            nb = nb.replace('#TYPE#', str(expr.__class__).split('.')[-1])
            #nb = nb.replace('#TYPE_LINK#', typeLink.replace('\\', '\\\\'))
            if unofficialNameKindContext is not None or expr_address is not None:
                kind_str = kind[0].upper() + kind[1:]
                if kind == 'common': kind_str = 'Common Expression'
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = '/'.join(['..', '..', Context.specialExprKindToModuleName[kind] + '.ipynb'])
                nb = nb.replace('#SPECIAL_EXPR_LINK#', json.dumps(special_expr_link + '#' + name).strip('"'))
        # write the expression notebook
        with open(filename, 'w') as expr_file:
            expr_file.write(nb)
        
        # it this is a special expression also generate the dependencies notebook if it does not yet exist
        if template_name == '_special_expr_template_.ipynb':
            dependencies_filename = os.path.join(self.pv_it_dir, hash_directory, 'dependencies.ipynb')
            # Even if the dependencies file exists, write over it since the expression notebook
            # was rewritten.  This will guarantee the file is overwritten if it needs to be (the
            # name or kind of the special expression changes) and not overwritten if the expression
            # notebook was allowed to remain unchanged.
            with open(os.path.join(proveit_path, '..', '_dependencies_template_.ipynb'), 'r') as template:
                nb = template.read()
                nb = nb.replace('#IMPORTS#', import_code)
                nb = nb.replace('#CONTEXT#', context.name)
                nb = nb.replace('#TYPE#', str(expr.__class__).split('.')[-1])
                #nb = nb.replace('#TYPE_LINK#', typeLink.replace('\\', '\\\\'))
                nb = nb.replace('#KIND#', kind_str)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                nb = nb.replace('#SPECIAL_EXPR_LINK#', json.dumps(special_expr_link + '#' + name).strip('"'))  
                if kind_str == 'Theorem':
                    see_proof_str = '***see <a href=\\"../../_proofs_/%s.ipynb\\">proof</a>***'%name
                else: see_proof_str = ''
                nb = nb.replace('#SEE_PROOF#', see_proof_str)
            with open(dependencies_filename, 'w') as dependencies_file:
                dependencies_file.write(nb)
            
        return filename # return the new proof file
        
    def _exprBuildingPrerequisites(self, expr, exprClasses, unnamedSubExprOccurences, namedSubExprAddresses, namedItems, isSubExpr=True):
        '''
        Given an Expression object (expr), visit all sub-expressions and obtain the set of 
        represented Expression classes (exprClasses), the count for 'unnamed' sub-Expression
        occurances (unnamedSubExprOccurances as an Expression:int dictionary),
        the 'address' of all named sub-Expressions [namedSubExprAddresses as an
        Expression:expression-address dictionary], and the Expression(s)/class(es) corresponding
        to each named item (namedItems as a name:set dictionary).  The expression-address
        is in the form (module, name) for special-expressions or (Expression class, '_operator_')
        for a Literal operator.  When there are muliple items with the same name, full names 
        must be used instead of abbreviations.
        '''
        from proveit import Operation, Expression, ExpressionList, NamedExpressions, ExpressionTensor
        
        if expr in Operation.operationClassOfOperator:
            # the expression is an '_operator_' of an Operation class
            operationClass = Operation.operationClassOfOperator[expr]
            exprClasses.add(operationClass)
            namedItems.setdefault(self.className(operationClass), set()).add(operationClass)
            namedSubExprAddresses[operationClass._operator_] = (operationClass, '_operator_')
            return
            
        if expr in Expression.contexts:
            # expr may be a special expression from a context
            try:
                # if it is a special expression in a context, 
                # we want to be able to address it as such.
                exprAddress = Expression.contexts[expr].specialExprAddress(expr)
                namedSubExprAddresses[expr] = exprAddress
                namedItems.setdefault(exprAddress[-1], set()).add(expr)
                return
            except KeyError:
                pass
        
        # add to the unnamed sub-expression count
        unnamedSubExprOccurences[expr] = unnamedSubExprOccurences.get(expr, 0) + 1
        if unnamedSubExprOccurences[expr] > 1:
            return # already visited this -- no need to reprocess it
        
        if not isSubExpr or expr.__class__ not in (ExpressionList, NamedExpressions, ExpressionTensor): 
            # add expr's class to exprClass and named items (unless it is a basic Composite sub-Expression
            # in which case we'll use a python list or dictionary to represent the composite expression).
            exprClasses.add(expr.__class__)
            namedItems.setdefault(self.className(expr.__class__), set()).add(expr.__class__)
                                
        # recurse over the expression build arguments (e.g., the sub-Expressions
        for arg in expr.buildArguments():
            try:
                if isinstance(arg[0], str):
                    argname, arg = arg # splits into a name, argument pair
            except:
                pass
            if not isinstance(arg, Expression) and not isinstance(arg, str):
                raise TypeError("The arguments of %s.buildArguments() should be Expressions or strings" %str(expr.__class__))
            if isinstance(arg, Expression):
                subExpr = arg
                self._exprBuildingPrerequisites(subExpr, exprClasses, unnamedSubExprOccurences, namedSubExprAddresses, namedItems)
        
    def _moduleAbbreviatedName(self, moduleName, objName):
        '''
        Return the abbreviated module name for the given object based upon
        the convention that packages will import objects within that package
        that should be visible externally.  Specifically, this successively
        checks parent packages to see of the object is defined there with
        the same name.  For example, 
        proveit.logic.boolean.conjunction.and_op will be abbreviated
        to proveit.logic for the 'And' class.
        '''
        module = importlib.import_module(moduleName)
            
        if not os.path.isabs(module.__file__):
            # convert a relative path to a path starting from the context root
            abs_module_name = self.context.name + '.' + moduleName
            if abs_module_name not in sys.modules:
                return moduleName # just use the relative path
        split_module_name = moduleName.split('.')
        while len(split_module_name) > 1:
            cur_module = sys.modules['.'.join(split_module_name)]
            parent_module = sys.modules['.'.join(split_module_name[:-1])]
            if not hasattr(parent_module, objName): break
            if getattr(cur_module, objName) == getattr(parent_module, objName):
                split_module_name = split_module_name[:-1]
        return '.'.join(split_module_name)
    
    def className(self, exprClass):
        return str(exprClass).split('.')[-1]
    
    def _exprBuildingCode(self, expr, itemNames, isSubExpr=True):
        from proveit import Expression, Composite, ExpressionList, NamedExpressions, ExpressionTensor
                
        if expr is None: return 'None' # special 'None' case
        
        if expr in itemNames:
            # the expression is simply a named item
            return itemNames[expr]
        
        def argToString(arg):
            if isinstance(arg, str): 
                return arg # just a single string
            if isinstance(arg, Expression):
                # convert a sub-Expression to a string, 
                # either a variable name or code to construct the sub-expression:
                return self._exprBuildingCode(arg, itemNames)
            # see of we can split arg into a (name, value) pair
            try:
                name, val = arg
                if isinstance(name, str):
                    return name + ' = ' + argToString(val)
            except:
                pass
            # the final possibility is that we need a list of expressions (i.e., parameters of a Lambda expression)
            return '[' + ', '.join(argToString(argItem) for argItem in arg) + ']' 
        
        argStr = ', '.join(argToString(arg) for arg in expr.buildArguments())        
        
        if isinstance(expr, Composite):
            if isinstance(expr, ExpressionList):
                compositeStr = '[' + argStr + ']'
            else: # ExpressionTensor or NamedExpressions
                compositeStr = '{' + argStr.replace(' = ', ':') + '}'                    
            if isSubExpr and expr.__class__ in (ExpressionList, NamedExpressions, ExpressionTensor): 
                # It is a sub-Expression and a standard composite class.
                # Just pass it in as an implicit composite expression (a list or dictionary).
                # The constructor should be equipped to handle it appropriately.
                return compositeStr
            else:
                return itemNames[expr.__class__] + '(' + compositeStr + ')'
        else:
            return itemNames[expr.__class__] + '(' + argStr + ')'
    
    def proofNotebook(self, theorem_name, expr):
        '''
        Return the path of the proof notebook, creating it if it does not
        already exist.
        '''
        context, hash_directory = self._retrieve(expr)
        proofs_path = os.path.join(self.directory, '_proofs_')
        filename = os.path.join(proofs_path, '%s.ipynb'%theorem_name)
        if os.path.isfile(filename):
            # Check the theorem name and make sure the capitalization
            # is the same.  If not, revise it appropriately.
            existing_theorem_name = self._proofNotebookTheoremName(filename)
            if existing_theorem_name is None:
                # The format is not correct; stash this one and generate a new one.
                self._stashNotebook(filename)
            else:
                if existing_theorem_name != theorem_name:
                    # update with the new capitalization
                    with open(filename, 'r') as proof_notebook:
                        nb = proof_notebook.read()
                    nb = nb.replace(existing_theorem_name, theorem_name)
                    # remove the file before creating again to force the new
                    # capitolization (e.g., in Windows where capitolization 
                    # can be flexible)
                    os.remove(filename) 
                    with open(filename, 'w') as proof_notebook:
                        proof_notebook.write(nb)
                return filename
        if not os.path.isdir(proofs_path):
            # make the directory for the _proofs_
            os.makedirs(proofs_path)            
        nb = self._generateGenericProofNotebook(theorem_name)
        # write the proof file
        with open(filename, 'w') as proof_notebook:
            proof_notebook.write(nb)
        return filename # return the new proof file
    
    def _generateGenericProofNotebook(self, theorem_name):
        '''
        Given a theorem name and hash directory, generate the generic start
        of a proof notebook using the template.
        '''
        import proveit
        # read the template and change the contexts as appropriate
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_proof_template_.ipynb'), 'r') as template:
            nb = template.read()
            nb = nb.replace('#THEOREM_NAME#', theorem_name)
        return nb
    
    def _proofNotebookTheoremName(self, filename):
        '''
        Return the theorem name extracted from the proof notebook.
        '''
        with open(filename, 'r') as proof_notebook:
            nb = proof_notebook.read()
            # the theorem name should come after "_theorems_.ipynb#" in the notebook
            match =  re.search(r'_theorems_\.ipynb\#([_a-zA-Z]\w*)', nb)
            if match is None: return None
            return match.groups()[0]
            
    def stashExtraneousProofNotebooks(self, theorem_names):
        '''
        For any proof notebooks for theorem names not included in the given 
        theorem_names, stash them or remove them if they are generic notebooks.
        '''
        proofs_path = os.path.join(self.directory, '_proofs_')
        if not os.path.isdir(proofs_path):
            return # nothing to stash
        for filename in os.listdir(proofs_path):
            # see if this is a proof notebook that should be kept
            if filename[:-len('.ipynb')] in theorem_names:
                continue # this one is a keeper
                
            filename = os.path.join(proofs_path, filename)
            if os.path.isdir(filename): continue # skip directories
            
            if "~stashed~" in filename:
                continue # already a stashed notebook
            
            remove_file = False # may be set to True below if it is a generic notebook
            
            # next, let's see if this is a generic notebook by extracting
            # its info, building the generic version, and comparing.
            theorem_name = self._proofNotebookTheoremName(filename)
            if theorem_name is not None:
                generic_version = self._generateGenericProofNotebook(theorem_name)        
                with open(filename, 'r') as notebook:
                    if generic_version == notebook.read():
                        remove_file = True # just remove it, it is generic
            
            if remove_file:
                os.remove(filename)
            else:
                self._stashNotebook(filename)
    
    def _stashNotebook(self, filename):
        '''
        Stash a notebook to a "~stashed~#" file using a '#' (number)
        that has not been used yet.
        '''
        num = 1
        filename_base = filename[:-len('.ipynb')]
        while os.path.isfile(filename_base + "~stashed~%d.ipynb"%num):
            num += 1
        new_filename = filename_base + "~stashed~%d.ipynb"%num
        print "Stashing %s to %s in case it is needed."%(os.path.relpath(filename), os.path.relpath(new_filename))
        os.rename(filename, new_filename)
        
    def makeExpression(self, exprId):
        '''
        Return the Expression object that is represented in storage by
        the given expression id.
        '''
        import importlib
        from proveit import Expression
        expr_class_map = dict() # map expression class strings to Expression class objects
        def importFn(exprClassStr):
            split_expr_class = exprClassStr.split('.')
            module = importlib.import_module('.'.join(split_expr_class[:-1]))
            expr_class_map[exprClassStr] = getattr(module, split_expr_class[-1])
        def exprBuilderFn(exprClassStr, exprInfo, subExpressions, context):
            expr = expr_class_map[exprClassStr].make(exprInfo, subExpressions)
            if context is not None and expr not in Expression.contexts:
                Expression.contexts[expr] = context
            return expr
        return self._makeExpression(exprId, importFn, exprBuilderFn)
        
    def _makeExpression(self, exprId, importFn, exprBuilderFn):
        '''
        Helper method for makeExpression
        '''
        from proveit import Expression
        from _dependency_graph import orderedDependencyNodes
        from .context import Context
        expr_class_strs = dict() # map expr-ids to lists of Expression class string representations
        expr_class_rel_strs = dict() # relative paths of Expression classes that are local
        core_info_map = dict() # map expr-ids to core information
        sub_expr_ids_map = dict() # map expr-ids to list of sub-expression ids
        context_map = dict() # map expr-ids to a Context 
        master_expr_id = exprId
        local_context_name = Context().name
                
        def getSubExprIds(exprId):
            context_name, hash_directory = self._split(exprId)
            if context_name != '': context_map[exprId] = Context.getContext(context_name)
            hash_path = self._storagePath(exprId)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # extract the unique representation from the pv_it file
                unique_rep = f.read()
                # extract the Expression class from the unique representation 
                expr_class_str = Expression._extractExprClass(unique_rep)
                if expr_class_str.find(local_context_name) == 0:
                    # import locally if necessary
                    expr_class_rel_strs[exprId] = expr_class_str[len(local_context_name)+1:]                
                expr_class_strs[exprId] = expr_class_str
                # extract the Expression "core information" from the unique representation
                core_info_map[exprId] = Expression._extractCoreInfo(unique_rep)
                # get the sub-expressions all sub-expressions
                sub_expr_ids_map[exprId] = self._extractReferencedStorageIds(unique_rep, context_name)
                return sub_expr_ids_map[exprId]
        
        expr_ids = orderedDependencyNodes(exprId, getSubExprIds)
        for expr_id in reversed(expr_ids):
            if expr_id in expr_class_rel_strs:
                # there exists a relative path
                try:
                    # First try the absolute path; that is preferred for
                    # consistency sake (we want different imports of something
                    # to be regarded as the same)
                    importFn(expr_class_strs[expr_id])
                except:
                    # If importing the absolute path fails, maybe the relative
                    # path will work.  This is needed to resolve, for example,
                    # the issue that the proveit.logic package imports from
                    # proveit.logic.boolean._common_ but we need to be able
                    # to execute proveit.logic.boolean._common_.ipynb in
                    # the first place which requires imports within 
                    # proveit.logic.boolean.  The solution is to use relative
                    # imports when executing proveit.logic.boolean._common_.ipynb
                    # the first time but afterwards use absolute paths. 
                    importFn(expr_class_rel_strs[expr_id])
                    # use the relative path
                    expr_class_strs[expr_id] = expr_class_rel_strs[expr_id]
            else:
                # there does not exist a relative path; 
                # the absolute path is the only option.
                importFn(expr_class_strs[expr_id])
        built_expr_map = dict() # map expr-ids to "built" expressions (whatever exprBuilderFn returns)
        for expr_id in reversed(expr_ids):
            sub_expressions =  [built_expr_map[sub_expr_id] for sub_expr_id in sub_expr_ids_map[expr_id]]
            context = context_map[expr_id] if expr_id in context_map else None
            built_expr_map[expr_id] = exprBuilderFn(expr_class_strs[expr_id], core_info_map[expr_id], sub_expressions, context)
        return built_expr_map[master_expr_id]        
    
    def recordReferencedCommons(self, contextNames):
        '''
        Record the context names of any reference common expressions in storage
        while creating the common expressions for this context
        (for the purposes of checking for illegal mutual dependencies).
        '''
        if contextNames == self.referencedCommons():
            return # unchanged
        referenced_commons_filename = os.path.join(self.pv_it_dir, '_referenced_commons_.txt')
        with open(referenced_commons_filename, 'w') as f:
            for context_name in contextNames:
                f.write(context_name + '\n')

    def referencedCommons(self):
        '''
        Return the stored set of context names of common expressions
        referenced by the common expression notebook of this context.
        '''
        referenced_commons_filename = os.path.join(self.pv_it_dir, '_referenced_commons_.txt')
        if os.path.isfile(referenced_commons_filename):
            with open(referenced_commons_filename, 'r') as f:
                return set(f.readlines())
        return set() # empty set by default
        
    def hasMutualReferencedCommons(self, contextNames):
        '''
        Check for illecial mutual dependencies of common expression notebooks.
        '''
        from .context import Context
        for context_name in contextNames:
            context = Context.getContext(context_name)
            other_referenced_commons = context.referencedCommons()
            if context.name in other_referenced_commons:
                return True
        return False
    
    def clean(self):
        '''
        Clean the __pv_it directory by erasing anything with a reference
        count of zero.
        '''
        for sub_dir in os.listdir(self.pv_it_dir):
            if sub_dir == '_axioms_' or sub_dir == '_theorems_':
                continue
            sub_path = os.path.join(self.pv_it_dir, sub_dir)
            if os.path.isdir(sub_path):
                # assume this is a hash directory for a prove-it object if it isn't _axioms_ or _theorems_
                hash_directory = sub_dir 
                if self._getRefCount(hash_directory) == 0:
                    self._removeReference(hash_directory)
    
    """    
    # This is not good to do if there are external references
           
    def erase(self):
        '''
        Erase the entire __pv_it directory.
        '''
        self._proveItObjects.clear()
        pv_it_dir = os.path.join(self.directory, '__pv_it')
        if not os.path.isdir(pv_it_dir): return
        for hash_dir in os.listdir(pv_it_dir):
            hash_path = os.path.join(pv_it_dir, hash_dir)
            for pv_it_file in os.listdir(hash_path):
                os.remove(os.path.join(hash_path, pv_it_file))
            os.rmdir(hash_path)
        os.rmdir(pv_it_dir)
    """
    
    
class StoredSpecialStmt:
    def __init__(self, context, name, kind):
        '''
        Base class of StoredAxiom and StoredTheorem initialization.
        '''
        self.context = context
        self.name = name
        self.kind = kind
        if kind == 'axiom':
            self.path = os.path.join(self.context._storage.pv_it_dir, '_axioms_', self.name)
        elif kind == 'theorem':
            self.path = os.path.join(self.context._storage.pv_it_dir, '_theorems_', self.name) 
        else:
            raise ValueError("kind must be 'axiom' or 'theorem'")

    def __str__(self):
        return self.context.name + '.' + self.name
    
    def remove(self, keepPath=False):
        '''
        Remove the axiom or theorem and all references to it and any proofs
        that depend upon it.
        '''
        from .context import Context
        # remove the reference to the expression to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'expr.pv_it'), 'r') as f:
            expr_id = f.read()
            storage = self.context._storage
            storage._removeReference(expr_id)
            hash_path = storage._storagePath(expr_id)
            if not os.path.isdir(hash_path):
                # remove name.txt that marks the stored expression as a special statement
                special_name_file = os.path.join(hash_path, 'name.txt')
                if os.path.isfile(special_name_file):
                    os.remove(special_name_file)                    
                # remove the "special" expression notebook 
                expr_notebook = os.path.join(hash_path, 'expr.ipynb')
                if os.path.isfile(expr_notebook):
                    os.remove(expr_notebook)
                # resurrect the original expression notebook
                orig_expr_notebook = os.path.join(hash_path, 'orig_expr.ipynb')
                if os.path.isfile(orig_expr_notebook):
                    os.rename(orig_expr_notebook, expr_notebook)
        # remove invalidated proofs that use this axiom/theorem
        dependentTheorems = self.readDependentTheorems()
        for dependent in dependentTheorems:
            Context.getStoredTheorem(dependent).removeProof()
        if not keepPath:
            # remove the entire directory for the axiom/theorem
            shutil.rmtree(self.path)
        
    def readDependentTheorems(self):
        '''
        Return the collection of theorems (as strings) that use this theorem/axiom directly.
        '''
        theorems = []
        usedByFilename = os.path.join(self.path, 'usedBy.txt')
        if not os.path.isfile(usedByFilename):
            return theorems # return the empty list
        with open(usedByFilename, 'r') as usedByFile:
            for line in usedByFile:
                theorems.append(line.strip())
        return theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the given 
        theorem or axiom directly or indirectly.
        '''
        from .context import Context
        toProcess = set(self.readDependentTheorems())
        processed = set()
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            processed.add(nextTheorem)
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            dependents = set(storedTheorem.readDependentTheorems())
            # add anything new to be processed
            toProcess.update(dependents.difference(processed))
        return processed

    def _removeEntryFromFile(self, filename, entryToRemove):
        '''
        Removes a specific entry from a file.
        '''
        # obtain all lines that are NOT the specified link to be removed
        remaining = []
        with open(os.path.join(self.path, filename), 'r') as f:
            for line in f:
                line = line.strip()
                if line != entryToRemove:
                    remaining.append(line)
        # re-write usedBy.txt with all of the remaining lines
        with open(os.path.join(self.path, filename), 'w') as f:
            for line in remaining:
                f.write(line + '\n')
    
    def _countEntries(self, filename):
        '''
        Returns the number of entries in a particular file.
        '''
        count = 0
        with open(os.path.join(self.path, filename), 'r') as f:
            for line in f:
                count += 1
        return count

    def _removeUsedByEntry(self, usedByTheorem):
        '''
        Remove a particular usedByTheorem entry in the usedBy.txt for this
        stored axiom or theorem.
        '''
        self._removeEntryFromFile('usedBy.txt', str(usedByTheorem))
    
class StoredAxiom(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredAxioms object for managing an axioms's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'axiom')
    
    def getDefLink(self):
        '''
        Return the link to the axiom definition in the _axioms_ notebook.
        '''
        axioms_notebook_link = os.path.relpath(os.path.join(self.context.getPath(), '_axioms_.ipynb'))
        return axioms_notebook_link + '#' + self.name

class StoredTheorem(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredTheorem object for managing a theorem's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'theorem')

    def getProofLink(self):
        '''
        Return the link to the theorem's proof notebook.
        '''
        return os.path.relpath(os.path.join(self.context.getPath(), '_proofs_', self.name + '.ipynb'))

    def remove(self, keepPath=False):
        if self.hasProof():
            # must remove the proof first
            self.removeProof()
        StoredSpecialStmt.remove(self, keepPath)

    def readDependencies(self):
        '''
        Returns the used set of axioms and theorems (as a tuple of sets
        of strings) that are used by the given theorem as recorded in the database.
        '''
        usedAxioms = set()
        usedTheorems = set()
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            try:
                with open(os.path.join(self.path, usedStmtsFilename), 'r') as usedStmtsFile:
                    for line in usedStmtsFile:
                        line = line.strip()
                        usedStmts.add(line)
            except IOError:
                pass # no contribution if the file doesn't exist
        return (usedAxioms, usedTheorems)

    def recordPresumingInfo(self, presuming):
        '''
        Record information about what the proof of the theorem
        presumes -- what other theorems/contexts the proof
        is expected to depend upon.
        '''
        presuming_str = (presuming if isinstance(presuming, str) else ', '.join(presuming))
        presuming_file = os.path.join(self.path, 'presuming.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                if presuming_str == f.read().strip():
                    return # unchanged; don't need to record anything
        with open(presuming_file, 'w') as f:
            f.write(presuming_str + '\n')
    
    def presumes(self, other_theorem_str):
        '''
        Return True iff the things that this "stored" theorem 
        presumes (or is intended to presume) include the other
        theorem with the given string representation.
        '''
        presuming_file = os.path.join(self.path, 'presuming.txt')
        if os.path.isfile(presuming_file):
            with open(presuming_file, 'r') as f:
                presuming_str = f.read().strip()
                presuming = presuming_str.split(',')
                for presume in presuming:
                    presume = presume.strip()
                    if other_theorem_str[:len(presume)] == presume:
                        # 'presume' includes other_theorem_str (either the theorem
                        # itself or a context containing it directly or indirectly).
                        return True
        # The default is False if no presuming info is stored
        # for this theorem.
        return False       
    
    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  Updates
        dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
        and proven dependency indicators (various provenTheorems.txt files 
        for theorems that depend upon this one) appropriately.
        '''
        from proveit._core_ import Proof
        from .context import Context
              
        # add a reference to the new proof
        proofId = self.context._storage._proveItStorageId(proof)
        self.context._storage._addReference(proofId)
        
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()
                    
        # record the proof id
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
        
        usedAxioms = [str(usedAxiom) for usedAxiom in proof.usedAxioms()]
        usedTheorems = [str(usedTheorem) for usedTheorem in proof.usedTheorems()]
        
        # Remove usedBy links that are obsolete because the proof has changed
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for prevUsedAxiom in prevUsedAxioms:
            if prevUsedAxiom not in usedAxioms:
                Context.getStoredAxiom(prevUsedAxiom)._removeUsedByEntry(str(self))
        for prevUsedTheorem in prevUsedTheorems:
            if prevUsedTheorem not in usedTheorems:
                Context.getStoredTheorem(prevUsedTheorem)._removeUsedByEntry(str(self))

        storedUsedAxioms = [Context.getStoredAxiom(usedAxiom) for usedAxiom in usedAxioms]
        storedUsedTheorems = [Context.getStoredTheorem(usedTheorem) for usedTheorem in usedTheorems]
        
        # record axioms/theorems that this theorem directly uses
        for storedUsedStmts, usedStmtsFilename in ((storedUsedAxioms, 'usedAxioms.txt'), (storedUsedTheorems, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for storedUsedStmt in sorted(storedUsedStmts):
                    self.context._includeMutualReferences(storedUsedStmt.context)
                    usedStmtsFile.write(str(storedUsedStmt) + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheorems:
                if Context.getStoredTheorem(usedTheorem).isComplete():
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the newly proven theorem
        for storedUsedStmts, prevUsedStmts in ((storedUsedAxioms, prevUsedAxioms), (storedUsedTheorems, prevUsedTheorems)):
            for storedUsedStmt in storedUsedStmts:
                if str(storedUsedStmt) not in prevUsedStmts: # otherwise the link should already exist
                    with open(os.path.join(storedUsedStmt.path, 'usedBy.txt'), 'a') as usedByFile:
                        usedByFile.write(str(self) + '\n')
        
        print str(self) + ' has a proof'
        # if this proof is complete (all of the theorems that it uses are complete) then
        # propagate this information to the theorems that depend upon this one.
        self._propagateCompletion()
    
    def hasProof(self):
        '''
        Returns True iff a proof was recorded for this theorem.
        '''
        return os.path.isfile(os.path.join(self.path, 'proof.pv_it'))
    
    def numUsedTheorems(self):
        try:
            return self._countEntries('usedTheorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason

    def numCompleteUsedTheorems(self):
        try:
            return self._countEntries('completeUsedTheorems.txt')
        except IOError:
            return 0 # if the file is not there for some reason
    
    def isComplete(self):
        '''
        Return True iff this theorem has a proof and all theorems that
        that it uses are also complete.
        '''
        if not self.hasProof():
            return False # Cannot be complete if there is no proof for this theorem
        # If all used theorems have are complete (and this theorem has a proof),
        # then this theorem is complete.
        return self.numUsedTheorems() == self.numCompleteUsedTheorems()
    
    def _propagateCompletion(self):
        '''
        If this theorem is complete, then let its dependents know.  If this
        update causes a dependent to become complete, propagate the news onward.
        '''
        from .context import Context
        if self.isComplete():
            print str(self) + ' has been completely proven'
            # This theorem has been completely proven.  Let the dependents know.
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                storedDependent = Context.getStoredTheorem(dependent)
                with open(os.path.join(storedDependent.path, 'completeUsedTheorems.txt'), 'a') as f:
                    f.write(str(self) + '\n')
                # propagate this recursively in case self's theorem was the final
                # theorem to complete the dependent
                storedDependent._propagateCompletion()
                        
    def removeProof(self):
        '''
        Erase the proof of this theorem from the database and all obsolete
        links/references.
        '''     
        from .context import Context 
        wasComplete = self.isComplete() # was it complete before the proof was removed?
        # remove the reference to the proof to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'proof.pv_it'), 'r') as f:
            proof_id = f.read()
            self.context._storage._removeReference(proof_id)
        # Remove obsolete usedBy links that refer to this theorem by its old proof
        prevUsedAxioms, prevUsedTheorems = self.readDependencies()
        for usedAxiom in prevUsedAxioms:
            Context.getStoredAxiom(usedAxiom)._removeUsedByEntry(str(self))
        for usedTheorem in prevUsedTheorems:
            Context.getStoredTheorem(usedTheorem)._removeUsedByEntry(str(self))
        # If it was previously complete before, we need to inform dependents that
        # it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))
        # remove 'proof.pv_it', 'usedAxioms.txt', 'usedTheorems.txt', and 'completeUsedTheorems.txt' for the theorem
        def removeIfExists(path):
            if os.path.isfile(path): os.remove(path)
        removeIfExists(os.path.join(self.path, 'proof.pv_it'))
        removeIfExists(os.path.join(self.path, 'usedAxioms.txt'))
        removeIfExists(os.path.join(self.path, 'usedTheorems.txt'))
        removeIfExists(os.path.join(self.path, 'completeUsedTheorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        usedAxioms, usedTheorems = self.readDependencies()
        requiredAxioms = usedAxioms # just a start
        requiredTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                requiredTheorems.add(nextTheorem)
                processed.add(nextTheorem)
                continue
            usedAxioms, usedTheorems = storedTheorem.readDependencies()
            requiredAxioms.update(usedAxioms)
            for usedTheorem in usedTheorems:
                if usedTheorem not in processed:
                    toProcess.add(usedTheorem)
            processed.add(nextTheorem)
        return (requiredAxioms, requiredTheorems)
    
    def allUsedTheorems(self):
        '''
        Returns the set of theorems used to prove the given theorem, directly
        or indirectly.
        '''
        from .context import Context
        if not self.hasProof():
            raise Exception('The theorem must be proven in order to obtain its requirements')
        _, usedTheorems = self.readDependencies()
        allUsedTheorems = set()
        processed = set()
        toProcess = usedTheorems
        while len(toProcess) > 0:
            nextTheorem = toProcess.pop()
            allUsedTheorems.add(nextTheorem)
            storedTheorem = Context.getStoredTheorem(nextTheorem)
            if not storedTheorem.hasProof():
                processed.add(nextTheorem)
                continue
            _, usedTheorems = storedTheorem.readDependencies()
            for usedTheorem in usedTheorems:
                if usedTheorem not in processed:
                    toProcess.add(usedTheorem)
            processed.add(nextTheorem)
        return allUsedTheorems 

    def _undoDependentCompletion(self, usedTheorem):
        '''
        Due to the proof being removed, a dependent theorem is no longer complete.
        This new status must be updated and propagated.
        '''
        from .context import Context
        wasComplete = self.isComplete() # was it complete before?
        # remove the entry from completeUsedTheorems.txt
        self._removeEntryFromFile('completeUsedTheorems.txt', str(usedTheorem))
        if self.isComplete():
            raise Exception('Corrupt _certified_ database')
        # If this theorem was previously complete before, we need to inform 
        # dependents that it is not longer complete.
        if wasComplete:
            dependentTheorems = self.readDependentTheorems()
            for dependent in dependentTheorems:
                Context.getStoredTheorem(dependent)._undoDependentCompletion(str(self))



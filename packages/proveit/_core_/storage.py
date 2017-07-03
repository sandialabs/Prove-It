import hashlib, os
import shutil
import sys
import importlib
import itertools
import json

class Storage:
    '''
    Manages the __pv_it directory of a Context, the distributed database
    of expressions, axioms, theorems, and proofs.
    '''
    
    def __init__(self, context, directory):
        from context import Context, ContextException
        if not isinstance(context, Context):
            raise ContextException("'context' should be a Context object")
        self.context = context
        self.directory = directory
        self.pv_it_dir = os.path.join(self.directory, '__pv_it')
        if not os.path.isdir(self.pv_it_dir):
            # make the directory for the storage
            os.makedirs(self.pv_it_dir)
        
        if self.context.isRoot():
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
        
        # For retrieved pv_it files that represent Prove-It object (Expressions, KnownTruths, and Proofs),
        # this maps the object to the pv_it file so we
        # can recall this without searching the hard drive again.
        self._proveItObjects = dict()
        
    def _updatePath(self):
        '''
        The path has changed.  Update paths.txt locally, and update the path
        reference from other Context's.
        '''
        from context import Context
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
        if hasattr(expr, 'context') and expr.context != self.context:
            return expr.context._stored_png(expr, latex, configLatexToolFn)
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
    
    def _storagePath(self, proveItStorageId):
        '''
        Return the storage directory path for the Prove-It object with the given
        storage id.
        '''
        from context import Context
        if '.' in proveItStorageId:
            # in a different context
            splitId = proveItStorageId.split('.')
            context_name, hash_directory = '.'.join(splitId[:-1]), splitId[-1]
            pv_it_dir = Context.getContext(context_name)._storage.pv_it_dir
            return os.path.join(pv_it_dir, hash_directory)
        return os.path.join(self.context._storage.pv_it_dir, proveItStorageId)
    
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
    
    def _extractReferencedStorageIds(self, unique_rep):
        '''
        Given a unique representation string, returns the list of Prove-It
        storage ids of objects that are referenced.
        '''
        from proveit import Expression, KnownTruth, Proof
        if unique_rep[:6] == 'Proof:':
            return Proof._extractReferencedObjIds(unique_rep[6:])
        elif unique_rep[:11] == 'KnownTruth:':
            return KnownTruth._extractReferencedObjIds(unique_rep[11:])
        else:
            # Assumed to be an expression then
            return Expression._extractReferencedObjIds(unique_rep)

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
        hash_path = self._storagePath(proveItStorageId)
        with open(os.path.join(hash_path, 'ref_count.txt'), 'r') as f:
            ref_count = int(f.read().strip()) - 1
        if ref_count <= 0:
            # Reference count down to zero (or less).  Remove references to
            # referenced objects and then delete this prove-it object from
            # storage and everything associated with it.
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                rep = f.read()
            for objId in self._extractReferencedStorageIds(rep):
                self._removeReference(objId)
            # remove the entire directory storing this prove-it object
            for filename in os.listdir(hash_path):
                path = os.path.join(hash_path, filename)
                if os.path.isdir(path):
                    for sub_filename in os.listdir(path):
                        os.remove(os.path.join(path, sub_filename))
                    os.rmdir(path)
                else:
                    os.remove(path)
            os.rmdir(hash_path)
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
    
    def _retrieve(self, proveItObject):
        '''
        Find the directory for the stored Expression, KnownTruth, or Proof.
        Create it if it did not previously exist.  Return the (context, hash_directory)
        pair, where the hash_directory is the directory name (within the context's
        __pv_it directory) based upon a hash of the unique representation.
        '''
        if proveItObject in self._proveItObjects:
            return self._proveItObjects[proveItObject]
        if hasattr(proveItObject, 'context') and proveItObject.context != self.context:
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
            with open(os.path.join(indexed_hash_path, 'unique_rep.pv_it'), 'r') as f:
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
        does not already exist.
        '''
        import proveit
        from proveit import Expression, expressionDepth
        from context import Context

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
            exprAddress = self.context.specialExprAddress(expr)
        except KeyError:
            exprAddress = None
        needsRewriting = False
        if exprAddress is not None:
            special_expr_name_filename = os.path.join(self.pv_it_dir, hash_directory, 'name.txt')
            if not os.path.isfile(special_expr_name_filename):
                needsRewriting = True
                with open(special_expr_name_filename, 'w') as nameFile:
                    nameFile.write(exprAddress[-1])
        filename = os.path.join(self.pv_it_dir, hash_directory, 'expr.ipynb')
        if not needsRewriting and os.path.isfile(filename):
            return filename # return the existing proof file
        
        exprClasses = set()
        unnamedSubExprOccurences = dict()
        namedSubExprAddresses = dict()
        # maps each class name or special expression name to a list of objects being represented; that
        # way we will know whether we can use the abbreviated name or full address.
        namedItems = dict() 
        self._exprBuildingPrerequisites(expr, exprClasses, unnamedSubExprOccurences, namedSubExprAddresses, namedItems)
        # find sub-expressions that are used multiple times, these ones will be assigned to a variable
        multiUseSubExprs = [subExpr for subExpr, count in unnamedSubExprOccurences.iteritems() if count > 1]
        # sort the multi-use sub-expressions so that the shallower ones come first
        multiUseSubExprs = sorted(multiUseSubExprs, key = lambda expr : expressionDepth(expr))
        
        # map modules to lists of objects to import from the module
        fromImports = dict()
        # set of modules to import directly
        directImports = set()
        # map from expression classes or special expressions to their names (abbreviated if there is no
        # ambiguity, otherwise using the full address).
        itemNames = dict() 

        for exprClass in exprClasses:
            className = self.className(exprClass)
            moduleName = self._moduleAbbreviatedName(exprClass.__module__, className)
            isUnique = (len(namedItems[className]) == 1)
            if isUnique:
                fromImports.setdefault(moduleName, []).append(className)
                itemNames[exprClass] = className
            else:
                directImports.add(moduleName)
                itemNames[exprClass] = moduleName+'.'+className
        for expr, exprAddress in namedSubExprAddresses.iteritems():
            moduleName = exprAddress[0]
            itemNames[expr] = objName = exprAddress[-1]
            isUnique = (len(namedItems[objName]) == 1)
            fromImports.setdefault(moduleName, []).append(objName)
        
        # see if we need to add anything to sys.path in order to import the module of this context
        needs_sys_path_update = False
        # first, see if we even need to import a module with the same root as our context
        context_root_name = self.context.name.split('.')[0]
        for moduleName in itertools.chain(directImports, fromImports.keys()):
            if moduleName.split('.')[0] == context_root_name:
                needs_sys_path_update = True
                break
        # if so, check to see if we can import the context without adding anything to sys.path
        if needs_sys_path_update:
            try:
                context_import_file = importlib.import_module(self.context.name).__file__
                context_import_path = os.path.join(context_import_file, '..')
                if os.path.relpath(context_import_path, self.directory) == '.':
                    # Assuming nothing was added to sys.path before calling this method,
                    # the expression notebook should be able to import the context's
                    # module without adding anything to sys.path 
                    needs_sys_path_update = False
            except:
                pass
        
        # generate the imports that we need (appending to sys.path if necessary).
        importStmts = []
        if needs_sys_path_update:
            # add to the sys path something that goes up enough directory levels
            # to where the root context starts, relative to the expression directory
            # within the __pv_it directory
            rel_context_path = os.path.join(['..']*(self.context.name.count('.')+2))
            importStmts = ['import sys', 'sys.path.append("%s")'%rel_context_path]
        # direct import statements
        importStmts += ['import %s'%moduleName for moduleName in sorted(directImports)]
        # from import statements
        importStmts += ['from %s import '%moduleName + ', '.join(sorted(fromImports[moduleName])) for moduleName in sorted(fromImports.keys())]
        # code to perform the required imports
        importCode = '\\n",\n\t"'.join(importStmts)
        
        # generate the code for building the expression
        exprCode = ''
        idx = 0
        for subExpr in multiUseSubExprs:
            if hasattr(subExpr, 'context') and subExpr.context is not None:
                continue # this expression is pulled from a context and does not need to be built
            idx += 1
            subExprName = 'subExpr%d'%idx
            exprCode += subExprName + ' = ' + json.dumps(self._exprBuildingCode(subExpr, itemNames, isSubExpr=False)).strip('"') + '\\n",\n\t"'
            itemNames[subExpr] = subExprName
        exprCode += 'expr = ' + json.dumps(self._exprBuildingCode(expr, itemNames, isSubExpr=False)).strip('"')
        
        # read the template and change the contexts as appropriate
        proveit_path = os.path.split(proveit.__file__)[0]
        if unofficialNameKindContext is not None:
            template_name = '_unofficial_special_expr_template_.ipynb'
            name, kind, context = unofficialNameKindContext
        elif exprAddress is not None:
            template_name = '_special_expr_template_.ipynb'
            kind, name = self.context.specialExpr(expr)
        else:
            template_name = '_expr_template_.ipynb'
        with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
            nb = template.read()
            nb = nb.replace('#EXPR#', exprCode)
            nb = nb.replace('#IMPORTS#', importCode)
            nb = nb.replace('#CONTEXT#', context.name)
            context_link = os.path.join('..', '..', '_context_.ipynb')
            nb = nb.replace('#CONTEXT_LINK#', context_link.replace('\\', '\\\\'))
            nb = nb.replace('#TYPE#', str(expr.__class__).split('.')[-1])
            #nb = nb.replace('#TYPE_LINK#', typeLink.replace('\\', '\\\\'))
            if unofficialNameKindContext is not None or exprAddress is not None:
                kindStr = kind[0].upper() + kind[1:]
                if kind == 'common': kindStr = 'Common Expression'
                nb = nb.replace('#KIND#', kindStr)
                nb = nb.replace('#SPECIAL_EXPR_NAME#', name)
                special_expr_link = os.path.join('..', '..', Context.specialExprKindToModuleName[kind] + '.ipynb')
                nb = nb.replace('#SPECIAL_EXPR_LINK#', json.dumps(special_expr_link + '#' + name).strip('"'))
        # write the proof file
        with open(filename, 'w') as exprFile:
            exprFile.write(nb)
        return filename # return the new proof file
        
    def _exprBuildingPrerequisites(self, expr, exprClasses, unnamedSubExprOccurences, namedSubExprAddresses, namedItems):
        if hasattr(expr, 'context') and expr.context is not None:
            # expr may be a special expression from a context
            try:
                # if it is a special expression in a context, 
                # we want to be able to address it as such.
                exprAddress = expr.context.specialExprAddress(expr)
                namedSubExprAddresses[expr] = exprAddress
                namedItems.setdefault(exprAddress[-1], set()).add(expr)
                return
            except KeyError:
                pass
        # recurse over the sub-expressions
        for subExpr in expr.subExprIter():
            self._exprBuildingPrerequisites(subExpr, exprClasses, unnamedSubExprOccurences, namedSubExprAddresses, namedItems)
        unnamedSubExprOccurences[expr] = unnamedSubExprOccurences.get(expr, 0) + 1
        exprClasses.add(expr.__class__)
        namedItems.setdefault(self.className(expr.__class__), set()).add(expr.__class__)
        
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
        assert hasattr(sys.modules[moduleName], objName)
        splitModuleName = moduleName.split('.')
        while len(splitModuleName) > 1:
            curModule = sys.modules['.'.join(splitModuleName)]
            parentModule = sys.modules['.'.join(splitModuleName[:-1])]
            if not hasattr(parentModule, objName): break
            if getattr(curModule, objName) == getattr(parentModule, objName):
                splitModuleName = splitModuleName[:-1]
        return '.'.join(splitModuleName)
    
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
                compositeStr = '{' + arg.replace(' = ', ':') + '}'                    
            if isSubExpr and expr.__class__ in (ExpressionList, NamedExpressions, ExpressionTensor): 
                # It is a sub-Expression and a standard composite class.
                # Just pass it in as an implicit composite expression (a list or dictionary).
                # The constructor should be equipped to handle it appropriately.
                return compositeStr
            else:
                return itemNames[expr.__class__] + '(' + compositeStr + ')'
        else:
            return itemNames[expr.__class__] + '(' + argStr + ')'
    
    def proofNotebook(self, theorem_name):
        '''
        Return the path of the proof notebook, creating it if it does not
        already exist.
        '''
        import proveit
        import json
        proofs_path = os.path.join(self.directory, '_proofs_')
        filename = os.path.join(proofs_path, '%s.ipynb'%theorem_name)
        if os.path.isfile(filename):
            return filename # return the existing proof file
        if not os.path.isdir(proofs_path):
            # make the directory for the _proofs_
            os.makedirs(proofs_path)            
        # read the template and change the contexts as appropriate
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_proof_template_.ipynb'), 'r') as template:
            nb = template.read()
            nb = nb.replace('#THEOREM_NAME#', theorem_name)
            theoremPath = os.path.join('..', '_theorems_.ipynb', '#%s'%theorem_name)
            nb = nb.replace('#THEOREM_PATH#', json.dumps(theoremPath))
        # write the proof file
        with open(filename, 'w') as proofFile:
            proofFile.write(nb)
        return filename # return the new proof file
        
    def makeExpression(self, exprId):
        '''
        Return the Expression object that is represented in storage by
        the given expression id.
        '''
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
        '''
        Helper method for makeExpression
        '''
        from proveit import Expression
        from _dependency_graph import orderedDependencyNodes
        exprClassStrs = dict() # map expr-ids to Expression class string representations
        coreInfoMap = dict() # map expr-ids to core information
        subExprIdsMap = dict() # map expr-ids to list of sub-expression ids 
        masterExprId = exprId
        def getSubExprIds(exprId):
            hash_path = self._storagePath(exprId)
            with open(os.path.join(hash_path, 'unique_rep.pv_it'), 'r') as f:
                # extract the unique representation from the pv_it file
                unique_rep = f.read()
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
        from context import Context
        # remove the reference to the expression to do reference counted
        # "garbage" collection in the packages database storage.
        with open(os.path.join(self.path, 'expr.pv_it'), 'r') as f:
            expr_id = f.read()
            self.context._storage._removeReference(expr_id)
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
        with open(os.path.join(self.path, 'usedBy.txt'), 'r') as usedByFile:
            for line in usedByFile:
                theorems.append(line.strip())
        return theorems
    
    def allDependents(self):
        '''
        Returns the set of theorems that are known to depend upon the given 
        theorem or axiom directly or indirectly.
        '''
        from context import Context
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

class StoredTheorem(StoredSpecialStmt):
    def __init__(self, context, name):
        '''
        Creates a StoredTheorem object for managing a theorem's
        __pv_it database entries.
        '''
        StoredSpecialStmt.__init__(self, context, name, 'theorem')

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

    def recordProof(self, proof):
        '''
        Record the given proof as the proof of this stored theorem.  Updates
        dependency links (usedAxioms.txt, usedTheorems.txt, and usedBy.txt files)
        and proven dependency indicators (various provenTheorems.txt files 
        for theorems that depend upon this one) appropriately.
        '''
        from proveit._core_ import Proof
        from context import Context
        
        if self.hasProof():
            # remove the old proof if one already exists
            self.removeProof()
                    
        # record the proof id
        if not isinstance(proof, Proof):
            raise ValueError("Expecting 'proof' to be a Proof object")
        proofId = self.context._storage._proveItStorageId(proof)
        with open(os.path.join(self.path, 'proof.pv_it'), 'w') as proofFile:
            proofFile.write(proofId)
            self.context._storage._addReference(proofId)
        
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
        
        # record axioms/theorems that this theorem directly uses
        for usedStmts, usedStmtsFilename in ((usedAxioms, 'usedAxioms.txt'), (usedTheorems, 'usedTheorems.txt')):
            with open(os.path.join(self.path, usedStmtsFilename), 'w') as usedStmtsFile:
                for usedStmt in sorted(usedStmts):
                    self.context._includeMutualReferences(usedStmt.context)
                    usedStmtsFile.write(usedStmt + '\n')
        
        # record any used theorems that are already completely proven
        with open(os.path.join(self.path, 'completeUsedTheorems.txt'), 'w') as completedTheoremsFile:
            for usedTheorem in usedTheorems:
                if Context.getStoredTheorem(usedTheorem).isComplete():
                    completedTheoremsFile.write(usedTheorem + '\n')
        
        # for each used axiom/theorem, record that it is used by the newly proven theorem
        storedUsedAxioms = [axiom._storedAxiom() for axiom in usedAxioms]
        storedUsedTheorems = [theorem._storedTheorem() for theorem in usedTheorems]
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
        return self._countEntries('usedTheorems.txt')

    def numCompleteUsedTheorems(self):
        return self._countEntries('completeUsedTheorems.txt')
    
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
        from context import Context
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
        from context import Context 
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
        os.remove(os.path.join(self.path, 'proof.pv_it'))
        os.remove(os.path.join(self.path, 'usedAxioms.txt'))
        os.remove(os.path.join(self.path, 'usedTheorems.txt'))
        os.remove(os.path.join(self.path, 'completeUsedTheorems.txt'))

    def allRequirements(self):
        '''
        Returns the set of axioms that are required (directly or indirectly)
        by the theorem.  Also, if the given theorem is not completely proven,
        return the set of unproven theorems that are required (directly or
        indirectly).  Returns this axiom set and theorem set as a tuple.
        '''
        from context import Context
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
        from context import Context
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
        from context import Context
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



'''
A theory in Prove-It is a conceptual space of related literals, axioms,
and theorems.  Consider, for example, a mathematics subject area such
as trigonometry or linear algebra.  A theory could represent such a
subject area, or a reasonable subset of such a subject area.  Such
theories are represented in directories.  The directory will contain
Jupyter notebooks for common expressions (common.ipynb) including
literals, axioms (axioms.ipynb), and theorems (theorems.ipynb).  It
will also contain Python scripts for defining Operation or Literal classes
for building Expression objects specific to the theory with convenient
methods for invoking theorems and automated derivations.  Proofs of
the theorems are to be stored in a _proofs_ sub-directory as Jupyter
notebooks named for the theorem to be proven.

A __pv_it sub-directory is generated to store a distributed
"database" of information pertaining to the theory.  It stores Expression
entries along with latex and png representations for convenience.  It
enumerates the Axioms and the Theorems, pointing to these Expression entries.
It also stores Judgment and Proof entries for the purpose of storing
the theorem proofs, and it stores theorem proof dependencies.
'''

import os
import json
from collections import OrderedDict
from ._theory_storage import TheoryStorage, TheoryFolderStorage, relurl
from types import ModuleType


class Theory:
    '''
    A Theory object provides an interface into the __pv_it database for access
    to the common expressions, axioms, theorems and associated proofs of a
    Prove-It theory.  You can also store miscellaneous expressions (and
    their latex/png representations) generated in test/demonstration notebooks
    within the theory directory.  These may be garbage collected via the
    'clean' method; anything that is not associated with a common
    expression, axiom, theorem, or theorem proof will be garbage collected.
    '''

    # maps root theory names to their directories.  A root theory
    # is one use containing directory has no __init__.py.  All theory
    # directories should have an __init__.py file.
    _rootTheoryPaths = dict()

    # The current default Theory when a Literal is created.
    # If this is None, use Theory(), the Theory at the current working
    # directory.
    default = None

    # Track the storage object associated with each theory and folder,
    # mapped by the absolute path.
    storages = dict()

    special_expr_kind_to_module_name = {
        'common': 'common',
        'axiom': 'axioms',
        'defining_property': 'definitions',
        'theorem': 'theorems'}

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information in
        the Theory jurisdiction.
        '''
        Theory._rootTheoryPaths.clear()
        Theory.default = None
        Theory.storages.clear()
        TheoryFolderStorage.active_theory_folder_storage = None
        TheoryFolderStorage.proveit_object_to_storage.clear()
        TheoryFolderStorage.owned_hash_folders.clear()

    # externals.txt at top level to track relative path to external
    # theories.
    def __init__(self, path='.', active_folder=None, owns_active_folder=False):
        '''
        Create a Theory for the given path.  If given a file name instead,
        use the path of the containing directory.  If no path
        is provided, base the theory on the current working directory.
        '''
        if not os.path.exists(path):
            raise TheoryException(
                "%s is not a valid path; unable to create Theory." %
                path)
        
        # We'll note the Literals of the Theory (definined as a common
        # expression or as an _operator_ of an Operation.)
        self._literals = set()

        path = os.path.abspath(path)
        # If in a __pv_it_ directory, go to the containing theory
        # directory.
        splitpath = path.split(os.path.sep)
        if '__pv_it' in splitpath:
            pv_it_idx = splitpath.index('__pv_it')
            num_up_levels = (len(splitpath) - pv_it_idx)
            # if num_up_levels > 1:
            #    active_folder = splitpath[pv_it_idx+1]
            path = os.path.abspath(os.path.join(
                *([path] + ['..'] * num_up_levels)))
        # If in a _theory_nbs_ directory, go to the 
        # containing theory directory.
        splitpath = path.split(os.path.sep)
        if '_theory_nbs_' in splitpath:
            nbs_idx = splitpath.index('_theory_nbs_')
            num_up_levels = (len(splitpath) - nbs_idx)
            path = os.path.abspath(os.path.join(
                *([path] + ['..'] * num_up_levels)))

        # move the path up to the directory level, not script file level
        if path[-3:] == '.py' or path[-4:] == '.pyc':
            path, _ = os.path.split(path)

        # Makes the case be consistent in operating systems (i.e. Windows)
        # with a case insensitive filesystem:
        normpath = os.path.normcase(path)

        if normpath in Theory.storages:
            # got the storage - we're good
            self._storage = Theory.storages[normpath]
            self.name = self._storage.name
            if active_folder is not None:
                self.set_active_folder(active_folder, owns_active_folder)
            return

        if os.path.isfile(
                path):  # just in case checking for '.py' or '.pyc' wasn't sufficient
            path, _ = os.path.split(path)
            normpath = os.path.normcase(path)

        if normpath in Theory.storages:
            # got the storage - we're good
            self._storage = Theory.storages[normpath]
            self.name = self._storage.name
            if active_folder is not None:
                self.set_active_folder(active_folder, owns_active_folder)
            return

        # the name of the theory is based upon the directory, going
        # up the tree as long as there is an __init__.py file.
        name = ''
        remaining_path = path
        while os.path.isfile(os.path.join(remaining_path, '__init__.py')):
            remaining_path, tail = os.path.split(remaining_path)
            name = tail if name == '' else (tail + '.' + name)
        # the root theory tracks paths to external packages
        if name == '':
            name = path
            raise TheoryException(
                '%s theory directory must have an __init__.py file' %
                path)
        root_directory = None
        if '.' in name:
            root_directory = os.path.join(remaining_path, name.split('.')[0])
        # Create the Storage object for this Theory
        if normpath not in Theory.storages:
            Theory.storages[normpath] = TheoryStorage(
                self, name, path, root_directory)
        self._storage = Theory.storages[normpath]
        if active_folder is not None:
            self.set_active_folder(active_folder, owns_active_folder)
        self.name = self._storage.name

    def __eq__(self, other):
        return self._storage is other._storage

    def __ne__(self, other):
        return self._storage is not other._storage

    def __str__(self):
        return self._storage.name

    def set_active_folder(self, active_folder, owns_active_folder=False):
        self.active_folder = active_folder
        if active_folder is not None:
            TheoryFolderStorage.active_theory_folder_storage = \
                self._theory_folder_storage(active_folder)
        else:
            TheoryFolderStorage.active_theory_folder_storage = None
            assert owns_active_folder == False
        TheoryFolderStorage.owns_active_storage = owns_active_folder

    def links(self, from_directory='.'):
        theory_name_segments = self._storage.name.split('.')
        theory_html_segments = []
        for k, theory_name_segment in enumerate(theory_name_segments):
            path = os.path.join(*([self._storage.directory] +
                                  ['..'] * (len(theory_name_segments) - k - 1) +
                                  ['_theory_nbs_', 'theory.ipynb']))
            url_link = relurl(path, start=from_directory)
            theory_html_segments.append(
                r'<a class=\"ProveItLink\" href=\"%s\">%s</a>' %
                (json.dumps(url_link).strip('"'), theory_name_segment))
        return '.'.join(theory_html_segments)

    def is_root(self):
        '''
        Return True iff this Theory is a "root" Theory (no parent
        directory with an __init__.py file).
        '''
        return self._storage.is_root()

    def get_path(self):
        '''
        Return the directory associated with the theory
        '''
        return self._storage.directory

    @staticmethod
    def _setRootTheoryPath(theory_name, path):
        path = os.path.normpath(os.path.abspath(path))
        if theory_name in Theory._rootTheoryPaths:
            stored_path = Theory._rootTheoryPaths[theory_name]
            if os.path.normcase(stored_path) != os.path.normcase(path):
                raise TheoryException(
                    "Conflicting directory references to theory '%s': %s vs %s" % (theory_name,
                                                                                   path,
                                                                                   stored_path))
        Theory._rootTheoryPaths[theory_name] = path

    @staticmethod
    def get_theory(theory_name):
        '''
        Return the Theory with the given name.
        '''
        split_theory_name = theory_name.split('.')
        root_name = split_theory_name[0]
        if root_name not in Theory._rootTheoryPaths:
            raise TheoryException(
                "Theory root '%s' is unknown (%s)" %
                (root_name, Theory._rootTheoryPaths))
        root_directory = Theory._rootTheoryPaths[root_name]
        return Theory(os.path.join(
            *([root_directory] + split_theory_name[1:])))

    def get_sub_theory_names(self):
        return self._storage.get_sub_theory_names()

    def generate_sub_theories(self):
        '''
        Yield the Theory objects for the sub-theories.
        '''
        for sub_theory_name in self._storage.get_sub_theory_names():
            yield Theory(os.path.join(self._storage.directory, sub_theory_name))

    def set_sub_theory_names(self, sub_theory_names):
        return self._storage.set_sub_theory_names(sub_theory_names)

    def append_sub_theory_name(self, sub_theory_name):
        return self._storage.append_sub_theory_name(sub_theory_name)

    def _set_axioms(self, axiom_definitions):
        if not isinstance(axiom_definitions, OrderedDict):
            raise TypeError("'axioms_definitions' must be an OrderedDict")
        self._storage.set_special_expressions(axiom_definitions,
                                              'axiom')

    def _set_defining_properties(self, definitions_for_properties):
        if not isinstance(definitions_for_properties, OrderedDict):
            raise TypeError("'definitions_for_properties' must be "
                            "an OrderedDict")
        self._storage.set_special_expressions(definitions_for_properties,
                                              'defining_property')

    def _set_theorems(self, theorem_definitions):
        if not isinstance(theorem_definitions, OrderedDict):
            raise TypeError("'theorem_definitions' must be an OrderedDict")
        self._storage.set_special_expressions(
            theorem_definitions, 'theorem')

    def _clear_axioms(self):
        self._set_axioms([], dict())

    def _clear_defining_properties(self):
        self._set_defining_properties([], dict())

    def _clear_theorems(self):
        self._set_theorems([], dict())

    def _clear_common_exressions(self):
        self._set_common_expressions([], dict(), clear=True)

    def _set_common_expressions(self, expr_definitions):
        if not isinstance(expr_definitions, OrderedDict):
            raise TypeError("'expr_definitions' must be an OrderedDict")
        self._storage.set_common_expressions(expr_definitions)

    @property
    def literals(self):
        return self._storage._literals

    def get_axiom_names(self):
        '''
        Return the names of the axioms in this Theory.
        '''
        return self._storage.get_axiom_names()

    def get_defining_property_names(self):
        '''
        Return the names of the defining properties of Literal
        definitions in this Theory.
        '''
        return self._storage.get_defining_property_names()

    def get_theorem_names(self):
        '''
        Return the names of the theorems in this Theory.
        '''
        return self._storage.get_theorem_names()

    def get_common_expression_names(self):
        '''
        Return the names of the common expression in this Theory.
        '''        
        return self._storage.get_common_expression_names()

    def get_theory_expression_names(self):
        '''
        Return the names of the common expressions, axioms, theorems 
        in this Theory.
        '''        
        return  self._storage.get_theory_expression_names()

    def get_expression_kind(self, name):
        '''
        Return 'common', 'axiom', or 'theorem' if the given name
        is the name of a common expression, axiom, or theorem of this
        Theory respectively.
        '''
        return  self._storage.get_expression_kind(name)

    def stored_common_expr_dependencies(self):
        '''
        Return the stored set of theory names of common expressions
        referenced by the common expressions of this theory.
        '''
        return self._storage.stored_common_expr_dependencies()

    def reference_hyperlinked_objects(self, name, clear=False):
        '''
        Reference displayed expressions, recorded under the given name
        in the __pv_it directory.  If the same name is reused,
        any expressions that are not displayed this time that
        were displayed last time will be unreferenced.
        If clear is True, remove all of the references and the
        file that stores these references.
        '''
        self._storage.reference_hyperlinked_objects(name, clear)

    def get_axiom(self, name):
        '''
        Return the Axiom of the given name in this theory.
        '''
        return self._storage.get_axiom(name)

    def get_theorem(self, name):
        '''
        Return the Theorem of the given name, or 
        DefinitionExistence if that theorem doesn't exist.
        '''
        try:
            return self._storage.get_theorem(name)
        except KeyError:
            return self._storage.get_definition_existence(name)            

    def get_defining_property(self, name):
        '''
        Return the DefiningProperty of the given name in this theory.
        '''
        return self._storage.get_defining_property(name)

    def get_definition_existence(self, name):
        '''
        Return the DefinitionExistence associated with the defining
        property of the given name in this theory.
        '''
        return self._storage.get_definition_existence(name)

    def get_definition_extension(self, name):
        '''
        Return the DefinitionExistence associated with the defining
        property of the given name in this theory.
        '''
        return self._storage.get_definition_extension(name)

    def generate_local_axioms(self):
        '''
        Yield each of the axioms contained at the local level
        of this theory.
        '''
        for name in self.get_axiom_names():
            yield self.get_axiom(name)

    def generate_all_contained_axioms(self):
        '''
        Yield each of the axioms contained both at the local
        level of this theory and recursively through contained
        theorys.
        '''
        for axiom in self.generate_local_axioms():
            yield axiom
        for theory in self.generate_sub_theories():
            for axiom in theory.generate_all_contained_axioms():
                yield axiom

    @staticmethod
    def find_axiom(full_name):
        '''
        Given the full name of an axiom that includes the theory
        name, return the Axiom obtained from the proper Theory.
        '''
        return Theory._findStmt(full_name, 'axiom')

    @staticmethod
    def find_defining_property(full_name):
        '''
        Given the full name of a defining property that includes the theory
        name, return the DefiningProperty obtained from the proper Theory.
        '''
        return Theory._findStmt(full_name, 'defining property')

    @staticmethod
    def find_theorem(full_name):
        '''
        Given the full name of an theorem that includes the theory
        name, return the Theorem obtained from the proper Theory.
        '''
        return Theory._findStmt(full_name, 'theorem')

    @staticmethod
    def _findStmt(full_name, kind):
        split_name = full_name.split('.')
        theory_name, stmt_name = '.'.join(split_name[:-1]), split_name[-1]
        theory = Theory.get_theory(theory_name)
        if kind == 'axiom':
            return theory.get_axiom(stmt_name)
        if kind == 'defining property':
            return theory.get_defining_property(stmt_name)
        if kind == 'theorem':
            return theory.get_theorem(stmt_name)

    @staticmethod
    def extract_markdowntitle_of_notebook(nb_str, replace_str=None):
        '''
        Given a Prove-It notebook as a string, extract the
        title displayed at the top of the first markdown
        cell.  If a 'replace_str' is given, then replace
        this title with the given replacement string and
        also return this replacement.
        '''
        idx = nb_str.find("source")  # find the source of the first cell
        idx = nb_str.find("[", idx)  # find the following '['
        idx = nb_str.find('"', idx)  # find the following '"'
        end_idx = nb_str.find(r'\n"', idx)  # find the end
        if idx == -1 or end_idx == -1:
            raise ValueError("Notebook not in proper format")
        title = nb_str[idx + 1:end_idx]
        if replace_str is None:
            return title
        else:
            if title != replace_str:
                nb_str = nb_str[:idx + 1] + replace_str + nb_str[end_idx:]
            return (title, nb_str)

    @staticmethod
    def update_title_if_needed(filename, generic_nb_str):
        '''
        Check if the notebook stored in 'filename' has the same
        markdown title as the generic version.  If not, update
        it to the generic version.  Return the possibly updated
        notebook string, or None if it file was not in an
        expected format to be able to extract the title.
        '''
        generic_title = Theory.extract_markdowntitle_of_notebook(
            generic_nb_str)
        with open(filename, 'r', encoding='utf8') as _f:
            nb_str = _f.read()
        try:
            existing_title, nb_str = \
                Theory.extract_markdowntitle_of_notebook(
                    nb_str, generic_title)
        except ValueError:
            # The format is not correct; stash this one and
            # generate a new one.
            existing_title, nb_str = None, None
        if nb_str is not None:
            if existing_title != generic_title:
                # Update the title.
                # Remove the file before creating again to force
                # new capitalization (e.g., in Windows where
                # capitalization can be flexible)
                os.remove(filename)
                with open(filename, 'w', encoding='utf8') as _f:
                    _f.write(nb_str)
        return nb_str

    @staticmethod
    def update_proving_name_if_needed(filename, theorem_name, *,
                                      definition_existence_proof,
                                      definition_extension_proof):
        '''
        Check if the notebook stored in 'filename' has the
        correct name following %proving.  If not, fix it.
        Return the possibly updated notebook string, or None
        if it file was not in an expected format to be able
        to extract the title.
        '''
        with open(filename, 'r', encoding='utf8') as _f:
            nb_str = _f.read()
        if definition_existence_proof:
            proving_str = '"%existence_proving '
        elif definition_extension_proof:
            proving_str = '"%extension_proving '
        else:
            proving_str = '"%proving '
        proving_str_idx = nb_str.find(proving_str)
        if proving_str_idx == -1:
            return None
        end_quote_idx = nb_str.find('"', proving_str_idx + 1)
        if end_quote_idx == -1:
            return None
        existing_name = nb_str[proving_str_idx +
                               len(proving_str):end_quote_idx]
        if existing_name != theorem_name:
            # Replace the name with the appropriate name.
            nb_str = (nb_str[:proving_str_idx] + proving_str +
                      theorem_name + nb_str[end_quote_idx:])
            with open(filename, 'w', encoding='utf8') as _f:
                _f.write(nb_str)
        return nb_str

    def proof_notebook(self, proof):
        '''
        Return the "basic" proof notebook corresponding to the given
        proof_id.  Note, this is different than a "theorem" proof
        notebook which generates the proof.  This just shows the
        proof as Prove-It stores it.
        '''
        theory_folder_storage = \
            TheoryFolderStorage.active_theory_folder_storage
        return theory_folder_storage.proof_notebook(proof)

    def thm_proof_notebook(self, theorem_name, expr, num_duplicates=0,
                           definition_existence_proof=False,
                           definition_extension_proof=False):
        '''
        Return the path of the proof notebook for a theorem with the
        given name and expression, creating it if it does not already
        exist.  num_duplicates is the number of previous instances
        of the expression that we have encountered.
        '''
        return self._storage.thm_proof_notebook(
                theorem_name, expr, num_duplicates, 
                definition_existence_proof, definition_extension_proof)

    def stash_extraneous_thm_proof_notebooks(
            self, *, definition_existence_proofs=False,
            definition_extension_proofs=False):
        '''
        For any proof notebooks for theorem names not included in the
        theory, stash them or remove them if they are generic notebooks.
        '''
        if definition_existence_proofs or definition_extension_proofs:
            # This is good enough for now.  Technically, only the
            # last of a defining property collection (in a cell of
            # a definitions notebook) will have an associated proof,
            # so this way may keep things around that become obsolete.
            # But it is better to err on the side of stashing too little
            # than too much.
            thm_names = self.get_defining_property_names()
        else:
            thm_names = self.get_theorem_names()
        self._storage.stash_extraneous_thm_proof_notebooks(
            thm_names, definition_existence_proofs=definition_existence_proofs,
            definition_extension_proofs=definition_extension_proofs)

    @staticmethod
    def expression_notebook(expr, name_kind_theory=None,
                            complete_special_expr_notebook=False):
        '''
        Return the path of the expression notebook, creating it if it
        does not already exist.  If 'name_kind_theory' is
        provided, it should be the (name, kind, theory) for a special
        expression that may or may not be complete/official
        (%end_[common/axioms/theorems] has not been
        called yet in the special expressions notebook).
        '''
        # use the Storage object to generate/grab the expression notebook.
        return TheoryFolderStorage.expression_notebook(
            expr, name_kind_theory, complete_special_expr_notebook)

    @staticmethod
    def get_stored_axiom(fullname):
        return Theory.get_stored_stmt(fullname, 'axiom')

    @staticmethod
    def get_stored_defining_property(fullname):
        return Theory.get_stored_stmt(fullname, 'defining_property')

    @staticmethod
    def get_stored_definition_existence(fullname):
        return Theory.get_stored_stmt(fullname, 'definition_existence')

    @staticmethod
    def get_stored_definition_extension(fullname):
        return Theory.get_stored_stmt(fullname, 'definition_extension')

    @staticmethod
    def get_stored_theorem(fullname):
        '''
        Return the stored theorem of the given name, or stored
        definition existence if that theorem doesn't exist.
        '''
        try:
            return Theory.get_stored_stmt(fullname, 'theorem')
        except:
            return Theory.get_stored_stmt(fullname, 'definition_existence')

    @staticmethod
    def get_stored_stmt(fullname, kind):
        from ._theory_storage import (StoredAxiom, StoredTheorem,
                                      StoredDefiningProperty,
                                      StoredDefinitionExistence,
                                      StoredDefinitionExtension)
        split_name = fullname.split('.')
        theory_name = '.'.join(split_name[:-1])
        stmt_name = split_name[-1]
        theory = Theory.get_theory(theory_name)
        if kind == 'axiom':
            return StoredAxiom(theory, stmt_name)
        elif kind == 'defining_property':
            return StoredDefiningProperty(theory, stmt_name)
        elif kind == 'definition_existence':
            return StoredDefinitionExistence(theory, stmt_name)
        elif kind == 'definition_extension':
            return StoredDefinitionExtension(theory, stmt_name)
        elif kind == 'theorem':
            return StoredTheorem(theory, stmt_name)
        else:
            raise TheoryException(
                "Expecting 'kind' to be 'axiom' or 'theorem' not '%s'" %
                kind)

    def get_common_expr(self, name):
        '''
        Return the Expression of the common expression in this theory
        with the given name.
        '''
        return self._storage.get_common_expr(name)

    def get_stored_expr(self, expr_id, folder=None):
        '''
        Return the stored Expression with the given id (hash string).
        Use the "active folder" as the default folder.
        '''
        theory_folder_storage = self._theory_folder_storage(folder)
        return theory_folder_storage.make_expression(expr_id)

    def get_stored_judgment_or_proof(self, storage_id, folder=None):
        '''
        Return the stored Judgment or Proof with the given id
        (hash string).  Use the "active folder" as the default folder.
        '''
        theory_folder_storage = self._theory_folder_storage(folder)
        return theory_folder_storage.make_judgment_or_proof(storage_id)

    def get_show_proof(self, proof_id, folder=None):
        '''
        Return the _ShowProof representing the proof with the
        given id (hash string) for display purposes.
        Use the "active folder" as the default folder.
        '''
        theory_folder_storage = self._theory_folder_storage(folder)
        return theory_folder_storage.make_show_proof(proof_id)

    @staticmethod
    def _stored_png(expr, latex, config_latex_tool_fn):
        '''
        Find the .png file for the stored Expression.
        Create it if it did not previously exist.
        Return the png data and path where the png is stored as a tuple.
        '''
        return TheoryFolderStorage.retrieve_png(
            expr, latex, config_latex_tool_fn)

    def _theory_folder_storage(self, folder=None, kind=None):
        '''
        Return the TheoryFolderStorage object associated with this
        theory and the folder.  The default folder is the
        "active_folder".
        '''
        if folder is None:
            if kind is None:
                folder = self.active_folder
            else:
                folder = self._storage._kind_to_folder(kind)
        if folder is None:
            raise ValueError("A 'folder' must be specified")
        return self._storage.theory_folder_storage(folder)

    def _common_storage(self):
        return self._theory_folder_storage('common')

    def clean_active_folder(self, clear=False):
        '''
        Clean the corresponding __pv_it directory of any stored expressions
        or proofs that have a reference count of zero.
        '''
        theory_folder_storage = self._theory_folder_storage(self.active_folder)
        if theory_folder_storage is not None:
            return theory_folder_storage.clean(clear)

    def contains_any_expression(self):
        '''
        Return True if this theory and all of its sub-theories
        contain no expressions.
        '''
        if self._storage.contains_any_expression():
            return True
        for sub_theory in self.generate_sub_theories():
            if sub_theory.contains_any_expression():
                return True
        return False

class TheoryPackage(ModuleType):
    '''
    Used in __init__.py modules of theory packages for accessing 
    common expressions, axioms, and theorems of the package.
    '''
    
    def __init__(self, name, filename, attr_dict):
        ModuleType.__init__(self, name)
        self._theory = Theory(filename)
        self.__file__ = filename
        self.__dict__.update(attr_dict)
    
    def __dir__(self):
        expression_axiom_and_theorems_names = \
            self._theory.get_theory_expression_names()
        return sorted(list(self.__dict__.keys()) + 
                      list(expression_axiom_and_theorems_names))
    
    def __getattr__(self, name):
        '''
        Allow common expressions, axioms, defining propreties, and 
        theorems to be imported from the theory package.  If the name 
        is not found, and a common expression notebook is currently 
        runninng, assume the missing name is a common expression that 
        hasn't been defined yet and return an 
        UnsetCommonExpressionPlaceholder.
        '''
        if name[0:2]=='__': 
            # don't handle internal Python attributes
            raise AttributeError 
        try:
            kind = self._theory.get_expression_kind(name)
        except KeyError:
            # By default, we'll assume it is a common expression
            # so we can deal with unset common expressions 
            # appropriately via UnsetCommonExpressionPlaceholder.
            kind = 'common'

        if kind == 'axiom':
            return self._theory.get_axiom(name).proven_truth
        elif kind == 'theorem':
            return self._theory.get_theorem(name).proven_truth
        elif kind == 'defining_property':
            return self._theory.get_defining_property(name).proven_truth
        try:
            return self._theory.get_common_expr(name)
        except (KeyError, OSError, TheoryException):
            import proveit
            if proveit.defaults._running_theory_notebook is not None:
                running_theory, running_kind = \
                    proveit.defaults._running_theory_notebook
                if running_kind == 'common':
                    # Failed to import a common expression while
                    # executing a common expression notebook.  Maybe the
                    # other notebook must be executed first.  Return an
                    # UnsetCommonExpressionPlaceholder.
                    # If this placeholder is used in creating any
                    # expression, record the import failure and raise an
                    # exception so we know to execute the other common
                    # expression notebook first.
                    return UnsetCommonExpressionPlaceholder(
                            self._theory,  name)
            raise AttributeError(
                    "'%s' not found in the list of common expressions, "
                    "axioms, or theorems of '%s'\n(make sure to execute "
                    "the appropriate 'common.ipynb' notebook after any "
                    "changes)"%(name, self._theory.name))

class UnsetCommonExpressionPlaceholder(object):
    '''
    A placeholder for a common expression that was attempted to be
    imported from a common expression notebook but fails to import.
    If it isn't used, don't worry about it.  If the notebook attempts
    to use it, mark it as a failed import and raise an exception --
    run the other notebook (from which there was a failed import) before
    trying again.
    '''

    def __init__(self, theory, name):
        self.theory = theory
        self.name = name

    def __str__(self):
        self.raise_attempted_use_error()

    def __repr__(self):
        self.raise_attempted_use_error()

    def raise_attempted_use_error(self):
        '''
        An error occurs when there is any attempt to use this
        placeholder.  Record this failure so we know to execute the
        other notebook first (used in build.py).
        Raise an exception.
        '''
        # File to store information about a failure to
        # import a common expression:
        import proveit
        import_failure_filename = \
            proveit.defaults.import_failure_filename
        assert proveit.defaults._running_theory_notebook is not None, (
            "Should only use UnsetCommonExpressionPlaceholder when "
            "executing a common expression notebook.")
        running_theory, running_kind = \
            proveit.defaults._running_theory_notebook
        assert self.theory.name != running_theory.name, (
            "Cannot reference %s.%s within the notebook that creates "
            "it." % (self.theory.name, self.name))
        with open(import_failure_filename, 'w') as f:
            f.write(self.theory.name + '\n')
        raise CommonExpressionDependencyError(
            "Must execute 'common.ipynb' for the theory of %s "
            "to define '%s' before it may be used" %
            (self.theory.name, self.name))


class TheoryException(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


class CommonExpressionDependencyError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message

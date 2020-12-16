'''
Build the Prove-It notebooks (common expressions, axioms, theorems,
and proofs) for the given theories, including sub-theories.
'''

from __future__ import print_function
import sys
import os
import subprocess
import re
import time
import lxml#Comment in for Python 3
from lxml import etree#Comment in for Python 3
import shutil
import argparse
import nbformat
from nbconvert.preprocessors import Preprocessor, ExecutePreprocessor
#from nbconvert.preprocessors.execute import executenb
from nbconvert import HTMLExporter
import IPython
from IPython.lib.latextools import LaTeXTool
import base64
import datetime
import tarfile
#import urllib#Comment out for Python 3
import urllib.request#Comment in for Python 3
import zmq # to catch ZMQError which randomly occurs when starting a Jupyter kernel
import proveit
from proveit import Theory

#IPython.InteractiveShell.cache_size=0

# for compiling LaTeX
LaTeXTool.clear_instance()
lt = LaTeXTool.instance()
lt.use_breqn = False

default_paths = ['packages/proveit', 'tutorial']#, 'tutorial/socks_demo']

def find_theory_paths(path):
    if os.path.isfile(os.path.join(path, '_theory_.ipynb')):
        yield path
        sub_theories_txt = os.path.join(path, '_sub_theories_.txt')
        if os.path.isfile(sub_theories_txt):
            for sub_theory in open(sub_theories_txt).readlines():
                sub_theory = sub_theory.rstrip() # strip off the carriage return
                sub_theory_path = os.path.join(path, sub_theory)
                for theory_path in find_theory_paths(sub_theory_path):
                    yield theory_path

# regular expression for finding 'a' html tags; trivially adapted from
# http://haacked.com/archive/2004/10/25/usingregularexpressionstomatchhtml.aspx/
atag_re = r"""<a((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""
imgtag_re = r"""<img((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""


"""
def revised_proof_nb(nb, notebook_path):
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'markdown':
            cell.source = cell.source.replace('\\\\', '\\')
            cell.source = cell.source.replace('\\"', '"')
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb
"""
"""
def revised_special_nb(nb, notebook_path):
    # this is temporarily needed for some backwards compatibility
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'code':
            cell.source = cell.source.replace('%begin_', '%begin ')
            cell.source = cell.source.replace('%end_', '%end ')
        new_cells.append(cell)
    nb.cells = new_cells            
    return nb
"""

class ProveItHTMLPreprocessor(Preprocessor):
    '''
    The Prove-It HTML processor will change links from ipynb
    to html and remove "target=blank".  Further, it is used to
    consolidate style information.
    '''
    
    def __init__(self, strip_links=False, make_images_inline=False):
        self.strip_links = strip_links
        self.make_images_inline = make_images_inline
        self.path = '.'
    
    def _process_atags(self, text):
        '''
        Search the text for html a-tags of the ProveItLink class.
        For each of these, replace .ipynb with .html and remove 
        any target='_blank' (so it does not create a new tab 
        in the browser).  Return the new version of the text.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for atag_match in re.finditer(atag_re, text):
            atag = text[atag_match.start():atag_match.end()]
            new_text += text[last_pos:atag_match.start()]
            # parse the a tag with a xml parser
            atag_root = lxml.etree.fromstring(atag + '</a>')
            if 'class' in atag_root.attrib and atag_root.attrib['class']=='ProveItLink':
                if '.ipynb' in atag_root.attrib['href']:
                    # replace the .ipynb extension in the href with .html
                    atag_root.attrib['href'] = atag_root.attrib['href'].replace('.ipynb', '.html')
                    # also, if the .ipynb link uses target='blank', nix that.
                    if 'target' in atag_root.attrib and atag_root.attrib['target']=='_blank':
                        atag_root.attrib.pop('target')
                    atag = lxml.etree.tostring(atag_root)
                    if atag[-2:] != b'/>':
                        raise Exception("Expecting '/>' at end of remade xml a-tag")
                    atag = atag[:-2].decode('ascii') + '>' # remove the / before >
            if not self.strip_links:
                new_text += atag
            last_pos = atag_match.end()
        new_text += text[last_pos:]
        if self.strip_links:
            return re.sub('</a>', '', new_text) # strip the </a>'s as well as the <a ...>'s
        else:
            return new_text

    def _remove_tags(self, text):
        '''
        Remove html tags from the text.
        '''
        p = re.compile(r'<.*?>')
        return p.sub('', text)
    
    """
    def _process_latex(self, text):
        '''
        Search the markdown for '$...$' indicating LaTeX.  Generate a png in place of the LaTeX.
        '''
        revised_text = ''
        cur_pos = 0
        latex_start = text.find('$')
        while latex_start >= 0:
            latex_end = text.find('$', latex_start+1)
            latex = text[latex_start+1:latex_end]
            png = latex_to_png(latex, backend='dvipng', wrap=True) # the 'matplotlib' backend can do some BAD rendering in my experience (like \lnot rendering as lnot in some theories)
            revised_text += text[cur_pos:latex_start]
            revised_text += '<img style="vertical-align:text-bottom; display:inline;" src="data:image/png;base64,%s"/>'%base64.b64encode(png)
            cur_pos = latex_end+1
            latex_start = text.find('$', cur_pos)
        revised_text += text[cur_pos:]
        return revised_text
    """
    
    def _inline_images(self, text):
        '''
        Convert imported images to inline pngs.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for imgtag_match in re.finditer(imgtag_re, text):
            imgtag = text[imgtag_match.start():imgtag_match.end()]
            #print imgtag
            new_text += text[last_pos:imgtag_match.start()]
            # parse the img tag with a xml parser
            imgtag_root = lxml.etree.fromstring(imgtag)
            if 'src' in imgtag_root.attrib:
                png = open(os.path.join(self.path, imgtag_root.attrib['src']), 'rb').read() 
                imgtag_root.attrib['src'] = "data:image/png;base64,%s"%base64.b64encode(png)
                imgtag = lxml.etree.tostring(imgtag_root)
            #print imgtag
            new_text += imgtag
            last_pos = imgtag_match.end()
        new_text += text[last_pos:]
        return new_text
        
    def preprocess(self, nb, resources):
        proveit_path = os.path.split(proveit.__file__)[0]
        new_cells = []
        empty_cells = [] # skip empty cells at the end for a cleaner look
        title = None # take the first line of the first cell to be the title
        for cell in nb.cells:
            cell = cell.copy() # copy the cell and possibly edit the copy
            if cell.cell_type == 'markdown':
                if title is None:
                    title = self._remove_tags(cell.source.split('\n')[0])
                # process a-tags in markdown cell source, as well as LaTeX.
                cell.source = self._process_atags(cell.source) #self._process_latex(self._process_atags(cell.source))
            if cell.cell_type == 'code':
                if len(cell.source)==0:
                    # an empty cell.  if it is at the end, these will be skipped altogether for a cleaner look
                    empty_cells.append(cell)
                    continue 
                if 'outputs' in cell:
                    for output in cell['outputs']:
                        if 'data' in output and 'text/html' in output.data:
                            # process a-tags in html output
                            output.data['text/html'] = self._process_atags(output.data['text/html'])
                            if self.make_images_inline:
                                # make all images inline
                                output.data['text/html'] = self._inline_images(output.data['text/html'])                                
            if len(empty_cells) > 0:
                # fill in empty cells which are not at the end
                new_cells.extend(empty_cells)
                empty_cells = []
            new_cells.append(cell)
        nb.cells = new_cells  
        resources['today'] = str(datetime.datetime.today()).split()[0]
        resources['title'] = title
        index_path = os.path.join(proveit_path, '..', '..', 'index.html')
        logo_path = os.path.join(proveit_path, '..', '..', 'pv_it.png')
        if self.path == '': self.path = '.'
        relpath_to_index = os.path.relpath(index_path, self.path)
        relpath_to_logo = os.path.relpath(logo_path, self.path)
        resources['relpath_to_index'] = relpath_to_index
        resources['relpath_to_logo'] = relpath_to_logo
        return nb, resources

html_exporter = HTMLExporter(preprocessors=[ProveItHTMLPreprocessor()])
html_exporter.template_file = 'proveit_html'

def git_clear_notebook(notebook_path):
    try:
        # If the file is in a git repository which is filtering
        # the notebook output, see if the only change is in
        # the output.  In that case, 'git add' the file so it
        # doesn't show up as modified.
        process = subprocess.Popen(["git", "diff", notebook_path],
                                   stdout=subprocess.PIPE)
        output = process.communicate()[0]
        output = re.sub('^diff --git .*$', '', output.decode('utf-8'))
        if output=="":
            # No change except perhaps filtered output.
            # Do "git add" so it won't show up as different.
            process = subprocess.Popen(['git', 'add', notebook_path])
            print("Clearing filtered notebook-output modifications in git:"
                  "\n\tgit add %s"%notebook_path)
            process.wait()
    except:
        # Our git check may fail because maybe it isn't in a git
        # repository.  In that case, don't worry about it.
        pass

class KernelStartFailure(Exception):
    def __init__(self):
        pass

class RecyclingExecutePreprocessor(ExecutePreprocessor):
    def __init__(self, **kwargs):
        ExecutePreprocessor.__init__(self, **kwargs)
    
    def __enter__(self):
        try:
            self.km, self.kc = self.start_new_kernel()
        except RuntimeError:
            raise KernelStartFailure()
        return self
    
    def __exit__(self, exception_type, exception_value, traceback):
        self.kc.stop_channels() 
        self.km.shutdown_kernel() 
        self.km, self.kc = None, None
        
    def preprocess(self, nb, resources, path, display_latex):
        # Record initial loaded modules, including the proveit defaults and
        # proveit.magics.  All other modules will be deleted when
        # we are done so we can "recycle" our Kernel to be used cleanly
        # for the next notebook.
        
        init_modules_source = """
import sys
from proveit import *
from proveit import defaults
defaults.display_latex=%s
import proveit.magics
__init_modules = list(sys.modules.keys())
__init_modules # avoid Prove-It magic assignment
"""%display_latex

        init_modules_cell = nbformat.NotebookNode(cell_type='code', source=init_modules_source, metadata=dict())
        self.preprocess_cell(init_modules_cell, resources, 0)
                
        # change the working directory
        cd_source = 'import os\nos.chdir(r\"' + path + '")'        
        cd_cell = nbformat.NotebookNode(cell_type='code', source=cd_source, metadata=dict())
        self.preprocess_cell(cd_cell, resources, 0)
        
        try:
            # Execute each cell.  We must correct the execution count so we treat this
            # like it was the only notebook executed in this session (even though we
            # are actually recycling the Kernel).
            exec_count = 0
            for index, cell in enumerate(nb.cells): 
                if hasattr(cell, 'source') and cell['source'].strip() != '':
                    cell, resources = self.preprocess_cell(cell, resources, index)
                    if 'execution_count' in cell:
                        # make proper execution counts
                        exec_count += 1
                        cell['execution_count'] = exec_count
                        if 'outputs' in cell:
                            for output in cell['outputs']:
                                if 'execution_count' in output:
                                    output['execution_count'] = exec_count
                nb.cells[index]

            if display_latex:
                # for notebooks with no %end or %qed
                clean_cell = nbformat.NotebookNode(
                        cell_type='code', source="%clean_active_folder\n", 
                        metadata=dict())
                cell, _ = self.preprocess_cell(clean_cell, resources, 0)
        finally:
            # "reset" the stored Prove-It data.  Also,
            # Delete all modules except those that were initially loaded.
            # Also, %reset local variables and history.
            # We are preparing the Kernel to be recycled.
            reset_source = """
import sys
import proveit
proveit.reset()
# delete all modules but initial modules and proveit._core_ modules
for m in list(sys.modules.keys()):
    if m not in __init_modules:
        if '.' in m:
            parent, child = m.rsplit('.', 1)
            if parent in __init_modules:
                # remove the module being deleted from its parent package
                sys.modules[parent].__dict__.pop(child)
        del(sys.modules[m])
%reset
%reset in
%reset out
    """    
            reset_cell = nbformat.NotebookNode(cell_type='code', source=reset_source, metadata=dict())
            cell, _ = self.preprocess_cell(reset_cell, resources, 0)
            
            # Garbage collect.
            garbage_collect_source = """import sys
import gc
gc.collect()
len(gc.get_objects()) # used to check for memory leaks
    """
            garbage_collect_cell = nbformat.NotebookNode(cell_type='code', source=garbage_collect_source, metadata=dict())
            cell, _ = self.preprocess_cell(garbage_collect_cell, resources, 0)
            # Useful debugging to check for memory leaks:
            #print('num gc objects', cell['outputs'][0]['data']['text/plain'])    
        return nb, resources

    def execute_notebook(self, notebook_path, no_latex=False, git_clear=True):
        '''
        Read, execute, and write out the notebook at the given path.
        Return the notebook object.
        '''
        print("Executing", notebook_path)
        start_time = time.time()
        
        # Read in the notebook.
        with open(notebook_path, encoding='utf8') as f:
            nb_str = f.read().rstrip()
        nb = nbformat.reads(nb_str, as_version=4)

        # execute using a KernelManager with the appropriate cwd (current working directory)
        notebook_dir = os.path.abspath(os.path.split(notebook_path)[0])
        resources=dict()
        while True:
            try:
                #executenb(nb, cwd=notebook_dir)
                self.preprocess(nb, resources, notebook_dir, not no_latex)
                break
            except zmq.ZMQError:
                print("ZMQError encountered")
                pass
                #execute_processor.km.restart_kernel(newport=True)
            except RuntimeError:
                print("Try restarting kernel")
                pass
                #execute_processor.km.restart_kernel(newport=True)
        new_nb_str = nbformat.writes(nb)
        if new_nb_str != nb_str:
            # Write it out if it has changed.
            with open(notebook_path, 'wt', encoding='utf8') as f:
                f.write(new_nb_str)
        print("\tFinished %s in %0.2f seconds"%(notebook_path, time.time()-start_time))
        
        if git_clear:
            git_clear_notebook(notebook_path)
        
        return nb

def generate_css_if_missing(path):
    # check if there is a notebook.css file in the directory
    css_filename = os.path.join(path, 'notebook.css')
    if not os.path.isfile(css_filename):
        # create a notebook.css that links to a css file of the 
        # same name in the directory above it.
        with open(css_filename, 'wt') as f:
            f.write('@import url("../notebook.css")\n')
        generate_css_if_missing(os.path.split(path)[0])

def export_notebook_to_html(notebook_path, nb=None, strip_links=False, make_images_inline=False):
    '''
    Export the notebook to html provided the notebook path.
    The notebook object (nb) may be provided, or it will be
    read in from the file.
    '''
    start_time = time.time()
    orig_strip_links = html_exporter.preprocessors[0].strip_links
    orig_make_images_inline = html_exporter.preprocessors[0].make_images_inline
    try:
        html_exporter.preprocessors[0].strip_links = strip_links
        html_exporter.preprocessors[0].make_images_inline = make_images_inline
        html_exporter.preprocessors[0].path = os.path.split(notebook_path)[0]
        if nb is None:
            # read in if it wasn't provided
            with open(notebook_path, encoding='utf8') as f:
                nb = nbformat.read(f, as_version=4)
        # export to HTML
        (body, resources) = html_exporter.from_notebook_node(nb)
        with open(os.path.splitext(notebook_path)[0] + '.html', 'wt',
                  encoding='utf8') as f:
            f.write(body)
        generate_css_if_missing(os.path.split(notebook_path)[0]) # add notebook.css if needed
    finally:
        html_exporter.preprocessors[0].strip_links = orig_strip_links
        html_exporter.preprocessors[0].make_images_inline = orig_make_images_inline # revert back to what it was
    print('Exported', notebook_path, 'to HTML in %0.2f seconds'%(time.time()-start_time))

def execute_and_export_notebook(execute_processor, notebook_path, 
                             no_execute=False, no_latex=False, git_clear=True):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML. 
    '''
    if no_execute:
        export_notebook_to_html(notebook_path)
    else:
        nb = execute_processor.execute_notebook(notebook_path, 
                                               no_latex=no_latex, 
                                               git_clear=git_clear)
        export_notebook_to_html(notebook_path, nb)

def execute_and_maybe_export_notebook(
        execute_processor, notebook_path, no_execute=False, no_latex=False, 
        git_clear=True, export_to_html=True):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML. 
    '''
    theory_notebook_name = '_theory_.ipynb'
    if notebook_path[-len(theory_notebook_name):] == theory_notebook_name:
        # This is a theory notebook.
        # Set the mode to 'interactive' so it will toggle to 'static' mode
        # when we execute this theory notebook.
        with open(os.path.join(os.path.split(notebook_path)[0], '_mode_.txt'), 
                  'wt') as f:
            f.write('interactive\n') 
    if export_to_html:
        execute_and_export_notebook(execute_processor, notebook_path, 
                                 no_latex=no_latex, no_execute=no_execute, 
                                 git_clear=git_clear)
    elif not no_execute:
        execute_processor.execute_notebook(
                notebook_path, no_latex=no_latex, git_clear=git_clear)

"""
def revise_proof_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_proof_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)        
"""

"""
def revise_special_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_special_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)   
"""

def fix_theory(theory_path):
    mode = None
    with open(os.path.join(theory_path, '_sub_theories_.txt')) as f:
        sub_theory_names = []
        for k, line in enumerate(f.readlines()):
            if k==0 and line[:6] == 'mode: ':
                mode = line[6:].strip()
            else:
                sub_theory_names.append(line.strip())
        Theory(theory_path).set_sub_theory_names(sub_theory_names)
    if mode is not None:
        with open(os.path.join(theory_path, '_mode_.txt'), 'w') as fw:
            fw.write(mode + '\n')

def record_presuming_info(theorem, proof_notebook_path):
    '''
    Given a Theorem object and corresponding proof notebook path,
    record the presuming information from information on the
    "%proving" command line.  We need to execute preceeding commands
    because some of the presumed things may be local variables generated
    in the notebook.
    '''
    with open(proof_notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    print("Record presuming info:", proof_notebook_path)
    
    # use '__' to prepend important local variables because we will start
    # running exec on user code and we don't want to pollute our locals.
    __owd = os.getcwd()
    os.chdir(os.path.split(proof_notebook_path)[0])
    __theorem = theorem
    try:
        for __cell in nb['cells']:
            if __cell['cell_type'] == 'code':
                __cellsource = __cell['source']
                __locls = locals()
                __begin_proof_str = '%proving '
                if __cellsource[:len(__begin_proof_str)] == __begin_proof_str or '\n%proving' in __cellsource:
                    __start = __cellsource.find("%proving")
                    exec(__cellsource[:__start])
                    # intercept the proving command
                    __line=__cellsource[__start+len(__begin_proof_str):]
                    __theorem_name, __presuming_str = str(__line.strip()).split(' ', 1)
                    if __theorem_name != __theorem.name:
                        raise ValueError("Theorem name, %s, does not match expectation, %s, according to filename"%(__theorem_name, theorem.name))
                    if not __presuming_str.find('presuming ') == 0:
                        raise ValueError("Bad presuming format: %s"%__presuming_str)
                    __args = __presuming_str.split(' ', 1)[-1].strip('[]').split(',')
                    __args = [__arg.strip(" \\\n") for __arg in __args]
                    __presumptions = [__arg for __arg in __args if __arg != '']
                    # Some of the presumptions are simply strings, but some are local variables
                    # we need to extract.  That is why we had to execute the previous lines.
                    __presumptions = [str(__locls[__presumption].proof()) if __presumption in __locls else __presumption for __presumption in __presumptions]
                    __theorem.proven_truth.begin_proof(__theorem, __presumptions, just_record_presuming_info=True)
                    return
                elif __cellsource[0] != '%': # skip other magic commands (only the imports should really matter)
                    exec(__cellsource)
    finally:
        os.chdir(__owd)
    
def build(execute_processor, theory_paths, all_paths, no_execute=False, 
          just_execute_essentials=False, just_execute_proofs=False, 
          just_execute_demos=False, just_execute_expression_nbs=False,
          no_latex=False):
    '''
    Build all Theory-related notebooks (_common_, _axioms_,
    _theorems_, and proof notebooks for the theorems)
    in the theory_paths.
    For the paths in all_paths (which should include the
    theory paths), build any contained notebooks and
    any of the expr.ipynb and dependencies.ipnyb notebooks
    within the __pv_it directory (storing Prove-It "database"
    information).
    '''
    if not just_execute_proofs and not just_execute_demos and not just_execute_expression_nbs:
        if not just_execute_essentials:
            # Generate html pages from index.ipynb and guide.ipynb in the packages folder:
            if no_execute:
                export_notebook_to_html('index.ipynb')
                export_notebook_to_html('guide.ipynb')
            else:
                execute_and_export_notebook(execute_processor, 'index.ipynb')
                execute_and_export_notebook(execute_processor, 'guide.ipynb')
        
        # Make sure there is a _common_.py, _axioms_.py, and _theorems_.py
        # in each theory directory.
        # These will be useful in figuring out dependencies between _common_
        # notebooks (see CommonExpressions in proveit._core_.theory as well
        # as avoiding import errors.
        for theory_path in theory_paths:
            for spec_expr_kind in ('common', 'axioms', 'theorems'):
                Theory(theory_path).make_special_expr_module(spec_expr_kind)
        
        # Execute the _theory_ notebooks in each theory directory 
        # and generate _theory_.html.
        for theory_path in theory_paths:
            fix_theory(theory_path)
            theory_notebook_path = os.path.join(theory_path, '_theory_.ipynb')
            with open(os.path.join(theory_path, '_mode_.txt'), 'wt') as f:
                f.write('interactive\n') # when executed again, it will toggle to 'static' mode                
            # execute into static mode
            execute_and_export_notebook(execute_processor, theory_notebook_path, 
                                     no_execute=no_execute, no_latex=no_latex)
        
        # Next, run the _common_.ipynb (common expression) notebooks for the theories.
        # For any that depend up _common_.py of other theories, run the
        # requirements first.
        
        """
        common_nb_queue = list(theory_paths)
        exececuted_common_nb = set()
        while len(common_nb_queue) > 0:
            theory_path = common_nb_queue.pop(0)
            if theory_path in exececuted_common_nb:
                continue
            
            # The failed_common_import.txt file is used to communicate a failed
            # common expression import from another theory.  First erase this
            # file, then see if it is created after executing the common notebook.
            failed_common_import_filename = os.path.join(theory_path, '__pv_it', 'failed_common_import.txt')
            if os.path.isfile(failed_common_import_filename):
                os.remove(failed_common_import_filename)
                
            try:
                revise_special_notebook(os.path.join(theory_path, '_common_.ipynb'))
                execute_and_export_notebook(os.path.join(theory_path, '_common_.ipynb'))
                exececuted_common_nb.add(theory_path) # finished successfully
            except execute.CellExecutionError as e:            
                retry = False
                if os.path.isfile(failed_common_import_filename):
                    # A failed_common_import.txt file was created.  It will indicate the
                    # theory from which a common expression was attempted to be imported.
                    # If its _common_ notebook has not already executed, execute it first
                    # and then try to execute this one again.
                    with open(failed_common_import_filename, 'r') as f:
                        required_theory_name = f.read().strip()
                        if required_theory_name not in exececuted_common_nb:
                            print '  Failed to execute; try a prerequisite first:', required_theory_name
                            common_nb_queue.insert(0, theory_path) # re-insert to try again
                            # but first execute the _common_ notebook from the required_theory.
                            common_nb_queue.insert(0, theory_map[required_theory_name])
                            retry = True
                if not retry:
                    raise e
        """
        
        if no_execute:
            for theory_path in theory_paths:
                #revise_special_notebook(os.path.join(theory_path, '_common_.ipynb'))
                export_notebook_to_html(os.path.join(theory_path, '_common_.ipynb'))
        else:
            # execute the commons notebooks first, and do this twice to work out inter-dependencies
            for _ in range(2):
                for theory_path in theory_paths:
                    #revise_special_notebook(os.path.join(theory_path, '_common_.ipynb'))
                    execute_processor.execute_notebook(os.path.join(theory_path, '_common_.ipynb'), no_latex=no_latex)
            # Unless 'no_latex' is True, execute one last time to 
            # eliminate "expression notebook ... updated" messages 
            # and we'll export to html.
            for theory_path in theory_paths:
                #revise_special_notebook(os.path.join(theory_path, '_common_.ipynb'))
                execute_and_export_notebook(execute_processor, os.path.join(theory_path, '_common_.ipynb'),
                                         no_execute=no_latex, no_latex=no_latex)
                    
        # Next, run _axioms_.ipynb and _theorems_.ipynb notebooks for the theories.
        # The order does not matter assuming these expression constructions
        # do not depend upon other axioms or theorems (but possibly common expressions).
        # Execute twice unless no_latex==True to get rid of extraneous 
        # information about adding/removing from database
        if no_execute:
            for theory_path in theory_paths:
                export_notebook_to_html(os.path.join(theory_path, '_axioms_.ipynb'))
                export_notebook_to_html(os.path.join(theory_path, '_theorems_.ipynb'))    
        else:
            for theory_path in theory_paths:
                #revise_special_notebook(os.path.join(theory_path, '_axioms_.ipynb'))
                #revise_special_notebook(os.path.join(theory_path, '_theorems_.ipynb'))
                execute_processor.execute_notebook(os.path.join(theory_path, '_axioms_.ipynb'), no_latex=no_latex)
                execute_processor.execute_notebook(os.path.join(theory_path, '_theorems_.ipynb'), no_latex=no_latex)    
            # The second time we'll export to html.  Unless 'no_latex'
            # is True, we will execute again to clear extra information.
            for theory_path in theory_paths:
                #revise_special_notebook(os.path.join(theory_path, '_axioms_.ipynb'))
                #revise_special_notebook(os.path.join(theory_path, '_theorems_.ipynb'))
                execute_and_export_notebook(execute_processor, os.path.join(theory_path, '_axioms_.ipynb'),
                                         no_execute=no_latex, no_latex=no_latex)
                execute_and_export_notebook(execute_processor, os.path.join(theory_path, '_theorems_.ipynb'),
                                         no_execute=no_latex, no_latex=no_latex)    
    if not just_execute_expression_nbs and not just_execute_demos:
        # Get the proof notebook filenames for the theorems in all of the 
        # theories.
        # Map proof notebook names to corresponding Theorem objects:
        proof_notebook_theorems = dict() 
        theorem_proof_notebooks = []
        # Turn off automation while loading theorems simply for recording
        # dependencies:
        #proveit.defaults.automation = False
        print("Finding theorem proof notebooks.")
        for theory_path in theory_paths:
            theory = Theory(theory_path)
            for theorem_name in theory.get_theorem_names():
                start_time = time.time()
                print("Loading", theorem_name, end='', flush=True)
                theorem = theory.get_theorem(theorem_name)
                proof_notebook_name = theory.thm_proof_notebook(theorem_name, theorem.proven_truth.expr)
                proof_notebook_theorems[proof_notebook_name] = theorem
                theorem_proof_notebooks.append(proof_notebook_name)
                print("; finished in %0.2f seconds"%(time.time()-start_time))
        # Turn automation back on:
        #proveit.defaults.automation = True
        
        '''
        # Some proveit modules may not have loaded properly while
        # automation was off, so we need to reset and reload it. 
        proveit.reset()
        for k,v in list(sys.modules.items()):
            if k.startswith('proveit'):
                if k=='proveit' or k.startswith('proveit._core_'):
                    # Don't reload proveit or proveit._core_.
                    continue
                print('reload', v)
                importlib.reload(v)
        '''
        
        if no_execute:
            if not just_execute_essentials:
                for proof_notebook in theorem_proof_notebooks:
                    #if not os.path.isfile(proof_notebook[-5:] + '.html'): # temporary
                    export_notebook_to_html(proof_notebook)
        else:
            # Next, for each of the theorems, record the "presuming" information
            # of the proof notebooks in the _proofs_ folder.  Do this before executing
            # any of the proof notebooks to account for dependencies properly
            # (avoiding circular dependencies as intended).
            print("Recording theorem dependencies.")
            for proof_notebook in theorem_proof_notebooks:
                record_presuming_info(proof_notebook_theorems[proof_notebook], proof_notebook)

            if not just_execute_essentials:
                # Next, execute all of the proof notebooks twice
                # to ensure there are no circular logic violations.
                for proof_notebook in theorem_proof_notebooks:
                    execute_processor.execute_notebook(proof_notebook, no_latex=no_latex)
                for proof_notebook in theorem_proof_notebooks:
                    execute_and_export_notebook(execute_processor, proof_notebook,
                                             no_latex=no_latex)
            
    if not just_execute_essentials and not just_execute_expression_nbs and not just_execute_proofs:
        # Next, run any other notebooks within path/theory directories
        # (e.g., with tests and demonstrations).
        for path in all_paths:
            for sub in os.listdir(path):
                full_path = os.path.join(path, sub)
                if os.path.isfile(full_path) and os.path.splitext(full_path)[1] == '.ipynb':
                    if sub == '_demonstrations_.ipynb' or sub[0] != '_':
                        execute_and_export_notebook(execute_processor, full_path, 
                                                 no_execute=no_execute,
                                                 no_latex=no_latex)
                        
    if not just_execute_essentials and not just_execute_proofs and not just_execute_demos:
        # Lastly, run expr.ipynb, proof.ipynb, and dependencies.ipynb within 
        # the hash directories of the __pv_it folders for each theory.
        # May require multiple passes (showing expression info may generate
        # expr.ipynb notebooks for sub-expressions).
        executed_hash_paths = set()  # hash paths whose notebooks have been executed
        while True: # repeat until there are no more new notebooks to process
            prev_num_executed = len(executed_hash_paths)
            for path in all_paths:
                pv_it_dir = os.path.join(path, '__pv_it')
                if os.path.isdir(pv_it_dir):
                    for folder in os.listdir(pv_it_dir):
                        folder_dir = os.path.join(pv_it_dir, folder)
                        if os.path.isdir(folder_dir):
                            for hash_directory in os.listdir(folder_dir):
                                hash_path = os.path.join(folder_dir, hash_directory)
                                if os.path.isdir(hash_path):
                                    if hash_path in executed_hash_paths:
                                        continue # already executed this case
                                    for filebase in ('expr', 'axiom_expr', 'theorem_expr', 'proof'):
                                        html_path = os.path.join(hash_path, filebase+'.html')
                                        notebook_path = os.path.join(hash_path, filebase+'.ipynb')
                                        if os.path.isfile(notebook_path):
                                            if no_execute:
                                                export_notebook_to_html(notebook_path)
                                            else:
                                                # if expr_html doesn't exist or is older than expr_notebook, generate it
                                                if not os.path.isfile(html_path) or os.path.getmtime(html_path) < os.path.getmtime(notebook_path):
                                                    # execute the expr.ipynb notebook
                                                    execute_and_export_notebook(
                                                            execute_processor, 
                                                            notebook_path,
                                                            no_latex=no_latex, git_clear=False)
                                                    executed_hash_paths.add(hash_path) # done
                                    # always execute the dependencies notebook for now to be safes
                                    dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                                    if os.path.isfile(dependencies_notebook):
                                        # execute the dependencies.ipynb notebook
                                        execute_and_export_notebook(
                                                execute_processor, dependencies_notebook, 
                                                no_execute=no_execute, no_latex=no_latex, 
                                                git_clear=False)
            if len(executed_hash_paths) == prev_num_executed:
                break # no more new ones to process

if __name__ == '__main__':
    if os.path.sep != '/':
        # use the appropriate path separator for the OS
        default_paths = [path.replace('/', os.path.sep) for path in default_paths]
        
    # parse the arguments and provide help information.
    parser = argparse.ArgumentParser(description='Build all of the Prove-It notebooks in selected directories.')
    parser.add_argument('--clean', dest='clean', action='store_const',
                        const=True, default=False,
                        help='remove all of the autogenerated __pv_it directories')    
    parser.add_argument('--download', dest='download', action='store_const',
                        const=True, default=False,
                        help='download and extract the tarball of __pv_it directories from http://pyproveit.org')   
    parser.add_argument('--justessential', dest='just_execute_essentials', action='store_const',
                        const=True, default=False,
                        help='only execute _common_, _axioms_ and _theorems_ notebooks')       
    parser.add_argument('--justproofs', dest='just_execute_proofs', action='store_const',
                        const=True, default=False,
                        help='only execute proofs')   
    parser.add_argument('--justdemos', dest='just_execute_demos', action='store_const',
                        const=True, default=False,
                        help='only execute demonstrations')   
    parser.add_argument('--justexpressions', dest='just_execute_expression_nbs', action='store_const',
                        const=True, default=False,
                        help='only execute expression notebooks')   
    parser.add_argument('--nolatex', dest='nolatex', action='store_const',
                        const=True, default=False,
                        help='speed execution by skipping LaTeX generation')   
    parser.add_argument('--noexecute', dest='noexecute', action='store_const',
                        const=True, default=False,
                        help='do not execute notebooks, just convert to HTML')   
    parser.add_argument('path', type=str, nargs='*', default=default_paths,
                        help='paths to be processed; sub-theories will be included recursively (default: %s)'%' '.join(default_paths))
    args = parser.parse_args()    
    paths = args.path
        
    # Get all the theories of the given top-level paths
    # in the order indicated in _sub_theory_.txt files.
    theory_paths = []
    theory_map = dict() # map Theory names to paths
    for path in paths:
        for theory_path in find_theory_paths(path):
            theory_paths.append(theory_path)
            theory_map[Theory(theory_path).name] = theory_path
    
    all_paths = list(theory_paths)
    all_paths += [path for path in paths if path not in theory_paths]

    if args.clean:
        # clean all of the __pv_it directories that may be auto-generated
        print("Cleaning '__pv_it' directories...")
        sys.stdout.flush()
        for path in all_paths:
            pv_it_dir = os.path.join(path, '__pv_it')
            shutil.rmtree(pv_it_dir)
            '''
            # remove files from __pv_it folders except *.png, *.latex kinds.
            for sub in os.listdir(pv_it_dir):
                if sub == '_referenced_':
                    shutil.rmtree(os.path.join(pv_it_dir, '_referenced_'))
                    continue
                sub_path = os.path.join(pv_it_dir, sub)
                if os.path.isdir(sub_path):
                    for _sub in os.listdir(sub_path):
                        if _sub[-4:] == '.png': continue
                        if _sub[-6:] == '.latex': continue
                        else:
                            os.remove(os.path.join(sub_path, _sub))
                else:
                    os.remove(sub_path)
            '''
    elif not args.download:
        # remove the __pv_it/commons.pv_it in all of the theory paths
        # to make sure everything gets updated where there are dependencies
        # between common expressions of different theories.
        for path in theory_paths:
            generate_css_if_missing(path)
            pv_it_dir = os.path.join(path, '__pv_it')
            generate_css_if_missing(pv_it_dir)
            if os.path.isdir(pv_it_dir):
                commons_filename = os.path.join(pv_it_dir, 'commons.pv_it')
                if os.path.isfile(commons_filename):
                    os.remove(commons_filename) 
        with RecyclingExecutePreprocessor(kernel_name='python3', timeout=-1) as execute_processor:
            build(execute_processor, theory_paths, all_paths, args.noexecute, 
                  args.just_execute_essentials, args.just_execute_proofs, 
                  args.just_execute_demos, args.just_execute_expression_nbs,
                  args.nolatex)
    
    if args.download:
        '''
        Download and extract the tarball of __pv_it directories.
        '''
        if not args.clean:
            raise ValueError("The '--download' option is currently only implemented to work in conjunction with the '--clean' option")
        if args.noexecute or args.just_execute_proofs or args.just_execute_demos or args.just_execute_expression_nbs:
            raise ValueError("Do not combine the '--download' option with any other option besides '--clean'")
        url = "http://pyproveit.org/pv_it.tar.gz" # tarball url
        print("Downloading '%s'"%url)
        print("NOTE: If this fails (e.g., due to a firewall), it may be easiest to manually download and extract pv_it.tar.gz in this folder.")
#        file_tmp = urllib.urlretrieve(url, filename=None)[0]#Comment out for Python 3
        file_tmp = urllib.request.urlretrieve(url, filename=None)[0]#Comment in for Python 3
        tar = tarfile.open(file_tmp)
        # extract into the directory of this 'build.py'
        path = os.path.dirname(os.path.realpath(__file__))
        print("Extracting tarball into %s"%path)
        tar.extractall(path)


def mpi_build(notebook_paths, no_latex=False, git_clear=True, no_execute=False, export_to_html=True):
    try:
        from mpi4py import MPI
        comm = MPI.COMM_WORLD
        rank = comm.Get_rank()
        nranks = comm.Get_size()
    except:
        rank, nranks = 0, 1
    
    assert export_to_html or not no_execute, "Nothing to do, in that case??"
    
    # Set of notebooks that should be attempted after prerequisites
    # have been satisfied (e.g., other common expression notebooks):
    retry_notebooks = set()
    # Map notebooks, to be retried, to theory names:
    retry_notebook_to_theory_name = dict()
    # Map notebooks that need to be retried to their original error
    # message:
    retry_orig_err_msg = dict()
    # Map notebooks that need to be retried to the theory whose common
    # expression notebook must be executed first:
    retry_prerequisite = dict()
    # retry_prerequisite values that have not been satisfied:
    unmet_prerequisites = set()
    # ranks that have been assigned to execute a notebook but
    # haven't finished.
    unfinished_ranks = set()
    
    # Inner functions to address retrying notebooks when executing
    # common expression notebooks and one imports from another that
    # hasn't been executed yet.
    def generate_notebook_paths_with_retries():
        # Try all of the notebooks once.
        while True:
            try:
                yield next(notebook_paths)
            except StopIteration:
                break
        # Retry some of the notebooks as needed and/or
        # wait for unfinished notebooks.
        while len(retry_notebooks) > 0 or len(unfinished_ranks) > 0:
            #print(len(retry_notebooks), 'retries', len(unfinished_ranks), 
            #      'unfinished', len(unmet_prerequisites), 'unmet_prerequisites')
            yielded_retry = False
            if len(retry_notebooks) > 0:
                for to_retry in retry_notebooks:
                    retry_theory_name = retry_notebook_to_theory_name[to_retry]
                    prerequisite = retry_prerequisite[retry_theory_name]
                    if prerequisite in unmet_prerequisites:
                        if (prerequisite not in retry_prerequisite.keys() and
                                len(unfinished_ranks)==0):
                            # Unable to satisfy the prerequisite because
                            # it isn't queued up.
                            raise Exception("Error while executing %s\n%s"%(
                                to_retry, retry_orig_err_msg[to_retry]))
                    else:
                        retry_notebooks.remove(to_retry)
                        yield to_retry
                        yielded_retry = True
                        break
            if not yielded_retry:
                # We have to wait for unfinished notebooks.
                yield None
    def should_retry_after_failed_execution(notebook_path, orig_err_msg):
        common_notebook_name = '_common_.ipynb'
        if notebook_path[-len(common_notebook_name):] != common_notebook_name:
            # Only retry for common expression notebooks.
            return False
        theory = Theory(notebook_path)
        import_failure_filename = os.path.join(
                theory._theory_folder_storage('common').path, 
                'import_failure.txt')
        if os.path.isfile(import_failure_filename):
            # There was a failure to import a common expression from
            # a different theory, so we should try again.
            retry_notebooks.add(notebook_path)
            retry_notebook_to_theory_name[notebook_path] = theory.name
            with open(import_failure_filename, 'r') as f:
                failed_import = f.read().strip()
            retry_prerequisite[theory.name] = failed_import
            if (failed_import in retry_prerequisite and
                    retry_prerequisite[failed_import] == theory.name):
                raise Exception("Cyclic dependency between %s and %s common "
                                "expression notebooks detected"%
                                (failed_import, theory.name))
            retry_orig_err_msg[notebook_path] = orig_err_msg
            unmet_prerequisites.add(failed_import)
            return True
        else:
            return False
    count = 0
    def successful_execution_notification(notebook_path):
        nonlocal count
        count += 1
        if len(unmet_prerequisites) > 0:
            theory = Theory(notebook_path)
            unmet_prerequisites.discard(theory.name)
    
    if nranks == 1:
        # The boring single rank case.
        with RecyclingExecutePreprocessor(kernel_name='python3', timeout=-1) as execute_processor: 
            for notebook_path in generate_notebook_paths_with_retries():
                try:
                    execute_and_maybe_export_notebook(
                            execute_processor, notebook_path, no_latex=no_latex, 
                            no_execute=no_execute, git_clear=git_clear,
                            export_to_html=export_to_html)
                    successful_execution_notification(notebook_path)
                except Exception as e:
                    if not should_retry_after_failed_execution(notebook_path, 
                                                               str(e)):
                        raise e
    elif rank > 0:
        # These ranks will request assignments from rank 0
        try:
            with RecyclingExecutePreprocessor(kernel_name='python3', timeout=-1) as execute_processor: 
                comm.send(rank, dest=0)
                while True:
                    notebook_path = comm.recv(source=0)
                    if len(notebook_path)==0:
                        break # empty path is "done" signal
                    try:
                        execute_and_maybe_export_notebook(
                            execute_processor, notebook_path, no_latex=no_latex, 
                            no_execute=no_execute, git_clear=False,
                            export_to_html=export_to_html)
                        comm.send(rank, dest=0)
                    except Exception as e:
                        comm.send((rank, str(e)), dest=0)
        except KernelStartFailure:
            # Occassionally there is an error getting a Jupyter notebook
            # engine started.  If that happens, just this this one out
            # and let the other cores keep going.
            print("Kernel failed to start on rank %d.  Going on without this rank."%rank)
            pass
    else:
        # Send out assignments as they are requested.
        assignments = [None]*nranks # remember the assigments of the ranks.
        def process_response(msg):
            # Checks for an error message in the response from the
            # worker ranks; otherwise, it will be the rank itself.
            try:
                ready_rank = int(msg)
            except TypeError:
                # If we get anything other than an integer,
                # it must be an exception message.
                err_rank = int(msg[0])
                failed_notebook = assignments[err_rank]
                if not should_retry_after_failed_execution(failed_notebook, 
                                                           msg[1]):
                    print("Error while executing %s:"%failed_notebook)
                    print(msg[1])
                    comm.Abort()
                else:
                    print("\tFailure to execute %s, but we may retry "
                          "after satisfying prerequisites"%failed_notebook)
                return err_rank
            finished_notebook = assignments[ready_rank]
            if finished_notebook is not None:
                successful_execution_notification(finished_notebook)
                if git_clear:
                    git_clear_notebook(finished_notebook)
            return ready_rank
        try:
            idle_ranks = set()
            for notebook_path in generate_notebook_paths_with_retries():
                if notebook_path is not None and len(idle_ranks) > 0:
                    # Send the job to a rank that was sitting idle.
                    ready_rank = idle_ranks.pop()
                else:
                    # Wait for a request/response from one of the ranks.
                    ready_rank = process_response(comm.recv(source=MPI.ANY_SOURCE))
                if notebook_path is not None:
                    unfinished_ranks.add(ready_rank)
                    comm.send(notebook_path, ready_rank)
                else:
                    unfinished_ranks.discard(ready_rank)
                    idle_ranks.add(ready_rank)
                assignments[ready_rank] = notebook_path
        except Exception as e:
            print(str(e))
            comm.Abort()
        # And now we are done
        for dest in range(1, nranks):
            comm.send("", dest)
    if rank==0:
        print("Finished executing %d notebooks"%count) 
        
def notebook_path_generator(top_level_paths, notebook_filename):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            yield os.path.join(theory_path, notebook_filename)

def theoremproof_path_generator(top_level_paths):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            theory = Theory(theory_path)
            for theorem_name in theory.get_theorem_names():
                yield os.path.join(theory._storage.directory, '_proofs_', theorem_name, 'thm_proof.ipynb')

def database_notebook_path_generator(top_level_paths, filebases):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            pv_it_dir = os.path.join(theory_path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                for folder in os.listdir(pv_it_dir):
                    folder_dir = os.path.join(pv_it_dir, folder)
                    if os.path.isdir(folder_dir):
                        for hash_directory in os.listdir(folder_dir):
                            hash_path = os.path.join(folder_dir, hash_directory)
                            if os.path.isdir(hash_path):
                                #if hash_path in executed_hash_paths:
                                #    continue # already executed this case
                                for filebase in filebases:
                                    notebook_path = os.path.join(hash_path, filebase+'.ipynb')
                                    if os.path.isfile(notebook_path):
                                        yield notebook_path

                                    """
                                        html_path = os.path.join(hash_path, filebase+'.html')
                                        notebook_path = os.path.join(hash_path, filebase+'.ipynb')
                                        if os.path.isfile(notebook_path):
                                            if no_execute:
                                                export_notebook_to_html(notebook_path)
                                            else:
                                                # if expr_html doesn't exist or is older than expr_notebook, generate it
                                                if not os.path.isfile(html_path) or os.path.getmtime(html_path) < os.path.getmtime(notebook_path):
                                                    # execute the expr.ipynb notebook
                                                    execute_and_export_notebook(
                                                            execute_processor, 
                                                            notebook_path,
                                                            no_latex=no_latex, git_clear=False)
                                                    executed_hash_paths.add(hash_path) # done
                                    # always execute the dependencies notebook for now to be safes
                                    dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                                    if os.path.isfile(dependencies_notebook):
                                        # execute the dependencies.ipynb notebook
                                        execute_and_export_notebook(
                                                execute_processor, dependencies_notebook, 
                                                no_execute=no_execute, no_latex=no_latex, 
                                                git_clear=False)
                                    """

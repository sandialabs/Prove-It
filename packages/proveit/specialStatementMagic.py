import proveit
from proveit.expression import Expression
import os, subprocess
import shutil
import re
import dill
from IPython import get_ipython
from IPython.core.magic import Magics, magics_class, line_magic

@magics_class
class AxiomsOrTheoremsMagics(Magics):
    "Magics that hold additional state"

    def __init__(self, shell):
        # You must call the parent constructor
        super(AxiomsOrTheoremsMagics, self).__init__(shell)
        self.exclusions = None

    def _start(self, statementType):
        if self.exclusions is not None:
            print 'Reboot the IPython notebook Kernal before performing %begin_' + statementType + ' again.'
            print 'Aborting'
            return
        self.exclusions = set(self.shell.user_ns.keys())
        self.statementType = statementType

    def _finish(self, statementType):
        # query for a user input query (input or raw_input depending upon python version):
        try:
            query = raw_input
        except NameError: # Python 3
            query = input
        if self.exclusions is None:
            raise Exception('Must run %begin_' + statementType + ' first')
        if self.statementType != statementType:
            raise Exception('%end_' + statementType + ' does not match %begin_' + self.statementType)
        print 'Creating', self.statementType, '*.dill and *.pv_it files in the __pv_it__ directory'
        # create the __pv_it__/axioms or __pv_it__/axioms directory if it doesn't exist
        dillPath = os.path.join('__pv_it__', self.statementType)
        if not os.path.exists(dillPath):
            os.makedirs(dillPath)
        # create the expressions directory if it doesn't exist
        expressionsDir = os.path.join('__pv_it__', 'expressions')
        if not os.path.exists(expressionsDir):
            os.mkdir(expressionsDir)
        # list of theorem or axiom definitions from the notebook:
        defns = {name:expr for name, expr in self.shell.user_ns.iteritems() if name[0] != '_' and name not in self.exclusions and isinstance(expr, Expression)}
        # see if any of the theorems/axioms are to be removed
        remove_all_extraneous = False
        for fname in os.listdir(dillPath):
            if fname[-6:] == '.pv_it':
                if fname[:-6] not in defns:
                    if remove_all_extraneous == False:
                        # TEMPORARILY MAKE THIS ALWAYS OVERWRITE, FOR CONVENIENCE
                        #response = query(fname[:-6] + ' appears to be obsolete.  Remove it?  (yes/no/all)')
                        response = 'a'                        
                        if response.lower() == 'a' or response.lower() == 'all':
                            remove_all_extraneous = True
                        elif response.lower() != 'y' and response.lower() != 'yes':
                            print "Aborting"
                            return
                    os.remove(os.path.join(dillPath, fname))
                    try:
                        os.remove(os.path.join(dillPath, fname[:-6] + '.dill'))
                    except:
                        pass
        # iterate over the theorems/axioms
        replace_all = False
        for name, expr in defns.iteritems():
            # dump the expression object into the corresponding dill file
            with open(os.path.join(dillPath, name+'.dill'), 'w') as f:
                dill.dump(expr, f)
            expr_id = expr._export_pvit(expressionsDir)
            pvit_file = os.path.join(dillPath, name+'.pv_it')
            if replace_all == False and os.path.exists(pvit_file):
                with open(os.path.join(pvit_file), 'r') as f:
                    changed = (f.read() != (expr_id + '\n'))
                    if changed:
                        # TEMPORARILY MAKE THIS ALWAYS OVERWRITE, FOR CONVENIENCE
                        #response = query(name + ' has changed.  Replace it? (yes/no/all)')
                        response = 'a'
                        if response.lower() == 'a' or response.lower() == 'all':
                            replace_all = True
                        elif response.lower() != 'y' and response.lower() != 'yes':
                            print "Aborting"
                            return
            with open(os.path.join(pvit_file), 'w') as f:
                f.write(expr_id + '\n')
        templateFile = os.path.join(os.path.split(proveit.__file__)[0], '..', 'axiomsOrTheoremsTemplate.py')
        if os.path.exists(statementType + '.py'):                                   
            if open(templateFile).read() != open(statementType + '.py').read():
                print statementType + '.py exists.  This file must be removed manually before replacing it with proveit.axiomsOrTheoremsTemplate.py.'
                print 'Aborting'
                return
        else:
            print 'Generating', (statementType + '.py'), 'from proveit.axiomsOrTheoremsTemplate.py'
            shutil.copyfile(templateFile, statementType + '.py')
        importName = os.path.relpath(os.path.abspath(statementType), os.path.join(os.path.split(proveit.__file__)[0], '..')).replace(os.path.sep, '.')
        print 'These', statementType, 'may be imported from', importName

    @line_magic
    def begin_axioms(self, line):
        self._start('axioms')

    @line_magic
    def end_axioms(self, line):
        self._finish('axioms')

    @line_magic
    def begin_theorems(self, line):
        self._start('theorems')

    @line_magic
    def end_theorems(self, line):
        self._finish('theorems')
        
# This class must then be registered with a manually created instance,
# since its constructor has different arguments from the default:
ip = get_ipython()
specialStatementsMagic = AxiomsOrTheoremsMagics(ip)
ip.register_magics(specialStatementsMagic)

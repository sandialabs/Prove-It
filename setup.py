"""Prove-It: general theorem prover in python"""

from setuptools import setup, find_packages
from nbstripout.install import install_nbstripout
import sys

with open("packages/proveit/_version.py") as f:
    code = compile(f.read(), "packages/proveit/_version.py", 'exec')
    exec(code)

classifiers = """\
Development Status :: 4 - Beta
Intended Audience :: Science/Research
License :: Other/Proprietary License
Programming Language :: Python
Topic :: Scientific/Engineering :: Mathematics
Operating System :: Microsoft :: Windows
Operating System :: MacOS :: MacOS X
Operating System :: Unix
"""

descriptionTxt = """\
Prove-It uses a powerful yet simple approach to theorem-proving.  
It is not designed with automation as the primary goal.  The primary goal is 
flexibility in order to be able to follow, ideally, any valid and complete 
(indivisible) chain of reasoning.  To that end, users can write additional 
Python scripts to make their own mathematical operations and LaTeX formatting 
rules.  Axioms are statements that are taken to be true without proof.  They
can be added by the user at will in order to define their new mathematical 
objects and operations.  Users can also add theorems that are to be proven.  
Theorems may be proven in any order.  Theorem proofs are constructed in 
Jupyter notebooks (interactive Python sessions in a web browser).  These 
notebooks render LaTeX-formatted mathematical expressions inline.  Proofs 
are constructed by invoking axioms and other theorems and employing 
fundamental derivation steps (modus ponens, hypothetical reasoning, 
instantiation, generalization, or axiom elimination).  Axioms and theorems
may be invoked indirectly via convenience methods or automation (methods
that are automatically invoked when attempting to prove something or
side-effects when something is proven).  Theorem proofs and their axiom/
theorem dependencies are stored a kind of database (filesystem based).  This
database is used to prevent circular logic.
"""

dist = setup(name='Prove-It',
      version=__version__,
      description='General theorem prover in python.',
      long_description=descriptionTxt,
      author='Wayne Witzel, Kenneth Ruddinger, Mohan Sarover, Robert Carr',
      author_email='wwitzel@sandia.gov',
      packages=['proveit'],
      package_data={}, # when 'export' is implemented for the certification database, put the exported data here
      package_dir={'': 'packages'},
      requires=[],
      platforms = ["any"],      
      classifiers = [_f for _f in classifiers.split("\n") if _f],
     )

if "develop" in sys.argv:
    print("\nConfiguring git locally to filter jupyter notebook 'output' so only 'input' changes will be tracked.")
    install_nbstripout(['git', 'config'])

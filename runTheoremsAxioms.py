#Run this script from 'proveit root directory

import os

listOfFiles = [
               'proveit/basiclogic/axioms.ipynb',
               'proveit/basiclogic/boolean/axioms.ipynb',
               'proveit/basiclogic/boolean/theorems.ipynb',
               'proveit/basiclogic/equality/axioms.ipynb',
               'proveit/basiclogic/equality/theorems.ipynb',
               'proveit/basiclogic/set/axioms.ipynb',
               'proveit/basiclogic/set/theorems.ipynb',

               'proveit/number/axioms.ipynb',
               'proveit/number/theorems.ipynb',
               'proveit/number/complex/theorems.ipynb',
               'proveit/number/integer/theorems.ipynb',
               'proveit/number/natural/theorems.ipynb',
               'proveit/number/real/theorems.ipynb',

               'proveit/physics/quantum/QPE/axioms.ipynb',
               'proveit/physics/quantum/QPE/theorems.ipynb'
               ]

for fileName in listOfFiles:
    os.system('ipython2-2.7 nbconvert --execute '+fileName)
#    os.system('ipython nbconvert --execute '+fileName)#If you're not Kenny, you probably want this line instead of the previous one.

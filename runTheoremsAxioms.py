#Run this script from 'proveit root directory

import os

cwd = os.getcwd()

listOfFolders = [
               'proveit/basiclogic',
               'proveit/basiclogic/boolean',                              
               'proveit/basiclogic/equality/',
               'proveit/basiclogic/set/',

               'proveit/number/',
               'proveit/number/complex/',
               'proveit/number/integer/',
               'proveit/number/natural/',
               'proveit/number/real/',

               'proveit/physics/quantum/QPE/'
               ]

for folderName in listOfFolders:
    os.chdir(cwd+'/'+folderName)
    print folderName
    if 'axioms.ipynb' in os.listdir('.'):    
        os.system('ipython2-2.7 nbconvert --execute axioms.ipynb')
#    os.system('ipython nbconvert --execute '+fileName)#If you're not Kenny, you probably want this line instead of the previous one.
    if 'theorems.ipynb' in os.listdir('.'):    
        os.system('ipython2-2.7 nbconvert --execute theorems.ipynb')
#    os.system('ipython nbconvert --execute '+fileName)#If you're not Kenny, you probably want this line instead of the previous one.

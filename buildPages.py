import os
from basiclogic import *
from HypertextGenerator import *
import sys
import os

htmlGen = HypertextGenerator()
print "\n"

for f in os.listdir('basiclogic'):
    if f[-2:] == 'py' and not f[0] == '_':
        name = f[:-3]
        if name in locals() and isinstance(locals()[name], Context):
            context = locals()[name]
            htmlGen.makeContextPage(context)
            thmsDir = os.path.join('basiclogic', '_'+name+'_')
            for thmFile in os.listdir(thmsDir):
                if thmFile[-2:] == 'py':
                    os.system('python ' + os.path.join(thmsDir, thmFile))

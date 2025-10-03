# Move thm_proof.ipynb files to _thm_proof.ipynb so they are slightly
# hidden.

import os

for root, _, files in os.walk('.'):
    for file in files:
        if file == 'thm_proof.ipynb':
            os.system("git mv %s %s"%(os.path.join(root, file),
                                      os.path.join(root, '_thm_proof.ipynb')))


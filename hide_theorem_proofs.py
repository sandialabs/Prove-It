# Move thm_proof.ipynb files to _thm_proof.ipynb so they are slightly
# hidden.

import os
import proveit
from proveit import Theory
from game_data import GameData
proveit_path = os.path.split(proveit.__file__)[0]
theory = Theory(proveit_path)
game_data = GameData()
game_data_path =os.path.join(proveit_path, '..', '..')
game_data.update_original_proof_info(game_data_path)

for name, kind in game_data.all_theorem_name_and_kind_to_prove:
    if kind == 'definition_existence':
        stmt = Theory.find_definition_existence(name)
    elif kind == 'definition_extensions':
        stmt = Theory.find_definition_extension(name)
    else:
        stmt = Theory.find_theorem(name)
    root, file = os.path.split(stmt.get_link())
    hidden_file = os.path.join(root, '_thm_proof.ipynb')
    if not os.path.isfile(hidden_file):
        os.system("git mv %s %s"%(os.path.join(root, file),
                                  hidden_file))
    else:
        os.system("mv %s %s"%(os.path.join(root, file),
                              hidden_file))
        os.system("git add %s"%hidden_file)


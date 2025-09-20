'''
Interface into the data for "gamified" Prove-It.  Specifally, information
about all fully proven theorems with the goal of the game to regenerate
these proofs with a preference to use few direct @prover method calls.
'''

import sys
import proveit
from proveit import Theory

class GameData:
    def __init__(self, theory):
        self.theory = theory
        self.all_theorem_name_and_kind_to_prove = []
        self.all_used_thm_indices = []
        self.all_original_direct_prover_calls = []
        self.all_original_proof_steps = []
        self.name_and_kind_to_idx = dict()
        
        # Load information about the original proofs
        data_file = open('game_data_file.txt', 'w')
        for line in data_file:
            split = line.split(' ')
            direct_prover_calls, proof_steps, kind, full_thm_name = split[:4]
            direct_prover_calls = int(direct_prover_calls.strip('(,'))
            proof_steps = int(proof_steps.strip(')'))
            used_thm_indices = tuple(int(_.strip('[,]')) for _ in split[4:])
            idx = len(self.all_theorem_name_and_kind_to_prove)
            self.all_used_thm_indices.append(set(used_thm_indices))
            self.all_theorem_name_and_kind_to_prove.append((full_thm_name, kind))
            self.all_original_direct_prover_calls.append(direct_prover_calls)
            self.all_original_proofs_steps.append(proof_steps)
            self.name_and_kind_to_idx[(full_thm_name, kind)] = idx
        
        num_theorems_to_prove = len(self.all_theorem_name_and_kind_to_prove)
        self.all_used_by_thm_indices = [[] for _ in range(num_theorems_to_prove)]
        for _user_idx, used_thm_indices in enumerate(self.all_used_thm_indices):
            for _used_idx in used_thm_indices:
                self.all_used_by_thm_indices[_used_idx].append(_user_idx)
        
        # Populate information about the player's proofs
        proven_theorem_name_and_kinds = extract_proven_theorem_name_and_kinds(
            theory)
        ready_to_prove = []
        for full_thm_name, kind in proven_theorem_name_and_kinds:
            idx = self.name_and_kind_to_idx[(full_thm_name, kind)]
            for _user_idx in self.all_used_by_thm_indices[idx]:
                self.all_used_thm_indices[_user_idx].remove(idx)
                if len(self.all_used_thm_indices) == 0:
                    # This theorem is ready to prove -- its dependencies
                    # are proven.
                    ready_to_prove.append(
                        self.all_theorem_name_and_kind_to_prove[_user_idx])
            stored_theorem = extract_stored_theorem(theory, full_thm_name, kind)
            proof_counts = stored_theorem.get_proof_counts()
        
        self.reproven_direct_prover_calls = dict()
        self.reproven_proof_steps = dict()


def extract_proven_theorem_name_and_kinds(theory):
    proven_definition_existences = []
    proven_definition_extensions = []
    proven_theorems = []
    for sub_theory in theory.generate_all_contained_theories():
        for def_prop_name in sub_theory.get_defining_property_names():
            full_thm_name = sub_theory.name+'.'+def_prop_name
            try:
                stored_def_existence = Theory.get_stored_definition_existence(
                    full_thm_name)
                if stored_def_existence.is_complete():
                    proven_definition_existences.append(full_thm_name)
            except KeyError:
                pass
            try:
                stored_def_extension = Theory.get_stored_definition_extension(
                    full_thm_name)
                if stored_def_extension.is_complete():
                    proven_definition_extensions.append(full_thm_name)
            except KeyError:
                pass            
        for theorem_name in sub_theory.get_theorem_names():
            full_thm_name = sub_theory.name+'.'+theorem_name
            stored_theorem = Theory.get_stored_theorem(full_thm_name)
            if stored_theorem.is_complete():
                proven_theorems.append(full_thm_name)

    proven_theorem_name_and_kinds = []
    
    for full_thm_names, kind in ((proven_definition_existences, 'def_existence'),
                                 (proven_definition_extensions, 'def_extension'),
                                 (proven_theorems, 'theorem')):
        for full_thm_name in full_thm_names:
            proven_theorem_name_and_kinds.append((full_thm_name, kind))
    
    return proven_theorem_name_and_kinds

def extract_stored_theorem(theory, full_thm_name, kind):
    if kind == 'def_existence':
        return Theory.get_stored_definition_existence(full_thm_name)
    elif kind == 'def_extension':
        return Theory.get_stored_definition_extension(full_thm_name)
    else:
        return Theory.get_stored_theorem(full_thm_name)
    
def generate_data_file(theory):
    name_and_kind_to_idx = dict()
    proven_theorem_name_and_kinds = extract_proven_theorem_name_and_kinds(theory)
    for idx, (full_thm_name, kind) in enumerate(proven_theorem_name_and_kinds):
        name_and_kind_to_idx[(full_thm_name, kind)] = idx
    
    data_file = open('game_data_file.txt', 'w')

    for full_thm_name, kind in proven_theorem_name_and_kinds:
        stored_theorem = extract_stored_theorem(theory, full_thm_name, kind)
        proof_counts = stored_theorem.get_proof_counts()
        used_thm_indices = []
        for used_def_prop in stored_theorem.read_used_defining_properties():
            if (used_def_prop, 'def_existence') in name_and_kind_to_idx:
                used_thm_indices.append(
                    name_and_kind_to_idx[(used_def_prop, 'def_existence')])
            if (used_def_prop, 'def_extension') in name_and_kind_to_idx:
                used_thm_indices.append(
                    name_and_kind_to_idx[(used_def_prop, 'def_extension')])
        for used_thm in stored_theorem.read_used_theorems():
            if (used_thm, 'theorem') in name_and_kind_to_idx:
                used_thm_indices.append(name_and_kind_to_idx[(used_thm, 'theorem')])

        data_file.write('%s %s %s %s\n'%(proof_counts, kind, full_thm_name,
                                         used_thm_indices))
        
    data_file.close()

if __name__ == '__main__':
    path = sys.argv[1]
    theory = Theory(path)
    proveit.defaults.automation = False
    generate_data_file(theory)
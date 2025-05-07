import numpy as np
import dd.autoref as _bdd


class SymbolicModel:

    def __init__(self, num_states: int, valuations, valuation_names, programs, program_names):
        
        self.num_states = num_states
        self.bdd = _bdd.BDD()
        self.bdd.configure(reordering=True)

        # generate empty BDDs for states
        self.states = [self.bdd.true for _ in range(self.num_states)]
        self.current_prop_number = 0
        self.programs = {}
        

        for valuation, name in zip(valuations, valuation_names):
            self.add_valuation(valuation, name)

        self.make_states_unique()
        
        self.primed_name_map = {var: var + "'" for var in self.bdd.vars}
        for v in self.primed_name_map.values():
            self.bdd.declare(v)
        

        for program, name in zip(programs, program_names):
            self.add_program(program, name)

    def create_new_prop(self, name=None):
        if name:
            current_prop_name = name
        else:
            current_prop_name = f'x{self.current_prop_number}'

        self.bdd.declare(current_prop_name)
        self.current_prop_number += 1
        return self.bdd.var(current_prop_name)

    def check_uniqueness(self):
        for i in range(len(self.states)):
                for j in range(len(self.states)):
                    if self.states[i] == self.states[j] and i != j:
                        print(f"{i} is equal to {j}")

    def add_valuation(self, valuations: list, name=None):
        if len(valuations) != self.num_states:
            raise ValueError('Different number of valuations than states')
        
        new_prop = self.create_new_prop(name)
        # per state add the corresponding valuation of a single proposition
        for i, valuation in enumerate(valuations):
            if valuation == 1:
                self.states[i] &= new_prop
            elif valuation == 0:
                self.states[i] &= ~new_prop
        

    def add_program(self, program, program_name):
        if len(program[0]) != self.num_states:
            raise ValueError('Different number of states in program than known')
        
        if program_name in self.programs.keys():
            raise ValueError(f"The program name '{program_name}' is used at least twice, while program names should be unique")
        
        # find the source and target state couples as indices
        base_state_indices, target_state_indices = np.where(program == 1)
        
        program_bdd = self.bdd.false
        
        for base_state_index, target_state_index in zip(base_state_indices, target_state_indices):
            base_state = self.states[base_state_index]
            target_state_primed = self.bdd.let(self.primed_name_map, self.states[target_state_index])

            transition = base_state & target_state_primed
            program_bdd = program_bdd | transition

        # merge all seperate relation formulas in one final formula string
        self.programs[program_name] = program_bdd

    def unique_duplicate_index(self):
        seen_once = set()
        indices = set()

        # save the indices of every second duplicate
        for index, state in enumerate(self.states):
            if state in seen_once:
                indices.add(index)
                seen_once.remove(state)
            else:
                seen_once.add(state)
        
        return indices
    
    def make_states_unique(self):
        duplicate_indices = self.unique_duplicate_index()

        while duplicate_indices:
            # to seperate, add new property that's true for all second duplicates and
            # false for others
            new_prop = self.create_new_prop()

            for index, state in enumerate(self.states):
                if index in duplicate_indices:
                    self.states[index] &= new_prop
                else:
                    self.states[index] &= ~new_prop
      
            duplicate_indices = self.unique_duplicate_index()

    def __str__(self):

        return_string = f'Number of states \n {self.num_states} \n \n Valuations'

        for i, state in enumerate(self.states):
            return_string += f' \n{i}:\n {state.to_expr()}'

        return_string += '\n\nProgram:\n'

        for key, value in self.programs.items():
            return_string += f'{key}:\n {value.to_expr()}\n'

        return return_string
    

def SymbolicModelFromFile(file: str):
    components = ['STATES', 'PROPS', 'PROGS', 'TESTS']
    mode = None
    num_states = 0
    valuations = []
    valuation_names = []
    programs = []
    program_names = []
    
    with open(file, 'r') as f:
        line = f.readline()
        while line:
            if len(line.split()) == 0:
                line = f.readline()
            elif line.strip() in components:
                mode = line.strip()
                line = f.readline()
            elif mode == 'STATES':
                num_states = int(line.strip())
                mode = None
                line = f.readline()
            elif mode == 'PROPS':
                if len(line.split()) == 1:
                    valuation_names.append(line.strip())
                    line = f.readline()
                    valuations.append([int(x) for x in line.split()])
                line = f.readline()
            elif mode == 'PROGS':
                if len(line.split()) == 1:
                    program_names.append(line.strip())
                    line = f.readline()
                    
                    programs.append(np.array([[int(x) for x in line.split()]]))
                    for _ in range(len(programs[-1][0])-1):
                        line = f.readline()
                        programs[-1] = np.vstack([programs[-1], [int(x) for x in line.split()]])

                line = f.readline()
            elif mode == 'TESTS':
                line = f.readline()
            else:
                line = f.readline()

    return SymbolicModel(num_states, valuations, valuation_names, programs, program_names)

test = SymbolicModelFromFile('small_kripke.txt')
print(test)


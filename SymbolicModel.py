import numpy as np
import dd.autoref as _bdd
from typing import Optional

class SymbolicModel:
    def __init__(self, num_states: int, valuations: list[list[int]], valuation_names: list[str],
                                        programs: list[np.ndarray], program_names: list[str]):
        
        self._num_states = num_states

        self.bdd = _bdd.BDD()
        self.bdd.configure(reordering=True)

        # generate empty BDDs for states
        self.states = [self.bdd.true for _ in range(self._num_states)]
        self.programs = {}

        for valuation, name in zip(valuations, valuation_names):
            self.add_valuation(valuation, name)

        self._current_prop_number = 0
        

        self.make_states_unique()

        self.law = self.add_law()
        
        for program, name in zip(programs, program_names):
            self.add_program(program, name)

        from Parser import PDLTransformer 
        self.transformer = PDLTransformer(self)
        
        del self.states



    def add_primes(self, expression):
        primed_name_map = {var: var + "'" for var in self.bdd.support(expression)}
        for v in primed_name_map.values():
            self.bdd.declare(v)
        return self.bdd.let(primed_name_map, expression)
    
    def add_temporary(self, expression, for_primed):
        remapping = {}
        for var in self.bdd.support(expression):
            if var.endswith("'") and for_primed:
                remapping[var] = var[:-1] + 'T'
            elif not var.endswith("'") and not for_primed:
                remapping[var] = var + 'T'

        for temp_var in remapping.values():
            self.bdd.declare(temp_var)

        return self.bdd.let(remapping, expression)
        

    def create_new_prop(self, name: Optional[str]=None) -> _bdd.Function:
        if name:
            current_prop_name = name
        else:
            current_prop_name = f'x{self._current_prop_number}'
            self._current_prop_number += 1

        self.bdd.declare(current_prop_name)
        return self.bdd.var(current_prop_name)

    def every_second_duplicate_index(self) -> list[int]:
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
    
    def make_states_unique(self) -> None:
        duplicate_indices = self.every_second_duplicate_index()

        while duplicate_indices:
            # to seperate, add new property that's true for all second duplicates and
            # false for others
            new_prop = self.create_new_prop()
            
            for index, state in enumerate(self.states):
                if index in duplicate_indices:
                    self.states[index] &= new_prop
                else:
                    self.states[index] &= ~new_prop
      
            duplicate_indices = self.every_second_duplicate_index()

    def add_valuation(self, valuations: list, name=None):
        if len(valuations) != self._num_states:
            raise ValueError('Different number of valuations than states')
        
        new_prop = self.create_new_prop(name)
        # per state add the corresponding valuation of a single proposition
        for i, valuation in enumerate(valuations):
            if valuation == 1:
                self.states[i] &= new_prop
            else:
                self.states[i] &= ~new_prop


    def add_law(self):
        result = self.bdd.false
        for state in self.states:
            result = result | state
        return result
        
    def add_program(self, program, program_name):
        if len(program[0]) != self._num_states:
            raise ValueError('Different number of states in program than known')
        
        if program_name in self.programs.keys():
            raise ValueError(f"The program name '{program_name}' is used at least twice, while program names should be unique")

        # find the source and target state couples as indices
        base_state_indices, target_state_indices = np.where(program == 1)
        
        program_bdd = self.bdd.false
        
        for base_state_index, target_state_index in zip(base_state_indices, target_state_indices):
            base_state = self.states[base_state_index]
            target_state_primed = self.add_primes(self.states[target_state_index])

            transition = base_state & target_state_primed
            program_bdd = program_bdd | transition

        # merge all seperate relation formulas in one final formula string
        self.programs[program_name] = program_bdd

    def check(self, test, state_valuation):
        
        states_where_true = self.transformer.expression_transformer(test)
        if state_valuation is None:
            return self.bdd.to_expr(states_where_true)
        
        state_valuation_bdd = self.bdd.add_expr(state_valuation)
        if state_valuation_bdd.implies(self.law) == self.bdd.true:
            return state_valuation_bdd.implies(states_where_true)  == self.bdd.true
        else:
            raise ValueError('State not found in model')
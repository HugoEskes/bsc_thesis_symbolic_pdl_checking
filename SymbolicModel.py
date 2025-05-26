import numpy as np
import dd.autoref as _bdd
from typing import Optional, Union

BDD = _bdd.Function

class SymbolicModel:
    def __init__(self, num_states: int, valuations: list[list[int]], proposition_names: list[str],
                                        programs: list[np.ndarray], program_names: list[str]):
        """Creates a symbolically represented kripke model.

        Contains
        - a symbolic law, which is a boolean expression containing all valid states (to save
          memory, the individual states are not stored after construction)
        - a list of symbolically represented programs with their names
        - a transformer, which can parse PDL strings to trees and transform those trees to an
          evaluation, based on the current model

        Args:
            num_states (int): Number of states in the model
            valuations (list[list[int]]): List of valuation list of propositions. Length of the 
            outer list is the amount of propositions, length of inner list must match the number of
            states. 
            proposition_names (list[str]): Names of the propositions as matched to the valuations list.
            programs (list[np.ndarray]): List of programs in explicit matrix notation. 
            program_names (list[str]): List of program names as matched to the programs list.
        """        
        
        self._num_states = num_states

        self.bdd = _bdd.BDD()
        self.bdd.configure(reordering=True)

        # generate empty BDDs for states
        self.states = [self.bdd.true for _ in range(self._num_states)]
        self.programs = {}

        for valuation, proposistion_name in zip(valuations, proposition_names):
            self.add_valuation(valuation, proposistion_name)

        self._current_prop_number = 0

        self.make_states_unique()

        self.law = self.construct_law_expression()
        
        for program, name in zip(programs, program_names):
            self.add_program(program, name)

        from Parser import PDLTransformer 
        self.transformer = PDLTransformer(self)
        
        del self.states

    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_value, traceback):
        self._release_bdd_references()

    def _release_bdd_references(self):
        self.law = None
        for program in self.programs:
            program = None
        self.bdd = None
        self.transformer = None    

    def add_primes(self, expression: BDD) -> BDD:
        """Add primes to all variables from an expression

        Args:
            expression (BDD): a boolean expression 

        Returns:
            BDD: the same expression with primes added to the variables
        """        
        primed_name_map = {var: var + "'" for var in self.bdd.support(expression)}
        for v in primed_name_map.values():
            self.bdd.declare(v)
        return self.bdd.let(primed_name_map, expression)
    
    def add_temporary(self, expression: BDD, is_primed: bool) -> BDD:
        """Adds temporary suffix 'T' to all variables in the expression.

        if is_primed is True all primes in variable names are replaced with Ts ("x'" -> "xT"), if 
        is_primed is False there is just a T added ("x" -> "xT")

        Args:
            expression (BDD): boolean expression
            is_primed (bool): indicator if the expression contains primed variables

        Returns:
            BDD: same boolean expression as input with T suffix added
        """        
        remapping = {}
        for var in self.bdd.support(expression):
            if var.endswith("'") and is_primed:
                remapping[var] = var[:-1] + 'T'
            elif not var.endswith("'") and not is_primed:
                remapping[var] = var + 'T'

        for temp_var in remapping.values():
            self.bdd.declare(temp_var)

        return self.bdd.let(remapping, expression)
        

    def create_new_prop(self, name: Optional[str]= None) -> BDD:
        """Creates a new proposition variable in the model.

        Uses the provided name, if no name is provided the name format x# is used. For instance x2
        is used for the third unnamed proposition.

        Args:
            name (Optional[str]): Name for the proposition, if left out format "x#" is used.

        Returns:
            BDD: The new proposition as a variable

        """        
        if name:
            current_prop_name = name
        else:
            current_prop_name = f'x{self._current_prop_number}'
            self._current_prop_number += 1

        self.bdd.declare(current_prop_name)
        return self.bdd.var(current_prop_name)

    def get_even_occurrence_indices(self) -> set[int]:
        """Finds every even-numbered occurrence of a state in the model.

        For example if a state appears five times in the model, the indices of the second and 
        fourth occurrence are returned

        Returns:
            set[int]: Set of the indices of every second occurrence of a state in the model

        """        
        seen_once = set()
        indices = set()

        for index, state in enumerate(self.states):
            if state in seen_once:
                indices.add(index)
                seen_once.remove(state)
            else:
                seen_once.add(state)
        
        return indices
    
    def make_states_unique(self) -> None:
        """Makes all the states in the model unique by continuously adding new variables that are 
        made true for every second occurrence of a state and false for all other states. This is 
        done until there are no duplicate states left in the model. Uses get_even_occurrence_indices()
        to find all even-numbered occurrences of a state.
        """        
        duplicate_indices = self.get_even_occurrence_indices()

        while duplicate_indices:
            new_prop = self.create_new_prop()
            
            for index, state in enumerate(self.states):
                if index in duplicate_indices:
                    self.states[index] &= new_prop
                else:
                    self.states[index] &= ~new_prop
      
            duplicate_indices = self.get_even_occurrence_indices()

    def add_valuation(self, valuations: list[int], proposition_name: str = None) -> None:
        """Adds a new proposition to all states based on the provided valuations.

        Each state in the model is updated with a new proposition that is set to True
        or False according to the corresponding value in `valuations`, where 1 means True
        and 0 means False. The order of valuations must match the order of states.

        Args:
            valuations (list[int]): List with 0s and 1s representing the valuations of the states.
            Must be as long as the number of states in the model. 
            proposition_name (str, optional): An optional name for the proposition. If no name is
            provided the proposition will be named according to the 'x#' format. Defaults to None.

        Raises:
            ValueError: If the number of valuations doesn't match up with the number of states 
            in the model
        """       
        if len(valuations) != self._num_states:
            raise ValueError('Different number of valuations than states')
        
        new_prop = self.create_new_prop(proposition_name)
        for i, valuation in enumerate(valuations):
            if valuation == 1:
                self.states[i] &= new_prop
            else:
                self.states[i] &= ~new_prop


    def construct_law_expression(self) -> BDD:
        """Constructs a law expression which is a Boolean expression representing all possible 
        states in the model

        Returns:
            BDD: A Boolean expression representing the union of all states.
        """        
        result = self.bdd.false
        for state in self.states:
            result = result | state
        return result
        
    def add_program(self, program: np.ndarray, program_name: str) -> None:
        """ Adds the explicit program as a symbolic program to the model.

        The explicit program is represented by a matrix of 0s and 1s, where the ones indicate a 
        transition from the state with the x index to the state with the y index.
        
        A symbolic program is a boolean expression which is the disjunction of all transitions 
        in the program. A transition is a conjunction of the valuations of the base state and the 
        primed valuations of the target state.

        Args:
            program (np.ndarray): The program as represented in a matrix of 0s and 1s. Size of the 
            matrix must match the number of states in the model
            program_name (str): The name of the program. The name must be unique.

        Raises:
            ValueError: Program contains a different number of states than the model.
            ValueError: The provided program name is not unique
        """              
        if program.shape != (self._num_states, self._num_states):
            raise ValueError("Number of states in the program and in the model don't match")
        
        if program_name in self.programs:
            raise ValueError(f"The program name '{program_name}' is used at least twice, while program names should be unique")

        # find the source and target state couples as indices
        base_state_indices, target_state_indices = np.where(program == 1)
        
        program_bdd = self.bdd.false
        
        for base_state_index, target_state_index in zip(base_state_indices, target_state_indices):
            base_state = self.states[base_state_index]
            target_state_primed = self.add_primes(self.states[target_state_index])

            transition = base_state & target_state_primed
            program_bdd = program_bdd | transition

        self.programs[program_name] = program_bdd

    def check(self, PDL_expression: str, state_valuation: Optional[str]=None) -> Union[bool, str]:
        """Evaluates a PDL expression within the Kripke model. If a state is provided gives the 
        evaluation of the PDL expression for that state.

        Args:
            PDL_expression (str): A PDL formula in ---TODO--- style.
            state_valuation (Optional[str], optional): A Boolean expression describing the valuation
            of a specific state. The state must exist in the model. Defaults to None.

        Raises:
            ValueError: State doesn't exist in the model.

        Returns:
            Union[bool, str]: 
                - If a state is provided: a Boolean for the evaluation of the PDL expression in that
                  state. 
                - If no state is provided: the boolean expression describing the evaluation of the
                  PDL expression in the model.
        """        
        
        states_where_true = self.transformer.evaluate_expression(PDL_expression)

        if state_valuation is None:
            return self.bdd.to_expr(states_where_true)
        
        state_valuation_bdd = self.bdd.add_expr(state_valuation)
        if state_valuation_bdd.implies(self.law) == self.bdd.true:
            return state_valuation_bdd.implies(states_where_true)  == self.bdd.true
        else:
            raise ValueError('State not found in model')
        
    def clear(self):
        """Cleans up the BDD manager by clearing all internal references and memory."""
        self.bdd.clear()
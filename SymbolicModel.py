import numpy as np
import dd.cudd as cudd
from time import time
from typing import Optional, Union
from SymbolicInputToModel import SymbolicModelFromSymbolic
import random

BDD = cudd.BDD

class SymbolicModel:
    def __init__(self, bdd, variables: list[str], law: cudd.BDD, programs: dict[str, cudd.BDD]):
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

        self.bdd = bdd
        self.variables = variables

        self.law = law

        self.programs = programs

        for program_name, program in self.programs.items():
            self.programs[program_name] = cudd.restrict(program, self.law)

        from Parser import PDLTransformer 
        self.transformer = PDLTransformer(self)

    @classmethod
    def from_file(cls, file_name: str) -> "SymbolicModel":
        bdd, variables, law, programs = SymbolicModelFromSymbolic(file_name)
        return cls(bdd, variables, law, programs) 
    
    @classmethod
    def random(cls, num_states:int, num_variables: int, num_programs: int, num_transitions: Optional[int] =None) -> "SymbolicModel":
        bdd = cudd.BDD()

        def random_expr(bdd, variables: list[str]):
            if len(variables) == 1:
                return bdd.add_expr(variables[0]) if random.choice([True, False]) else ~bdd.add_expr(variables[0])
            
            
            split_index = random.randint(1, len(variables) - 1)
            left_vars = variables[:split_index]
            right_vars = variables[split_index:]
            
            operator = random.choice(['&', '|'])
            left = random_expr(bdd, left_vars)
            right = random_expr(bdd, right_vars)

            return bdd.apply(operator, left, right)
        
        def random_valid_expr(bdd, variables, law):
            expression = random_expr(bdd, variables)
            while (~expression & law) == bdd.true:
                expression = random_expr(bdd, variables)
            return expression
        
        variables = ['x'+str(i) for i in range(num_variables)]
        targets = ['x'+str(i)+"'" for i in range(num_variables)]

        for variable in variables:
            bdd.declare(variable)

        for target in targets:
            bdd.declare(target)

        law = random_expr(bdd, variables)
        primed_name_map = dict(zip(variables, targets))
        law_primed = bdd.let(primed_name_map, law)
        

        if num_transitions == None:
            num_transitions = random.choice(range(1, num_variables))


        programs_set = set()
        final_programs = {}
        i = 0
        while len(programs_set) < num_programs:
            transitions = set()
            while len(transitions) < num_transitions:
                base_state = random_valid_expr(bdd, variables, law)
                target_state = random_valid_expr(bdd, targets, law_primed)
                transitions.add(bdd.apply('&', base_state, target_state))
            program = bdd.false
            for transition in transitions:
                program |= transition
            if program.node not in programs_set:
                programs_set.add(program)
                final_programs[f'prog{i}'] = program
                i += 1

        return cls(bdd, variables, law, final_programs)

    def __enter__(self):
        return self
    
    def __exit__(self, exc_type, exc_value, traceback):
        self._release_bdd_references()

    def _release_bdd_references(self):
        self.law = None
        self.programs.clear()
        self.bdd = None
        self.transformer = None    

    def _add_primes(self, expression: BDD) -> BDD:
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
    
    def _add_temporary(self, expression: BDD, is_primed: bool) -> BDD:
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
        

    def check(self, PDL_expression: str, state_valuation: Optional[str]=None, print_bdd_filename: Optional[str]=None) -> Union[bool, tuple[list[int], str]]:
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

        if state_valuation:
            state_valuation_bdd = self.bdd.add_expr(state_valuation)
            if state_valuation_bdd.implies(self.law) == self.bdd.true:
                return state_valuation_bdd.implies(states_where_true) == self.bdd.true
            else:
                raise ValueError('State not found in model')
        
        elif print_bdd_filename:
            self.bdd.dump(print_bdd_filename, roots=[states_where_true])
        
        
    def file_tests(self) -> None:
        return self.tests
    
    def program_names_listed(self) -> str:
        full_result = ', '.join(self.programs.keys())
        if len(full_result) > 40:
            return full_result[:40] + '...'
        return full_result

    def prop_names_listed(self) -> str:
        full_result = ', '.join(self.variables)
        if len(full_result) > 40:
            return full_result[:40] + '...'
        return full_result
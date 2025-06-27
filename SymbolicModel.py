import numpy as np
import dd.cudd as cudd
from typing import Optional, Union
from SymbolicInputToModel import SymbolicModelFromSymbolic
import random

BDD = cudd.BDD

class SymbolicModel:
    def __init__(self, bdd, variables: list[str], law: cudd.BDD, programs: dict[str, cudd.BDD], tests: list[str]):
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
        self.tests = tests

        self.programs = programs

        for program_name, program in self.programs.items():
            self.programs[program_name] = cudd.restrict(program, self.law)

        from Parser import PDLTransformer 
        self.transformer = PDLTransformer(self)

    @classmethod
    def from_file(cls, file_name: str) -> "SymbolicModel":
        bdd, variables, law, programs, tests = SymbolicModelFromSymbolic(file_name)
        return cls(bdd, variables, law, programs, tests) 

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
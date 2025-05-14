import numpy as np
import dd.autoref as _bdd
from lark import Lark, Token, Transformer

class PDLTransformer(Transformer):
    def __init__(self, model):
        self.model = model
        self.bdd = model.bdd
        self.identity = self.find_identity()
        

    def formula(self, items):
        name = str(items[0])
        return self.bdd.var(name)
    
    def formula_symbol(self, items):
        name = str(items[0])
        if name not in self.bdd.vars:
            raise ValueError(f"Expected formula symbol, got unknown: {name}")
        return self.bdd.var(name)

    def program_symbol(self, items):
        name = str(items[0])
        if name not in self.model.programs.keys():
            raise ValueError(f"Expected program symbol, got unknown: {name}")
        return self.model.programs[name]

    def not_(self, items):
        return ~items[1]
    
    def test(self, items):
        return self.identity & items[1]

    def and_(self, items):
        return items[0] & items[2]

    def or_(self, items):
        return items[0] | items[2]

    def implies(self, items):
        return ~items[0] | items[2]

    def equiv(self, items):
        return ~(items[0] ^ items[2])

    def diamond(self, items):
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.bdd.support(prog) if s.endswith("'")])

        return self.bdd.exist(primed_variables, prog & self.model.add_primes(formula))

    def box(self, items):
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.bdd.support(prog) if s.endswith("'")])
        
        return self.bdd.forall(primed_variables, prog.implies(self.model.add_primes(formula)))

    def prog(self, items):
        name = str(items[0])
        return self.model.programs[name]

    def seq(self, items):
        item_a, item_b = items[0], items[2]
        return self.compose(item_a, item_b)

    def choice(self, items):
        return items[0] | items[2]

    def star(self, items):
        prog = items[0]
        old_result = self.identity
        new_result = self.identity | self.compose(old_result, prog)
        while old_result != new_result:
            old_result = new_result
            new_result = self.identity | self.compose(old_result, prog)
        return new_result

    def parens(self, items):
        return items[1]

    def parens_prog(self, items):
        return items[1]

    def compose(self, first, second):
        first_with_temp = self.model.add_temporary(first, for_primed=True)
        second_with_temp = self.model.add_temporary(second, for_primed=False)

        compose = first_with_temp & second_with_temp
        
        temporary_variables = ([s for s in self.bdd.support(compose) if s.endswith("T")])

        return self.bdd.exist(temporary_variables, compose)
    
    def find_identity(self):
        identity = self.bdd.true
        for proposition in self.bdd.support(self.model.law):
            identity &= ~(self.bdd.var(proposition) ^ self.model.add_primes(self.bdd.var(proposition))) 
        return identity


class SymbolicModel:
    def __init__(self, num_states: int, valuations: list[list[int]], valuation_names: list[str],
                                        programs: list[np.ndarray], program_names: list[str],
                                        tests: list[str]):
        
        self.num_states = num_states

        self.bdd = _bdd.BDD()
        self.bdd.configure(reordering=True)

        # generate empty BDDs for states
        self.states = [self.bdd.true for _ in range(self.num_states)]
        self.current_prop_number = 0
        self.number_of_primes = 0
        self.programs = {}
        

        for valuation, name in zip(valuations, valuation_names):
            self.add_valuation(valuation, name)

        # after adding all propositions to the states, add more propositions to make the
        # states unique
        self.make_states_unique()

        # using the explicit unique states to create the law
        self.theta = self.add_law()
        
        for program, name in zip(programs, program_names):
            self.add_program(program, name)
        
        for test in tests:
            self.check_test(test)

        # after adding law and the programs the explicit states are not necessary anymore
        del self.states

    grammar = """
    ?start: formula

    ?formula: biconditional

    ?biconditional: implication
                | implication BICONDITIONAL biconditional               -> equiv

    ?implication: disjunction
                | disjunction IMPLICATION implication                   -> implies

    ?disjunction: conjunction
                | disjunction DISJUNCTION conjunction                   -> or_

    ?conjunction: unary
                | conjunction CONJUNCTION unary                         -> and_

    ?unary: NEGATE unary                                                -> not_
                | SYMBOL                                                -> formula_symbol
                | LPAR formula RPAR                                     -> parens
                | modal

    ?modal: "[" program "]" formula                                     -> box
                | "<" program ">" formula                               -> diamond

    ?program: sequence

    ?sequence: choice
                | choice SEQUENCE sequence                              -> seq

    ?choice: choice CHOICE iteration                                    -> choice
                | iteration

    ?iteration: program_atom
                | program_atom ITERATION                                -> star

    ?test: TEST formula                                                 -> test

    ?program_atom: SYMBOL                                              -> program_symbol
                | test
                | LPAR program RPAR                                     -> parens_prog
    %ignore " "
    TEST: "?"
    SEQUENCE: ";"
    CHOICE: "U"
    ITERATION: "*"
    NEGATE: "!"
    CONJUNCTION: "&"
    DISJUNCTION: "|"
    BICONDITIONAL: "<->"
    IMPLICATION: "->"
    DIAMOND_OPEN: "<"
    DIAMOND_CLOSE: ">"
    BOX_OPEN: "["
    BOX_CLOSE: "]"
    LPAR: "("
    RPAR: ")"

    SYMBOL: /[a-zA-Z_][a-zA-Z0-9_]*/
    """

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
        

    def create_new_prop(self, name=None):
        if name:
            current_prop_name = name
        else:
            current_prop_name = f'x{self.current_prop_number}'

        self.bdd.declare(current_prop_name)
        self.current_prop_number += 1
        return self.bdd.var(current_prop_name)

    def every_second_duplicate_index(self):
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
        duplicate_indices = self.every_second_duplicate_index()

        while duplicate_indices:
            # to seperate, add new property that's true for all second duplicates and
            # false for others
            new_prop = self.create_new_prop()

            # only saving the non negated variables
            # for index, state in enumerate(self.states):
            #     if index in duplicate_indices and self.states[index] == self.bdd.false:
            #         self.states[index] = self.bdd.true & new_prop
            #     elif index in duplicate_indices and self.states[index] != self.bdd.false:
            #         self.states[index] &= new_prop
            #     if self.states[index] == self.bdd.false:
            #         self.states[index] = self.bdd.true & ~new_prop
            #     elif self.states[index] != self.bdd.false:
            #         self.states[index] &= ~new_prop
            
            for index, state in enumerate(self.states):
                if index in duplicate_indices:
                    self.states[index] &= new_prop
                else:
                    self.states[index] &= ~new_prop
      
            duplicate_indices = self.every_second_duplicate_index()
    
    def program_or_formula(self, token: Token) -> Token:
        """
        finds if a token is a program or a formula and changes it's type accordingly
        """
        if token.value in self.bdd.vars:
            token.type = 'FORMULA'
        elif token.value in self.programs.keys():
            token.type = 'PROGRAM'
        else:
            raise ValueError(f'Symbol value {token.value} not found in model')
        return token

    def add_valuation(self, valuations: list, name=None):
        if len(valuations) != self.num_states:
            raise ValueError('Different number of valuations than states')
        
        new_prop = self.create_new_prop(name)
        # per state add the corresponding valuation of a single proposition
        for i, valuation in enumerate(valuations):
            if valuation == 1:
                self.states[i] &= new_prop
            else:
                self.states[i] &= ~new_prop
                

        # for i, valuation in enumerate(valuations):
        #     if valuation == 1 and self.states[i] == self.bdd.false:
        #         self.states[i] = self.bdd.true & new_prop
        #     elif valuation == 1:
        #         self.states[i] &= new_prop

    def add_law(self):
        result = self.bdd.false
        for state in self.states:
            result = result | state
        return result
        
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
            target_state_primed = self.add_primes(self.states[target_state_index])

            transition = base_state & target_state_primed
            program_bdd = program_bdd | transition

        # merge all seperate relation formulas in one final formula string
        self.programs[program_name] = program_bdd

    def check_test(self, test: str):
        parser = Lark(self.grammar,
                           parser='earley',
                           lexer='basic')
        tree = parser.parse(test)
        
        print(self.bdd.to_expr(PDLTransformer(self).transform(tree)))     

    def __str__(self):

        return_string = f'Number of states \n {self.num_states} \n \n Theta:\n{self.theta.to_expr()}'


        # for i, state in enumerate(self.states):
        #     return_string += f' \n{i}:\n {state.to_expr()}'

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
    tests = []
    
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
                tests.append(line.strip())
                line = f.readline()
                
            else:
                line = f.readline()

    return SymbolicModel(num_states, valuations, valuation_names, programs, program_names, tests)

test = SymbolicModelFromFile('small_kripke.txt')
# print(test.check_test('<a;b*>(p&!q)'))


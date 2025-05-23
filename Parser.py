from lark import Transformer, Lark
import SymbolicModel


class PDLTransformer(Transformer):
    def __init__(self, model):
        self.model = model
        self.identity = self.find_identity()
        self.parser = Lark(self.grammar,
                            parser='earley',
                            lexer='basic')
        
    def expression_transformer(self, test):
        self.tree = self.parser.parse(test)
        return self.transform(self.tree)
    
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

    def formula(self, items):
        name = str(items[0])
        return self.model.bdd.var(name)
    
    def formula_symbol(self, items):
        name = str(items[0])
        if name not in self.model.bdd.vars:
            raise ValueError(f"Expected formula symbol, got unknown: {name}")
        return self.model.bdd.var(name)

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
        return self.model.bdd.apply('xor', items[0], items[2])

    def diamond(self, items):
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.model.bdd.support(prog) if s.endswith("'")])

        return self.model.bdd.exist(primed_variables, prog & self.model.add_primes(self.model.law) & self.model.add_primes(formula))

    def box(self, items):
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.model.bdd.support(prog) if s.endswith("'")])
        
        return self.model.bdd.forall(primed_variables, (prog & self.model.add_primes(self.model.law)).implies(self.model.add_primes(formula)))

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
        
        temporary_variables = ([s for s in self.model.bdd.support(compose) if s.endswith("T")])

        return self.model.bdd.exist(temporary_variables, compose)
    
    def find_identity(self):
        identity = self.model.bdd.true
        for proposition in self.model.bdd.support(self.model.law):
            p = self.model.bdd.var(proposition)
            p_prime = self.model.add_primes(p)
            identity &= ~self.model.bdd.apply('xor', p, p_prime)
        return identity
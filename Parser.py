from lark import Transformer, Lark
import dd.cudd as _bdd
from ExplicitSymbolicModel import BDD
from typing import Union

FormulaItems = list[Union[str, BDD]]


class PDLTransformer(Transformer):
    def __init__(self, model):
        self.model = model
        self.identity = self.find_identity()
        self.parser = Lark(self.grammar,
                            parser='earley',
                            lexer='basic')
        
    def evaluate_expression(self, test: str) -> BDD:
        self.tree = self.parser.parse(test)
        return self.transform(self.tree)
    
    grammar =  """ 
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

            ?test: formula TEST   -> test

            ?program_atom: SYMBOL                                               -> program_symbol
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
    
    def formula_symbol(self, items: FormulaItems) -> BDD:
        """Returns the formula variable from the model given in the items list

        Args:
            items (FormulaItems): AST tree as given by the lark parser

        Raises:
            ValueError: The given formula name is not found in the model

        Returns:
            BDD: The formula variable from the model.
        """        
        name = str(items[0])
        if name not in self.model.bdd.vars:
            raise ValueError(f"Expected formula symbol, got unknown: {name}")
        return self.model.bdd.var(name)

    def program_symbol(self, items: FormulaItems) -> BDD:
        """Returns the program from the model given by the items list

        Args:
            items (FormulaItems): AST tree as given by the lark parser

        Raises:
            ValueError: The given program name is not found in the model

        Returns:
            BDD: Returns the program BDD from the model
        """        
        name = str(items[0])
        if name not in self.model.programs.keys():
            raise ValueError(f"Expected program symbol, got unknown: {name}")
        return self.model.programs[name]

    def not_(self, items: FormulaItems) -> BDD:
        """Returns the negation of the given variable

        Args:
            items (FormulaItems): The AST tree given by the lark parser, where the first items
            should be the negate operator ! and the second items should be the variable to be negated

        Raises:
            ValueError: The AST tree doesn't start with the negate operator.

        Returns:
            BDD: The negated variable
        """ 
        if items[0] != '!':
            raise ValueError(f'Expected the negate operator, found {items[0]}')
        return ~items[1]
    
    def test(self, items: FormulaItems) -> BDD:
        return self.identity & items[0]

    def and_(self, items: FormulaItems) -> BDD:
        """Returns the conjunction of the two variables given by the AST tree

        Args:
            items (FormulaItems): The AST tree given by the lark parser, the variables should be
            the first and third argument, with the conjunction operator between them.

        Raises:
            ValueError: Second item of the AST tree not the conjunction operator '&'

        Returns:
            BDD: The result of the conjunction
        """ 
        
        if items[1] != '&':
            raise ValueError(f'Expected the negate operator, found {items[1]}')
        return items[0] & items[2]

    def or_(self, items: FormulaItems) -> BDD:
        """Returns the disjunction of the two variables given by the AST tree

        Args:
            items (FormulaItems): The AST tree given by the lark parser, the variables should be
            the first and third argument, with the disjunction operator between them.

        Raises:
            ValueError: Second item of the AST tree not the disjunction operator '|'

        Returns:
            BDD: The result of the disjunction
        """ 
        if items[1] != '|':
            raise ValueError(f'Expected the negate operator, found {items[1]}')
        return items[0] | items[2]

    def implies(self, items: FormulaItems) -> BDD:
        return ~items[0] | items[2]

    def equiv(self, items: FormulaItems) -> BDD:
        return self.model.bdd.apply('xor', items[0], items[2])

    def diamond(self, items: FormulaItems) -> BDD:
        """_summary_

        Args:
            items (FormulaItems): _description_

        Returns:
            BDD: _description_
        """        
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.model.bdd.support(prog) if s.endswith("'")])

        return self.model.bdd.exist(primed_variables, prog & self.model._add_primes(self.model.law) & self.model._add_primes(formula))

    def box(self, items: FormulaItems) -> BDD:
        prog = items[0]
        formula = items[1]

        primed_variables = ([s for s in self.model.bdd.support(prog) if s.endswith("'")])
        
        return self.model.bdd.forall(primed_variables, (prog & self.model._add_primes(self.model.law)).implies(self.model._add_primes(formula)))

    def seq(self, items: FormulaItems) -> BDD:
        item_a, item_b = items[0], items[2]
        return self.compose(item_a, item_b)

    def choice(self, items: FormulaItems) -> BDD:
        return items[0] | items[2]

    def star(self, items: FormulaItems) -> BDD:
        prog = items[0]
        old_result = self.identity
        new_result = self.identity | self.compose(old_result, prog)
        while old_result != new_result:
            old_result = new_result
            new_result = self.identity | self.compose(old_result, prog)
        return new_result

    def parens(self, items: FormulaItems) -> BDD:
        return items[1]

    def parens_prog(self, items: FormulaItems) -> BDD:
        return items[1]

    def compose(self, first: BDD, second: BDD) -> BDD:
        first_with_temp = self.model._add_temporary(first, is_primed=True)
        second_with_temp = self.model._add_temporary(second, is_primed=False)

        compose = first_with_temp & second_with_temp
        
        temporary_variables = ([s for s in self.model.bdd.support(compose) if s.endswith("T")])

        return self.model.bdd.exist(temporary_variables, compose)
    
    def find_identity(self) -> BDD:
        identity = self.model.bdd.true
        for proposition in self.model.bdd.support(self.model.law):
            p = self.model.bdd.var(proposition)
            p_prime = self.model._add_primes(p)
            identity &= ~self.model.bdd.apply('xor', p, p_prime)
        return identity
    
    
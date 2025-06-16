from SymbolicModel import SymbolicModel
import argparse
from time import time

def generate_model(args):
    if args.file:
        try:
            f = open(args.file)
            f.close()
        except FileNotFoundError:
            print('File does not exist or wrong input')
        t0 = time()
        model = SymbolicModel.from_file(args.file)
        t1 = time()
        print(f'Model from {args.file} created in {t1-t0:.3e} seconds')
        return model

    elif args.random:
        num_states, num_valuations, num_programs = args.random
        t0 = time()
        model = SymbolicModel.random(num_states, num_valuations, num_programs)
        t1 = time()
        print(f'Random model with {num_states} states, {num_valuations} propositions and {num_programs} programs created in {str(t1-t0)} seconds')
        return model
    else:
        raise ValueError('No model generation type given (either --file or --random)')

def find_tests(model, args):
    if args.formula:
        return [args.formula]
    elif args.T:
        return model.file_tests()
    else:
        return None

def output_bdd_file_name(test: str, args: argparse.Namespace) -> str:
    file_name = ''
    if args.random:
        file_name += 'random'
    elif args.file:
        file_name += args.file
    file_name = file_name.replace('.txt', '')
    file_name += '_'
    file_name += test
    file_name += '.png'
    return file_name

def output_to_file(test, model, args):
    file_name = output_bdd_file_name(test, args)
    try:
        t0 = time()
        model.check(test, print_bdd_filename=file_name)
        t1 = time()
        print(f'Result succesfully exported to {file_name} in {t1-t0:.3e} seconds')
    except:
        print('Unable to export result to file')

def output_specific_state(test, model, args):
    try:
        t0 = time()
        result = model.check(test, state_valuation=args.state)
        t1 = time()
        print(f'Test: {test}')
        print(f'In state: {args.state}')
        print(f'Result: {result}')
        print(f'Time: {t1-t0:.3e}\n')
    except:
        print(f'Unable to test {test} in state {args.state}')

def output_vector(test, model):
    try:
        t0 = time()
        result = model.check(test)
        t1 = time()
        print(f'Test: {test}')
        print(f'Result: {result}')
        print(f'Time: {t1-t0:.3e}\n')
    except:
        print(f'Unable to test {test}')


def output(tests, model, args):
    if tests is None:
        check_formula_interactive(model, args)
    else:
        for test in tests:
            if args.printbdd:
                output_to_file(test, model, args)
            elif args.state:
                output_specific_state(test, model, args)
            else:
                output_vector(test, model)


def check_formula_interactive(model: SymbolicModel, args)-> None:
    while True:
        input_formula = input("Enter a PDL formula (or type 'h' for help, 'q' to quit):\n")
        cmd = input_formula.strip().lower()

        if cmd == 'h':
            print("Compound formulas and programs must always be between parentheses\n"
                    "EXAMPLE: <a;(bUc)>(p->q)\n\n"
                    "Formula Operators:\n"
                    "<a>p = <a>p\n"
                    "[a]p = [a]p\n"
                    "Negation(p) = !p\n"
                    "Logical AND = &\n"
                    "Logical OR = |\n"
                    "Implication = ->\n\n"
                    "Program Operators:\n"
                    "Test(p) = p?\n"
                    "Kleene_Star(a) = a*\n"
                    "Composition = ;\n"
                    "Union = U\n"
                    )

        elif cmd in {'q', 'quit', 'stop'}:
            print('Stopping')
            break

        else:
            try:
                output([cmd], model, args)
            except ValueError:
                print('State not found in model')


def parse():
    parser = argparse.ArgumentParser(description="PDL Model Checker")

    input_model = parser.add_mutually_exclusive_group(required=True)
    flag_group = parser.add_mutually_exclusive_group()
    input_model.add_argument('--file', metavar='FILENAME', type=str, help="Input model from a file")
    flag_group.add_argument("--T", action='store_true', help="Use tests provided in file")
    input_model.add_argument('--random', nargs=3, type=int, metavar=('num_states', 'num_valuations', 'num_programs'), help="Generate random model of given size")

    flag_group.add_argument("--formula", type=str, help="Evaluate a single formula and exit")

    output_group = parser.add_mutually_exclusive_group()
    output_group.add_argument('--vector', action='store_true', help="Return truth vector for all states")
    output_group.add_argument('--state', metavar='STATE VALUATION', type=str, help="Evaluate formula in a specific state, only available for models with unique states")
    output_group.add_argument('--printbdd', action='store_true', help="Write BDD expression to file")

    args = parser.parse_args()

    if args.T and not args.file:
        parser.error("--T can only be used with --file.")

    return args

def main():
    args = parse()
    model = generate_model(args)
    tests = find_tests(model, args)
    output(tests, model, args)


if __name__ == "__main__":
    main()
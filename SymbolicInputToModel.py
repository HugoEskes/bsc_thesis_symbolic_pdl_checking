import numpy as np
import dd.cudd as cudd

def map_new_variable_names(expression: str, mapping: dict[str, str]) -> str:
    for orig_name, new_name in mapping.items():
        expression = expression.replace(orig_name, new_name)
    return expression

def SymbolicModelFromSymbolic(file: str) -> tuple[cudd.BDD, list[str], cudd.BDD, dict[str, cudd.BDD]]:
    components = ['PROPS', 'LAW', 'PROGRAMS']
    mode = None
    variables = []
    mapping_variable_names = {}
    programs = {}
    law = None
    bdd = cudd.BDD()

    with open(file, 'r') as f:
        line = f.readline()
        while line:
            line = line.strip()
            if not line.split():
                line = f.readline()
            elif line in components:
                mode = line
                line = f.readline()
            elif mode == 'PROPS':
                variables = line.split(',')
                for i in range(len(variables)):
                    if variables[i].isdigit():
                        print(f'Note: variable {variables[i]} replaced with x{variables[i]}')
                        mapping_variable_names[variables[i]] = 'x' + variables[i]
                        variables[i] = 'x' + variables[i]
                    else:
                        mapping_variable_names[variables[i]] = variables[i]

                    bdd.declare(variables[i], variables[i]+"'")

                line = f.readline()
            elif mode == 'LAW':
                if line:
                    law_expr = map_new_variable_names(line, mapping_variable_names)
                    
                    try:
                        law = bdd.add_expr(law_expr)
                    except Exception as e:
                        if isinstance(e, ValueError):
                            raise ValueError(f'Variable used in law ({line}) that is not declared in VARS section ({variables})') from e
                        elif isinstance(e, RuntimeError):
                            raise RuntimeError(f'Invalid character/operator used in law ({line})') from e
                        else:
                            raise Exception(f'Unexpected error during the creation of the law: {e}') from e
                    
                line = f.readline()

            elif mode == 'PROGRAMS':
                if line.split():
                    program_name = line
                    if program_name in programs:
                        raise ValueError(f'Program name {program_name} is not unique, all program names must be unique')
                    programs[program_name] = bdd.false                   

                    line = f.readline()
                    while line and line.split():
                        try:
                            transition = map_new_variable_names(line, mapping_variable_names)
                            new_transition = bdd.add_expr(transition)
                        except Exception as e:
                            if isinstance(e, ValueError):
                                raise ValueError(f'Variable used in transition ({line}) that is not declared in VARS section ({variables})') from e
                            elif isinstance(e, RuntimeError):
                                raise RuntimeError(f'Invalid character/operator used in transition ({line})') from e
                            else:
                                raise Exception(f'Unexpected error during the creation of the transition: {line}') from e
                            
                        programs[program_name] = programs[program_name] | new_transition
                    
                        line = f.readline()

                line = f.readline()
            else:
                line = f.readline()
    
    return bdd, variables, law, programs

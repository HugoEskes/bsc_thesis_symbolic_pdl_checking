
import numpy as np
from SymbolicModel import SymbolicModel
    

def SymbolicModelFromFile(file: str) -> SymbolicModel:
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
    return SymbolicModel(num_states, valuations, valuation_names, programs, program_names)


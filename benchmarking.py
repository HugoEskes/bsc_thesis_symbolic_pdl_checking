import time
from SymbolicModel import SymbolicModel
from ExplicitSymbolicModel import ExplicitSymbolicModel
import matplotlib.pyplot as plt
import dd.cudd as cudd
import numpy as np
from math import ceil, log2
import pandas as pd
from datetime import datetime

def encode_state(bdd, var_names, index) -> cudd.BDD:
    bits = bin(index)[2:].zfill(len(var_names))
    cube = bdd.true
    for bit, var in zip(bits, var_names):
        cube &= bdd.var(var) if bit == '1' else ~bdd.var(var)
    return cube

def create_symbolic_model(num_states: int, reorder: bool = False) -> tuple[cudd.BDD, list[str], cudd.BDD, dict[str, cudd.BDD]]:
    bdd = cudd.BDD()
    bdd.configure(reordering=reorder)

    if num_states < 3:
        raise ValueError('Model needs at least three states')
    if num_states % 2 == 0:
        num_states += 1

    num_bits = ceil(log2(num_states))
    state_vars = [f'x{i}' for i in range(num_bits)]
    state_vars_primed = [f"x{i}'" for i in range(num_bits)]
    bdd.declare(*state_vars, *state_vars_primed, 'p', "p'")

    # Valid state constraint: current state's encoding < num_states
    valid_state = bdd.false
    for i in range(num_states):
        valid_state |= encode_state(bdd, state_vars, i)

    # Constraint: final state ↔ p
    law = valid_state & bdd.apply('<->', encode_state(bdd, state_vars, num_states - 1), bdd.var('p'))

    # Build transition relation
    program = bdd.false

    # Fork: 0 → 1 and 0 → 2
    program |= encode_state(bdd, state_vars, 0) & encode_state(bdd, state_vars_primed, 1)
    program |= encode_state(bdd, state_vars, 0) & encode_state(bdd, state_vars_primed, 2)

    # Steps of +2
    for i in range(1, num_states - 2):
        program |= encode_state(bdd, state_vars, i) & encode_state(bdd, state_vars_primed, i + 2)

    # Final transition includes p'
    program |= encode_state(bdd, state_vars, num_states - 3) & encode_state(bdd, state_vars_primed, num_states - 1) & bdd.var("p'")

    programs = {'a': program}
    return bdd, state_vars, law, programs


def create_explicit_model(num_states: int) -> tuple[int, list[list[int]], list[str], list[np.ndarray], list[str]]:

    if num_states < 3:
        raise ValueError('Model needs at least three states')
    if num_states % 2 == 0:
        num_states += 1

    num_bits = ceil(log2(num_states))
    proposition_names = [f'x{i}' for i in range(num_bits)]
    proposition_names.append('p')

    valuations = []
    for i in range(num_states):
        bits = [(i >> b) & 1 for b in range(num_bits)]
        valuations.append(bits)

    valuations = np.array(valuations).T.tolist()

    program = np.zeros((num_states, num_states))
    program[0][1] = 1
    for i in range(num_states - 2):
        program[i][i+2] = 1
    programs = [program]

    program_names = ['a']

    return num_states, valuations, proposition_names, programs, program_names


results = []

values = np.logspace(np.log10(10), np.log10(500), 30).astype(int).tolist()


for i in values[:20]:
    bdd, prop_names, law, programs = create_symbolic_model(i)
    model = SymbolicModel(bdd, prop_names, law, programs)
    model.check('<a*>p')

for i in values:
    for j in range(3):
        
        start_cpu = time.process_time_ns()
        bdd, prop_names, law, programs = create_symbolic_model(i, False)
        model = SymbolicModel(bdd, prop_names, law, programs)
        model.check('<a*>p')
        time_taken = time.process_time_ns() - start_cpu 
        print(f'num_states: {i}\nrun: {j},\nmethod: without_reordering, \nrun_time: {time_taken / 1e9}')

        results.append({'num_states': i, 'run': j, 'method': 'without_reordering', 'run_time': time_taken/1e9})



        
        start_cpu = time.process_time_ns()
        bdd, prop_names, law, programs = create_symbolic_model(i, True)
        model = SymbolicModel(bdd, prop_names, law, programs)
        model.check('<a*>p')
        time_taken = time.process_time_ns() - start_cpu 
        print(f'num_states: {i}\nrun: {j},\nmethod: with_reordering, \nrun_time: {time_taken / 1e9}')

        results.append({'num_states': i, 'run': j, 'method': 'with_reordering', 'run_time': time_taken/1e9})

current_time_str = datetime.now()
current_time_str = current_time_str.strftime("%H%M")
df = pd.DataFrame(results)

# Save to disk
df.to_csv(f'results_{current_time_str}.csv', index=False)

# # num_states = []
# # time_taken = []
# # for j in range(50):
# #     individ_time_taken = []
# #     for i in range(30):
# #         t0 = time()
# #         model = SymbolicModel.random(i+1, i+1, i+1)
# #         t1 = time()
# #         individ_time_taken.append(t1-t0)
# #     time_taken.append(individ_time_taken)

# # time_taken = np.array(time_taken)
# # averages = np.mean(time_taken, axis=0)
# # std_devs = np.std(time_taken, axis=0)

# # num_states = np.arange(1, 30 + 1)


# # plt.plot(num_states, averages, label="Dense", color="red")

# # plt.xlabel("Number of States")
# # plt.ylabel("CPU Time (in sec.)")
# # plt.legend()
# # plt.grid(True)
# # plt.show()

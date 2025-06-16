from time import time
from SymbolicModel import SymbolicModel
import matplotlib.pyplot as plt
import numpy as np

num_states = []
time_taken = []
for j in range(50):
    individ_time_taken = []
    for i in range(30):
        t0 = time()
        model = SymbolicModel.random(i+1, i+1, i+1)
        t1 = time()
        individ_time_taken.append(t1-t0)
    time_taken.append(individ_time_taken)

time_taken = np.array(time_taken)
averages = np.mean(time_taken, axis=0)
std_devs = np.std(time_taken, axis=0)

num_states = np.arange(1, 30 + 1)


plt.plot(num_states, averages, label="Dense", color="red")

plt.xlabel("Number of States")
plt.ylabel("CPU Time (in sec.)")
plt.legend()
plt.grid(True)
plt.show()
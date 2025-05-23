from TextToModel import SymbolicModelFromFile
from typing import Union

def check_test(model_file_name: str, test: str, state_valuation: str=None) -> Union[bool, str]:
    model = SymbolicModelFromFile(model_file_name)
    return model.check(test, state_valuation)

print(type(check_test('small_kripke.txt', '[a]q')))

print(check_test('small_kripke.txt', '[a]q'))
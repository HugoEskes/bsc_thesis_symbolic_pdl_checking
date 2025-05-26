from TextToModel import SymbolicModelFromFile
from typing import Union

def check_test(model_file_name: str, tests: list[str], state_valuation: str=None) -> Union[bool, str]:
    with SymbolicModelFromFile(model_file_name) as model:
        for test in tests:
            print(model.check(test, state_valuation))

tests = ['<a;b*>(p&!q)', '[a;b*](p&!q)', '[a*]p']

check_test('test.txt', tests)
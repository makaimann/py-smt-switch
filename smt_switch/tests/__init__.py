from smt_switch.src import solvers

all_solvers = {'Z3': solvers.Z3Solver,
               'CVC4': solvers.CVC4Solver}

bv_solvers = {'Z3': solvers.Z3Solver,
              'CVC4': solvers.CVC4Solver,
              'Boolector': solvers.BoolectorSolver}

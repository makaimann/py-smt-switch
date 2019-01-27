# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.
from enum import Enum

from . import solverbase
from .BoolectorSolver import BoolectorSolver
from .CVC4Solver import CVC4Solver
from .Z3Solver import Z3Solver

from ..terms import TermBase
from ..terms import BoolectorTerm, CVC4Term, Z3Term

class SOLVERS(Enum):
    Z3 = Z3Solver, Z3Term
    CVC4 = CVC4Solver, CVC4Term
    Boolector = BoolectorSolver, BoolectorTerm

    @classmethod
    def from_string(cls, solver_string:str) -> 'SOLVERS':
        '''converts a string into a enum value'''
        try:
            return cls.__members__[solver_string]
        except KeyError:
            raise ValueError('{} is not a supported solver'.format(solver_name))

    @property
    def available(self) -> bool:
        '''checks if solver is available'''
        try:
            self.Solver._import_func()
        except ImportError:
            return False
        else:
            return True

    @property
    def Term(self) -> TermBase:
        return self.value[1]

    @property
    def Solver(self) -> solverbase.SolverBase:
        return self.value[0]

    def construct_api(self, strict:bool=False) -> 'smt':
        '''builds an smt api object bound to the solver'''
        from ..api import smt
        #If we deprecate direct construct of smt apis
        #we could pass the solver object directly and term type to the api
        #removing the circular dependency
        return smt(self, strict)

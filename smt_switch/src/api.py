from collections import Sequence
from ..config import config
from . import sorts
from . import functions
from . import terms
from . import solvers


def check_solver(f):
    def eval_f(self, *args):
        if self.solver is None:
            raise ValueError('Please set solver before using a solver function')
        else:
            return f(self, *args)

    return eval_f


class _smt:
    # better to reinitialize each time actually
    # __solver_cache = {'CVC4': None,
    #                   'Z3': None,
    #                   'Boolector': None}
    __solver_map = {'CVC4': solvers.CVC4Solver,
                    'Z3': solvers.Z3Solver,
                    'Boolector': solvers.BoolectorSolver}
    __term_map = {solvers.CVC4Solver: terms.CVC4Term,
                  solvers.Z3Solver: terms.Z3Term,
                  solvers.BoolectorSolver: terms.BoolectorTerm}

    def __init__(self):
        self._solver = None
        self.constraints = []

    def __call__(self, solver_name=None):
        if solver_name in self.__solver_map:
            self.set_solver(solver_name)
        else:
            raise ValueError('{} is not a supported solver'.format(solver_name))

        return self

    def set_solver(self, solver_name):
        # originally returned solver instance if it already existed,
        # but this could be confusing because you'd have to reset the
        # solver to be sure it wasn't already carrying assertions
        # easier to just overwrite
        self._solver = self.__solver_map[solver_name]()
        self.constraints = []

    def construct_fun(self, fun, *args):
        # partial function evaluation all handled internally
        return fun(*args)

    def construct_sort(self, s, *args):
        return s(*args)

    @property
    def solver(self):
        return self._solver

    # solver functions
    @check_solver
    def add(self, c):
        ''' Alias for Assert '''
        self.solver.add(c)

    @check_solver
    def reset(self):
        self.solver.reset()

    @check_solver
    def check_sat(self):
        return self.solver.check_sat()

    @property
    @check_solver
    def sat(self):
        return self.solver.sat

    @check_solver
    def set_logic(self, logicstr):
        self.solver.set_logic(logicstr)

    @check_solver
    def set_option(self, optionstr, value):
        self.solver.set_option(optionstr, value)

    @check_solver
    def declare_const(self, name, sort):
        sconst = self.solver.declare_const(name, sort)
        return self.__term_map[self.solver.__class__](self,
                                                      self.No_op,
                                                      sconst,
                                                      [sort])

    @check_solver
    def theory_const(self, sort, value):
        stconst = self.solver.theory_const(sort, value)
        return self.__term_map[self.solver.__class__](self,
                                                      self.No_op,
                                                      stconst,
                                                      [sort])

    @check_solver
    def apply_fun(self, fun, *args):
        # handle lists of arguments
        if isinstance(args[0], Sequence):
            args = tuple(args[0])

        for arg in args:
            if arg.__class__ is not self.__term_map[self._solver.__class__] and \
               arg.__class__ in self.__term_map.values():  # raw python types are fine
                raise ValueError('Mixing terms with different solvers is not allowed.\n'
                                 'Found a {}, but the solver is {}'.format(arg.__class__,
                                                                           self._solver.__class__))

        ls_term = list(filter(lambda x: hasattr(x, 'solver_term'), args))[-1]

        if config.strict:
            solver_args = tuple([arg.solver_term for arg in args])

        else:
            solver_args = tuple([arg.solver_term
                                 if hasattr(arg, 'solver_term')
                                 else
                                 self.solver.theory_const(ls_term.sort, arg)
                                 for arg in args])

        s_term = self.solver.apply_fun(fun.fname, fun.args, *solver_args)
        return self.__term_map[self._solver.__class__](self,
                                                       fun,
                                                       s_term,
                                                       list(args))

    @check_solver
    def Assert(self, *constraints):
        if isinstance(constraints[0], Sequence):
            constraints = tuple(constraints[0])

        for constraint in constraints:
            sort = getattr(constraint, 'sort', type(constraint))

            if sort != bool and sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. '
                                 'Received sort: {}'.format(sort))

            if hasattr(constraint, 'solver_term'):
                c = constraint.solver_term
            else:
                c = self.solver.theory_const(sorts.Bool(), constraint)

            self.solver.Assert(c)

            # add wrapped constraint to solver assertions
            self.constraints.append(constraint)

    @property
    @check_solver
    def assertions(self):
        return self.solver.assertions()

    @check_solver
    def get_model(self):
        raise NotImplementedError()

    @check_solver
    def get_value(self, var):
        var._value = self.solver.get_value(var.solver_term)
        return var


# instantiate the smt api
smt = _smt()


for name, fdata in functions.func_symbols.items():
    op = functions.__gen_operator(smt, name, fdata)
    setattr(smt, name, op)

for s in sorts.__all__:
    setattr(smt, s, sorts.__dict__[s])

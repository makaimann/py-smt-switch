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


def check_instance(f):
    def eval_f(self, *terms):
        if isinstance(terms[0], Sequence):
            terms = terms[0]

        for term in terms:
            # if it's a term object, verify that the
            # smt api instance is the same as the one
            # currently being used
            if hasattr(term, '_smt') and term._smt != self:
                raise ValueError('Bad! Mixing terms from different api (smt) instances')

        return f(self, *terms)

    return eval_f


class smt:

    __solver_map = {'CVC4': solvers.CVC4Solver,
                    'Z3': solvers.Z3Solver,
                    'Boolector': solvers.BoolectorSolver}
    __term_map = {solvers.CVC4Solver: terms.CVC4Term,
                  solvers.Z3Solver: terms.Z3Term,
                  solvers.BoolectorSolver: terms.BoolectorTerm}

    def __init__(self, solver_name):
        if solver_name not in self.__solver_map:
            raise ValueError('{} is not a supported solver'.format(solver_name))

        self._solver = self.__solver_map[solver_name]()
        self.constraints = []

        # give the instance access to functions
        for f_enum in functions.func_enum:
            op = functions.operator(self, f_enum, functions.func_symbols[f_enum.name])
            setattr(self, f_enum.name, op)

        # give the instance access to sorts
        for s in sorts.__all__:
            setattr(self, s, sorts.__dict__[s])

    def ConstructFun(self, fun, *args):
        # partial function evaluation all handled internally
        return fun(*args)

    def ConstructSort(self, s, *args):
        return s(*args)

    @property
    def solver(self):
        return self._solver

    # solver functions

    def Add(self, c):
        ''' Alias for Assert '''
        self.solver.Assert(c)

    def Reset(self):
        self.solver.Reset()

    def CheckSat(self):
        return self.solver.CheckSat()

    @property
    def Sat(self):
        return self.solver.Sat

    def SetLogic(self, logicstr):
        self.solver.SetLogic(logicstr)

    def SetOption(self, optionstr, value):
        self.solver.SetOption(optionstr, value)

    def DeclareConst(self, name, sort):
        assert isinstance(name, str), 'name parameter should be a string'
        sconst = self.solver.DeclareConst(name, sort)
        return self.__term_map[self.solver.__class__](self,
                                                      self.No_op,
                                                      sconst,
                                                      [sort])

    def TheoryConst(self, sort, value):
        stconst = self.solver.TheoryConst(sort, value)
        return self.__term_map[self.solver.__class__](self,
                                                      self.No_op,
                                                      stconst,
                                                      [sort])

    @check_instance
    def ApplyFun(self, fun, *args):
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
                                 self.solver.TheoryConst(ls_term.sort, arg)
                                 for arg in args])

        s_term = self.solver.ApplyFun(fun.enum, fun.args, *solver_args)
        return self.__term_map[self._solver.__class__](self,
                                                       fun,
                                                       s_term,
                                                       list(args))

    @check_instance
    def Assert(self, *constraints):
        if isinstance(constraints[0], Sequence):
            constraints = tuple(constraints[0])

        for constraint in constraints:
            sort = getattr(constraint, 'sort', type(constraint))

            if sort not in {bool, sorts.Bool(), sorts.BitVec(1)}:
                raise ValueError('Can only assert formulas of sort Bool/BitVec(1). '
                                 'Received sort: {}'.format(sort))

            if hasattr(constraint, 'solver_term'):
                c = constraint.solver_term
            else:
                c = self.solver.TheoryConst(sorts.Bool(), constraint)

            self.solver.Assert(c)

            # add wrapped constraint to solver assertions
            self.constraints.append(constraint)

    @property
    def Assertions(self):
        return self.solver.Assertions()

    def GetModel(self):
        raise NotImplementedError()

    def GetValue(self, var):
        var._value = self.solver.GetValue(var.solver_term)
        return var

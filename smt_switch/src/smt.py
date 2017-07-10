import sys
from collections import Sequence
# register sort and function namespaces
from . import sorts
from . import functions
from . import terms
from . import results
from . import solvers
from ..config import config

__all__ = ['And', 'Or']

_solver = None
__solver_cache = {'CVC4': None,
                  'Z3': None,
                  'Boolector': None}
__solver_map = {'CVC4': solvers.CVC4Solver,
                'Z3': solvers.Z3Solver,
                'Boolector': solvers.BoolectorSolver}
__term_map = {solvers.CVC4Solver: terms.CVC4Term,
              solvers.Z3Solver: terms.Z3Term,
              solvers.BoolectorSolver: terms.BoolectorTerm}

sat = None

__smtmodule = sys.modules[__name__]


def set_solver(solver_name):
    global _solver

    if __solver_cache[solver_name] is None:
        __solver_cache[solver_name] = __solver_map[solver_name]()

    _solver = __solver_cache[solver_name]


# add functions to namespace and to __all__
for name, m in functions.func_symbols.items():
    f = functions.__gen_function(__smtmodule, name, m)
    __smtmodule.__dict__[name] = f
    __all__.append(name)


# construct a function in strict mode
def construct_fun(fun, *args):
    # partial function evaluation all handled internally
    return fun(*args)


# register in namespace
for s in sorts.__all__:
    __smtmodule.__dict__[s] = sorts.__dict__[s]
    __all__.append(s)



# solver functions
def add(c):
    ''' Alias for Assert '''
    global _solver
    _solver.add(c)


def reset(self):
    global _solver
    _solver.reset()


def check_sat():
    global _solver
    global sat
    sat = _solver.check_sat()
    return sat


def set_logic(logicstr):
    global _solver
    _solver.set_logic(logicstr)


def set_option(optionstr, value):
    global _solver
    _solver.set_logic(optionstr, value)


def declare_const(name, sort):
    global _solver
    sconst = _solver.declare_const(name, sort)
    return __term_map[_solver.__class__](__smtmodule,
                                        No_op,
                                        sconst,
                                        [sort])


def theory_const(sort, value):
    global _solver
    stconst = _solver.theory_const(sort, value)
    return __term_map[_solver.__class__](__smtmodule,
                                        No_op,
                                        stconst,
                                        [sort])


def apply_fun(fun, *args):
    global _solver
    # handle lists of arguments
    if isinstance(args[0], Sequence):
        args = tuple(args[0])

    ls_term = [getattr(arg, 'solver_term', arg) for arg in args][-1]

    if config.strict:
        solver_args = tuple([arg.solver_term for arg in args])

    else:
        solver_args = tuple([arg.solver_term
                             if hasattr(arg, 'solver_term')
                             else
                             _solver.theory_const(ls_term.sort, arg)
                             for arg in args])

    s_term = _solver.apply_fun(fun.fname, fun.args, *solver_args)
    return __term_map[_solver.__class__](__smtmodule,
                                        fun,
                                        s_term,
                                        list(args))


def Assert(constraints):
    global _solver
    if isinstance(constraints[0], Sequence):
        constraints = tuple(constraints[0])

    for constraint in constraints:
        sort = getattr(constraint, 'sort', type(constraint))

        if sort != bool and sort != sorts.Bool():
            raise ValueError('Can only assert formulas of sort Bool. '
                             'Received sort: {}'.format(sort))

        c = getattr(constraint, 'solver_term',
                    _solver.theory_const(sorts.Bool(), constraint))

        _solver.Assert(c)


def assertions():
    global _solver
    return _solver.assertions()


def get_model(self):
    raise NotImplementedError()


def get_value(self, var):
    raise NotImplementedError('Deprecating results so waiting to just '
                              'do get value correctly with terms')




def _bool_fun(*args):
    return sorts.Bool()


fun2sort = {'And': _bool_fun,
            'Or': _bool_fun,
            'No_op': sorts.get_sort,
            'Equals': _bool_fun,
            'Not': _bool_fun,
            'LT': _bool_fun,
            'GT': _bool_fun,
            'LEQ': _bool_fun,
            'GEQ': _bool_fun,
            'BVUlt': _bool_fun,
            'BVUle': _bool_fun,
            'BVUgt': _bool_fun,
            'BVUge': _bool_fun,
            'BVSlt': _bool_fun,
            'BVSle': _bool_fun,
            'BVSgt': _bool_fun,
            'BVSge': _bool_fun,
            'BVNot': sorts.get_sort,
            'BVNeg': sorts.get_sort,
            'Ite': lambda *args: sorts.get_sort(*args[1:]),
            'Sub': sorts.get_sort,
            'Add': sorts.get_sort,
            'Extract': lambda ub, lb, arg: sorts.BitVec(ub - lb + 1),
            'Concat': lambda b1, b2: sorts.BitVec(b1.sort.width + b2.sort.width),
            'Zero_extend': lambda bv, pad_width: sorts.BitVec(bv.sort.width + pad_width),
            'BVAnd': sorts.get_sort,
            'BVOr': sorts.get_sort,
            'BVXor': sorts.get_sort,
            'BVAdd': sorts.get_sort,
            'BVSub': sorts.get_sort,
            'BVMul': sorts.get_sort,
            'BVUdiv': sorts.get_sort,
            'BVUrem': sorts.get_sort,
            'BVShl': sorts.get_sort,
            'BVAshr': sorts.get_sort,
            'BVLshr': sorts.get_sort}


# class smt:
#     class __smt:
#         def __init__(self, solver):
#             # Handle the solver=None case
#             self._solver = solver

#         # do stuff with the solver

#     instance = None

#     def __init__(self, solver=None):

#         # add all the functions
#         for fname in functions.__all__:
#             self.__dict__[fname] = functions.__dict__[fname]

#         if not smt.instance:
#             smt.instance = smt.__smt(solver)
#         elif solver != smt.instance._solver:
#             smt.instance._solver = solver

#     def __getattr__(self, name):
#         return getattr(self.instance, name)

from functools import partial
from .. import sorts
from .. import functions
from .. import terms
from .. import results
from .solverbase import SolverBase
from smt_switch.config import config


class Z3Solver(SolverBase):
    # import z3
    z3 = __import__('z3')
    _z3Sorts = {sorts.BitVec: z3.BitVec,
                sorts.Int: z3.Int,
                sorts.Real: z3.Real,
                sorts.Bool: z3.Bool}
    # Note: indexed operators are already raw functions so don't use .func
    _z3Funs = {functions.extract: z3.Extract,
               functions.concat.func: z3.Concat,
               functions.zero_extend.func: z3.ZeroExt,
               functions.Not.func: z3.Not,
               functions.Equals.func: lambda arg1, arg2: arg1 == arg2,
               functions.And.func: z3.And,
               functions.Or.func: z3.Or,
               functions.Ite.func: z3.If,
               functions.Sub.func: lambda arg1, arg2: arg1 - arg2,
               functions.Plus.func: lambda arg1, arg2: arg1 + arg2,
               functions.LT.func: lambda arg1, arg2: arg1 < arg2,
               functions.LEQ.func: lambda arg1, arg2: arg1 <= arg2,
               functions.GT.func: lambda arg1, arg2: arg1 > arg2,
               functions.GEQ.func: lambda arg1, arg2: arg1 >= arg2,
               functions.bvand.func: lambda arg1, arg2: arg1 & arg2,
               functions.bvor.func: lambda arg1, arg2: arg1 | arg2,
               functions.bvxor.func: lambda arg1, arg2: arg1 ^ arg2,
               functions.bvadd.func: lambda arg1, arg2: arg1 + arg2,
               functions.bvsub.func: lambda arg1, arg2: arg1 - arg2,
               functions.bvmul.func: lambda arg1, arg2: arg1*arg2,
               functions.bvudiv.func: z3.UDiv,
               functions.bvurem: z3.URem,
               functions.bvshl.func: lambda arg1, arg2: arg1 << arg2,
               functions.bvashr.func: lambda arg1, arg2: arg1 >> arg2,
               functions.bvlshr.func: z3.LShR,
               functions.bvult.func: z3.ULT,
               functions.bvule.func: z3.ULE,
               functions.bvugt.func: z3.UGT,
               functions.bvuge.func: z3.UGE,
               functions.bvslt.func: lambda arg1, arg2: arg1 < arg2,
               functions.bvsle.func: lambda arg1, arg2: arg1 <= arg2,
               functions.bvsgt.func: lambda arg1, arg2: arg1 > arg2,
               functions.bvsge.func: lambda arg1, arg2: arg1 >= arg2,
               functions.bvnot.func: lambda arg: ~arg,
               functions.bvneg.func: lambda arg: -arg}
    _z3Consts = {sorts.BitVec: z3.BitVecVal,
                 sorts.Int: z3.IntVal,
                 sorts.Real: z3.RealVal}
    _z3Options = {'produce-models': 'model'}
    _z3Results = {sorts.BitVec: results.Z3BitVecResult,
                  sorts.Int: results.Z3IntResult,
                  sorts.Real: results.Z3RealResult,
                  sorts.Bool: results.Z3BoolResult}

    def __init__(self):
        super().__init__()
        self._solver = self.z3.Solver()

    def reset(self):
        self._solver.reset()

    def check_sat(self):
        # rely on Assert for now
        # chose this way so user can get assertions, but also aren't added twice
        # self._solver.add(self.constraints)
        self.sat = self._solver.check() == self.z3.sat
        return self.sat

    def set_logic(self, logicstr):
        self._solver.set(logic=logicstr)

    def set_option(self, optionstr, value):
        # check if option is defined (some options are always on in z3)
        if optionstr in self._z3Options:
            self.z3.set_param(self._z3Options[optionstr], value)

    def set_nonstandard_option(self, optionstr, value):
        self.z3.set_param(self, optionstr, value)

    def declare_const(self, name, sort):
        z3const = self._z3Sorts[sort.__class__](name, *sort.params)
        # should there be a no-op or just use None?
        const = terms.Z3Term(self, functions.No_op, z3const, [sort])
        return const

    def theory_const(self, sort, value):
        # Note: order of arguments is opposite what I would expect
        # if it becomes a problem, might need to use keywords
        z3tconst = self._z3Consts[sort.__class__](value, *sort.params)
        tconst = terms.Z3Term(self, functions.No_op, z3tconst, [sort])
        return tconst

    # if config strict, check arity of function
    def apply_fun(self, fun, *args):
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        args = fun.args + args

        solver_args = tuple(map(lambda arg:
                               arg.solver_term if isinstance(arg, terms.Z3Term)
                               else arg, args))
        # Some versions of python don't allow fun(*list1, *list2) so combining
        z3expr = self._z3Funs[fun.func](*solver_args)
        expr = terms.Z3Term(self, fun, z3expr, list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            # get z3 terms
            for constraint in constraints:
                sort = getattr(constraint, 'sort', type(constraint))
                if sort != bool and sort != sorts.Bool():
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(sort))
                self._solver.add(getattr(constraint, 'solver_term', constraint))
        else:
            sort = getattr(constraints, 'sort', type(constraints))
            if sort != bool and sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(sort))
            self._solver.add(getattr(constraints, 'solver_term', constraints))

    def assertions(self):
        # had issue with returning an iterable for CVC4
        # thus to keep things consistent, returning a list here
        # it also mimics both z3 and cvc4's normal behavior to use a list
        return [assertion.sexpr() for assertion in self._solver.assertions()]

    def get_model(self):
        if self.sat:
            return self._solver.model()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._z3Results[var.sort.__class__](self._solver.model().eval(var.solver_term))
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

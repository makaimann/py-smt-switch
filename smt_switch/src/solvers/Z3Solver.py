from .. import sorts
from .solverbase import SolverBase


class Z3Solver(SolverBase):
    # import z3
    z3 = __import__('z3')
    _z3Sorts = {sorts.BitVec: z3.BitVec,
                sorts.Int: z3.Int,
                sorts.Real: z3.Real,
                sorts.Bool: z3.Bool}

    _z3Funs = {'Extract': z3.Extract,
               'Concat': z3.Concat,
               'Zero_extend': z3.ZeroExt,
               'Not': z3.Not,
               'Equals': lambda arg1, arg2: arg1 == arg2,
               'And': z3.And,
               'Or': z3.Or,
               'Ite': z3.If,
               'Sub': lambda arg1, arg2: arg1 - arg2,
               'Add': lambda arg1, arg2: arg1 + arg2,
               'LT': lambda arg1, arg2: arg1 < arg2,
               'LEQ': lambda arg1, arg2: arg1 <= arg2,
               'GT': lambda arg1, arg2: arg1 > arg2,
               'GEQ': lambda arg1, arg2: arg1 >= arg2,
               'BVAnd': lambda arg1, arg2: arg1 & arg2,
               'BVOr': lambda arg1, arg2: arg1 | arg2,
               'BVXor': lambda arg1, arg2: arg1 ^ arg2,
               'BVAdd': lambda arg1, arg2: arg1 + arg2,
               'BVSub': lambda arg1, arg2: arg1 - arg2,
               'BVMul': lambda arg1, arg2: arg1*arg2,
               'BVUdiv': z3.UDiv,
               'BVUrem': z3.URem,
               'BVShl': lambda arg1, arg2: arg1 << arg2,
               'BVAshr': lambda arg1, arg2: arg1 >> arg2,
               'BVLshr': z3.LShR,
               'BVUlt': z3.ULT,
               'BVUle': z3.ULE,
               'BVUgt': z3.UGT,
               'BVUge': z3.UGE,
               'BVSlt': lambda arg1, arg2: arg1 < arg2,
               'BVSle': lambda arg1, arg2: arg1 <= arg2,
               'BVSgt': lambda arg1, arg2: arg1 > arg2,
               'BVSge': lambda arg1, arg2: arg1 >= arg2,
               'BVNot': lambda arg: ~arg,
               'BVNeg': lambda arg: -arg}
    _z3Consts = {sorts.BitVec: z3.BitVecVal,
                 sorts.Int: z3.IntVal,
                 sorts.Real: z3.RealVal}
    _z3Options = {'produce-models': 'model'}

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
        return z3const

    def theory_const(self, sort, value):
        # Note: order of arguments is opposite what I would expect
        # if it becomes a problem, might need to use keywords
        z3tconst = self._z3Consts[sort.__class__](value, *sort.params)
        return z3tconst

    # if config strict, check arity of function
    def apply_fun(self, fname, indices, *args):
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        # Some versions of python don't allow fun(*list1, *list2) so combining
        z3expr = self._z3Funs[fname](*(indices + args))
        return z3expr

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
            return self._solver.model().eval(var.solver_term)
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

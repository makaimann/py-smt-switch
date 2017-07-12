from .. import sorts
from ..functions import func_enum
from .solverbase import SolverBase


class Z3Solver(SolverBase):
    # import z3
    z3 = __import__('z3')
    _z3Sorts = {sorts.BitVec: z3.BitVec,
                sorts.Int: z3.Int,
                sorts.Real: z3.Real,
                sorts.Bool: z3.Bool}

    _z3Funs = {func_enum.Extract: z3.Extract,
               func_enum.Concat: z3.Concat,
               func_enum.Zero_extend: z3.ZeroExt,
               func_enum.Not: z3.Not,
               func_enum.Equals: lambda arg1, arg2: arg1 == arg2,
               func_enum.And: z3.And,
               func_enum.Or: z3.Or,
               func_enum.Ite: z3.If,
               func_enum.Sub: lambda arg1, arg2: arg1 - arg2,
               func_enum.Add: lambda arg1, arg2: arg1 + arg2,
               func_enum.LT: lambda arg1, arg2: arg1 < arg2,
               func_enum.LEQ: lambda arg1, arg2: arg1 <= arg2,
               func_enum.GT: lambda arg1, arg2: arg1 > arg2,
               func_enum.GEQ: lambda arg1, arg2: arg1 >= arg2,
               func_enum.BVAnd: lambda arg1, arg2: arg1 & arg2,
               func_enum.BVOr: lambda arg1, arg2: arg1 | arg2,
               func_enum.BVXor: lambda arg1, arg2: arg1 ^ arg2,
               func_enum.BVAdd: lambda arg1, arg2: arg1 + arg2,
               func_enum.BVSub: lambda arg1, arg2: arg1 - arg2,
               func_enum.BVMul: lambda arg1, arg2: arg1*arg2,
               func_enum.BVUdiv: z3.UDiv,
               func_enum.BVUrem: z3.URem,
               func_enum.BVShl: lambda arg1, arg2: arg1 << arg2,
               func_enum.BVAshr: lambda arg1, arg2: arg1 >> arg2,
               func_enum.BVLshr: z3.LShR,
               func_enum.BVUlt: z3.ULT,
               func_enum.BVUle: z3.ULE,
               func_enum.BVUgt: z3.UGT,
               func_enum.BVUge: z3.UGE,
               func_enum.BVSlt: lambda arg1, arg2: arg1 < arg2,
               func_enum.BVSle: lambda arg1, arg2: arg1 <= arg2,
               func_enum.BVSgt: lambda arg1, arg2: arg1 > arg2,
               func_enum.BVSge: lambda arg1, arg2: arg1 >= arg2,
               func_enum.BVNot: lambda arg: ~arg,
               func_enum.BVNeg: lambda arg: -arg}
    _z3Consts = {sorts.BitVec: z3.BitVecVal,
                 sorts.Int: z3.IntVal,
                 sorts.Real: z3.RealVal,
                 sorts.Bool: lambda x: x}
    _z3Options = {'produce-models': 'model'}

    def __init__(self):
        super().__init__()
        self._solver = self.z3.Solver()

    def Reset(self):
        self._solver.Reset()

    def CheckSat(self):
        # rely on Assert for now
        # chose this way so user can get Assertions, but also aren't added twice
        # self._solver.add(self.constraints)
        self.Sat = self._solver.check() == self.z3.sat
        return self.Sat

    def SetLogic(self, logicstr):
        self._solver.set(logic=logicstr)

    def SetOption(self, optionstr, value):
        # check if option is defined (some options are always on in z3)
        if optionstr in self._z3Options:
            self.z3.set_param(self._z3Options[optionstr], value)

    def DeclareConst(self, name, sort):
        z3const = self._z3Sorts[sort.__class__](name, *sort.params)
        # should there be a no-op or just use None?
        return z3const

    def TheoryConst(self, sort, value):
        # Note: order of arguments is opposite what I would expect
        # if it becomes a problem, might need to use keywords
        z3tconst = self._z3Consts[sort.__class__](value, *sort.params)
        return z3tconst

    def ApplyFun(self, f_enum, indices, *args):
        # Some versions of python don't allow fun(*list1, *list2) so combining
        z3expr = self._z3Funs[f_enum](*(indices + args))
        return z3expr

    def Assert(self, c):
        self._solver.add(c)

    def Assertions(self):
        # had issue with returning an iterable for CVC4
        # thus to keep things consistent, returning a list here
        # it also mimics both z3 and cvc4's normal behavior to use a list
        return [assertion.sexpr() for assertion in self._solver.Assertions()]

    def GetModel(self):
        if self.Sat:
            return self._solver.model()
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def GetValue(self, var):
        if self.Sat:
            return self._solver.model().eval(var)
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

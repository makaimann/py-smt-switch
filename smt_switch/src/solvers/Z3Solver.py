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
               func_enum.ZeroExt: z3.ZeroExt,
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

    _z3Funs2swFuns = {z3.Z3_OP_EXTRACT: func_enum.Extract,
                      z3.Z3_OP_CONCAT: func_enum.Concat,
                      z3.Z3_OP_ZERO_EXT: func_enum.ZeroExt,
                      z3.Z3_OP_NOT: func_enum.Not,
                      z3.Z3_OP_EQ: func_enum.Equals,
                      z3.Z3_OP_AND: func_enum.And,
                      z3.Z3_OP_OR: func_enum.Or,
                      z3.Z3_OP_ITE: func_enum.Ite,
                      z3.Z3_OP_SUB: func_enum.Sub,
                      z3.Z3_OP_ADD: func_enum.Add,
                      z3.Z3_OP_LT: func_enum.LT,
                      z3.Z3_OP_LE: func_enum.LEQ,
                      z3.Z3_OP_GT: func_enum.GT,
                      z3.Z3_OP_GE: func_enum.GEQ,
                      z3.Z3_OP_BAND: func_enum.BVAnd,
                      z3.Z3_OP_BOR: func_enum.BVOr,
                      z3.Z3_OP_BXOR: func_enum.BVXor,
                      z3.Z3_OP_BADD: func_enum.BVAdd,
                      z3.Z3_OP_BSUB: func_enum.BVSub,
                      z3.Z3_OP_BMUL: func_enum.BVMul,
                      z3.Z3_OP_BUDIV: func_enum.BVUdiv,
                      z3.Z3_OP_BUREM: func_enum.BVUrem,
                      z3.Z3_OP_BSHL: func_enum.BVShl,
                      z3.Z3_OP_BASHR: func_enum.BVAshr,
                      z3.Z3_OP_BLSHR: func_enum.BVLshr,
                      z3.Z3_OP_ULT: func_enum.BVUlt,
                      z3.Z3_OP_ULEQ: func_enum.BVUle,
                      z3.Z3_OP_UGT: func_enum.BVUgt,
                      z3.Z3_OP_UGEQ: func_enum.BVUge,
                      z3.Z3_OP_SLT: func_enum.BVSlt,
                      z3.Z3_OP_SLEQ: func_enum.BVSle,
                      z3.Z3_OP_SGT: func_enum.BVSgt,
                      z3.Z3_OP_SGEQ: func_enum.BVSge,
                      z3.Z3_OP_BNOT: func_enum.BVNot,
                      z3.Z3_OP_BNEG: func_enum.BVNeg,
                      # Constants are all No_op in smt-switch
                      z3.Z3_OP_UNINTERPRETED: func_enum.No_op,
                      z3.Z3_OP_ANUM: func_enum.No_op,
                      z3.Z3_OP_BNUM: func_enum.No_op}


    _z3Consts = {sorts.BitVec: z3.BitVecVal,
                 sorts.Int: z3.IntVal,
                 sorts.Real: z3.RealVal,
                 sorts.Bool: lambda x: x}
    _z3Options = {'produce-models': 'model',
                  'random-seed': 'smt.random_seed'}

    def __init__(self):
        super().__init__()
        self._solver = self.z3.Solver()

    def Reset(self):
        self._solver.reset()

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
        return [assertion.sexpr() for assertion in self._solver.assertions()]

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

    def ToSmt2(self, filename):
        with open(filename, 'w') as f:
            f.write(self._solver.to_smt2())
            f.close()

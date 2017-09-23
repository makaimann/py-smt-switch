# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from .. import sorts
from ..functions import func_enum
from .solverbase import SolverBase
from smt_switch.util import reversabledict
from collections import Sequence


class Z3Solver(SolverBase):

    def __init__(self, strict):
        super().__init__(strict)

            # import z3
        self.z3 = __import__('z3')

        self._z3Sorts = {sorts.BitVec: self.z3.BitVecSort,
                    sorts.Int: self.z3.IntSort,
                    sorts.Real: self.z3.RealSort,
                    sorts.Bool: self.z3.BoolSort,
                    sorts.Array: self.z3.Z3_ARRAY_SORT,
                    # for going the other way
                    self.z3.Z3_BOOL_SORT: lambda var: sorts.Bool(),
                    self.z3.Z3_INT_SORT: lambda var: sorts.Int(),
                    self.z3.Z3_REAL_SORT: lambda var: sorts.Real(),
                    self.z3.Z3_BV_SORT: lambda var: sorts.BitVec(var.size())}
                    # adding array sort later

        def get_array_sort(var):
            domain_sort = self._z3Sorts[var.domain().kind()](var.domain())
            range_sort = self._z3Sorts[var.range().kind()](var.range())
            return sorts.Array(domain_sort, range_sort)

        self._z3Sorts[self.z3.Z3_ARRAY_SORT] = get_array_sort

        # function used to create array
        def create_array(name, idxsort, dsort):
            # need to recover parameterized sorts
            z3_idxsort = self._z3Sorts[idxsort.__class__](*idxsort.params)
            z3_dsort = self._z3Sorts[dsort.__class__](*dsort.params)
            return self.z3.Array(name, z3_idxsort, z3_dsort)

        self._z3sorts2var = {sorts.BitVec: self.z3.BitVec,
                        sorts.Int: self.z3.Int,
                        sorts.Real: self.z3.Real,
                        sorts.Bool: self.z3.Bool,
                        sorts.Array: create_array}

        self._z3Funs = {func_enum.Extract: self.z3.Extract,
                   func_enum.Concat: self.z3.Concat,
                   func_enum.ZeroExt: self.z3.ZeroExt,
                   func_enum.Not: self.z3.Not,
                   func_enum.Equals: lambda arg1, arg2: arg1 == arg2,
                   func_enum.And: self.z3.And,
                   func_enum.Or: self.z3.Or,
                   func_enum.Ite: self.z3.If,
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
                   func_enum.BVUdiv: self.z3.UDiv,
                   func_enum.BVUrem: self.z3.URem,
                   func_enum.BVShl: lambda arg1, arg2: arg1 << arg2,
                   func_enum.BVAshr: lambda arg1, arg2: arg1 >> arg2,
                   func_enum.BVLshr: self.z3.LShR,
                   func_enum.BVUlt: self.z3.ULT,
                   func_enum.BVUle: self.z3.ULE,
                   func_enum.BVUgt: self.z3.UGT,
                   func_enum.BVUge: self.z3.UGE,
                   func_enum.BVSlt: lambda arg1, arg2: arg1 < arg2,
                   func_enum.BVSle: lambda arg1, arg2: arg1 <= arg2,
                   func_enum.BVSgt: lambda arg1, arg2: arg1 > arg2,
                   func_enum.BVSge: lambda arg1, arg2: arg1 >= arg2,
                   func_enum.BVNot: lambda arg: ~arg,
                   func_enum.BVNeg: lambda arg: -arg,
                   func_enum.Store: self.z3.Store,
                   func_enum.Select: self.z3.Select}

        self._z3Funs2swFuns = {self.z3.Z3_OP_EXTRACT: func_enum.Extract,
                          self.z3.Z3_OP_CONCAT: func_enum.Concat,
                          self.z3.Z3_OP_ZERO_EXT: func_enum.ZeroExt,
                          self.z3.Z3_OP_NOT: func_enum.Not,
                          self.z3.Z3_OP_EQ: func_enum.Equals,
                          self.z3.Z3_OP_AND: func_enum.And,
                          self.z3.Z3_OP_OR: func_enum.Or,
                          self.z3.Z3_OP_ITE: func_enum.Ite,
                          self.z3.Z3_OP_SUB: func_enum.Sub,
                          self.z3.Z3_OP_ADD: func_enum.Add,
                          self.z3.Z3_OP_LT: func_enum.LT,
                          self.z3.Z3_OP_LE: func_enum.LEQ,
                          self.z3.Z3_OP_GT: func_enum.GT,
                          self.z3.Z3_OP_GE: func_enum.GEQ,
                          self.z3.Z3_OP_BAND: func_enum.BVAnd,
                          self.z3.Z3_OP_BOR: func_enum.BVOr,
                          self.z3.Z3_OP_BXOR: func_enum.BVXor,
                          self.z3.Z3_OP_BADD: func_enum.BVAdd,
                          self.z3.Z3_OP_BSUB: func_enum.BVSub,
                          self.z3.Z3_OP_BMUL: func_enum.BVMul,
                          self.z3.Z3_OP_BUDIV: func_enum.BVUdiv,
                          self.z3.Z3_OP_BUREM: func_enum.BVUrem,
                          self.z3.Z3_OP_BSHL: func_enum.BVShl,
                          self.z3.Z3_OP_BASHR: func_enum.BVAshr,
                          self.z3.Z3_OP_BLSHR: func_enum.BVLshr,
                          self.z3.Z3_OP_ULT: func_enum.BVUlt,
                          self.z3.Z3_OP_ULEQ: func_enum.BVUle,
                          self.z3.Z3_OP_UGT: func_enum.BVUgt,
                          self.z3.Z3_OP_UGEQ: func_enum.BVUge,
                          self.z3.Z3_OP_SLT: func_enum.BVSlt,
                          self.z3.Z3_OP_SLEQ: func_enum.BVSle,
                          self.z3.Z3_OP_SGT: func_enum.BVSgt,
                          self.z3.Z3_OP_SGEQ: func_enum.BVSge,
                          self.z3.Z3_OP_BNOT: func_enum.BVNot,
                          self.z3.Z3_OP_BNEG: func_enum.BVNeg,
                          # Constants are all No_op in smt-switch
                          self.z3.Z3_OP_FALSE: func_enum.No_op,
                          self.z3.Z3_OP_TRUE: func_enum.No_op,
                          self.z3.Z3_OP_UNINTERPRETED: func_enum.No_op,
                          self.z3.Z3_OP_ANUM: func_enum.No_op,
                          self.z3.Z3_OP_BNUM: func_enum.No_op,
                          self.z3.Z3_OP_STORE: func_enum.Store,
                          self.z3.Z3_OP_SELECT: func_enum.Select}


        self._z3Consts = {sorts.BitVec: self.z3.BitVecVal,
                     sorts.Int: self.z3.IntVal,
                     sorts.Real: self.z3.RealVal,
                     sorts.Bool: lambda x: x}
        self._z3Options = {'produce-models': 'model',
                      'random-seed': 'smt.random_seed'}


        # this attribute is used by an inherited function to translate sorts
        self._tosorts = self._z3Sorts
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

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a non-empty list of input sorts"

        sortlist = [self._z3Sorts[sort.__class__](*sort.params)
                        for sort in inputsorts]
        sortlist.append(self._z3Sorts[outputsort.__class__](*outputsort.params))
        return self.z3.Function(name, *sortlist)

    def DeclareConst(self, name, sort):
        z3const = self._z3sorts2var[sort.__class__](name, *sort.params)
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

    def ApplyCustomFun(self, func, *args):
        return func(*args)

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

    def Symbol(self, name, sort):
        raise NotImplementedError("Z3 does not support symbols for function macros through the API.")

    def DefineFun(self, name, sortlist, paramlist, fundef):
        raise NotImplementedError("Z3 does not support the define-fun macro through the API.")

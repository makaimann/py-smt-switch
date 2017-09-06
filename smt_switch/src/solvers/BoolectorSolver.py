from .. import sorts
from .solverbase import SolverBase
from functools import reduce
from ..functions import func_enum
from collections import Sequence


class BoolectorSolver(SolverBase):
    def __init__(self):
        super().__init__()
        
        self.boolector = __import__('boolector')
        self._btor = self.boolector.Boolector()

        # keeping track of Assertions because couldn't figure out
        # how to print a list of Assertions (other than dumping to stdout/a file)
        self._Assertions = []

        self._BoolectorSorts = {sorts.BitVec: self._btor.BitVecSort,
                                sorts.Bool: lambda: self._btor.BitVecSort(1)}
        self._BoolectorFuns = {func_enum.Equals: self._btor.Eq,
                               func_enum.And: self.And,
                               func_enum.Or: self.Or,
                               func_enum.Ite: self._btor.Cond,
                               func_enum.Not: self._btor.Not,
                               func_enum.Extract: self._btor.Slice,
                               func_enum.Concat: self._btor.Concat,
                               func_enum.BVAnd: self._btor.And,
                               func_enum.BVOr: self._btor.Or,
                               func_enum.BVXor: self._btor.Xor,
                               func_enum.BVAdd: self._btor.Add,
                               func_enum.BVSub: self._btor.Sub,
                               func_enum.BVMul: self._btor.Mul,
                               func_enum.BVUdiv: self._btor.Udiv,
                               func_enum.BVUrem: self._btor.Urem,
                               func_enum.BVShl: self.Sll,
                               func_enum.BVAshr: self.Sra,
                               func_enum.BVLshr: self.Srl,
                               func_enum.BVUlt: self._btor.Ult,
                               func_enum.BVUle: self._btor.Ulte,
                               func_enum.BVUgt: self._btor.Ugt,
                               func_enum.BVUge: self._btor.Ugte,
                               func_enum.BVSlt: self._btor.Slt,
                               func_enum.BVSle: self._btor.Slte,
                               func_enum.BVSgt: self._btor.Sgt,
                               func_enum.BVSge: self._btor.Sgte,
                               func_enum.BVNot: self._btor.Not,
                               func_enum.BVNeg: self._btor.Neg}

        self._BoolectorConsts = {sorts.BitVec: self._btor.Const,
                                 sorts.Bool: self._btor.Const}
        # Note: Boolector does not distinguish between Bools and (_ BitVec 1)
        #       so smt_switch is not either (specifically for Boolector)
        # self._BoolectorResults = {sorts.BitVec: results.BoolectorBitVecResult,
        #                           sorts.Bool: results.BoolectorBitVecResult}
        self._BoolectorOptions = {'produce-models': self.boolector.BTOR_OPT_MODEL_GEN,
                                  'random-seed': self.boolector.BTOR_OPT_SEED}

        # am I missing any?
        self._BoolectorLogics = ['QF_BV', 'QF_ABV', 'QF_UFBV']

    def Reset(self):
        self.__init__()

    def CheckSat(self):
        if self._btor.Sat() == self._btor.SAT:
            self.Sat = True
        else:
            self.Sat = False
        return self.Sat

    def SetLogic(self, logicstr):
        if logicstr not in self._BoolectorLogics:
            raise ValueError('Boolector does not support {} '.format(logicstr) +
                             'If you believe this is incorrect, please contact a ' +
                             'developer or modify the class yourself (see _BoolectorLogics)')

    def SetOption(self, optionstr, value):
        if optionstr in self._BoolectorOptions:
            self._btor.Set_opt(self._BoolectorOptions[optionstr], bool(value))

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a non-empty list of input sorts"

        btorisorts = [self._BoolectorSorts[sort.__class__](*sort.params)
                          for sort in inputsorts]

        btorosort = self._BoolectorSorts[outputsort.__class__](*outputsort.params)
        _funsort = self._btor.FunSort(btorisorts, btorosort)
        return self._btor.UF(_funsort)

    def DeclareConst(self, name, sort):
        btorsort = self._BoolectorSorts[sort.__class__](*sort.params)
        btorconst = self._btor.Var(btorsort, name)
        return btorconst

    def TheoryConst(self, sort, value):
        btortconst = self._BoolectorConsts[sort.__class__](*((value,) + sort.params))
        return btortconst

    def ApplyFun(self, f_enum, indices, *args):
        btor_expr = self._BoolectorFuns[f_enum](*(args + indices))
        return btor_expr

    def ApplyCustomFun(self, func, *args):
        '''
           Apply a custom function. Don't need to look up corresponding function
           -- assume func is a Boolector function.
        '''
        btor_expr = self._btor.Apply(list(args), func)
        return btor_expr

    def Assert(self, c):
        self._btor.Assert(c)

    def Assertions(self):
        return self._Assertions

    def GetModel(self):
        if self.Sat:
            return self._btor.Print_model()
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def GetValue(self, var):
        if self.Sat:
            # The value will be wrapped at the api level
            return var
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def ToSmt2(self, filename):
        self._btor.Dump(format="smt2", outfile=filename)

    def Symbol(self, name, sort):
        btorsort = self._BoolectorSorts[sort.__class__](*sort.params)
        btorsym = self._btor.Param(btorsort, name)
        return btorsym

    def DefineFun(self, name, sortlist, paramlist, fundef):
        return self._btor.Fun(paramlist, fundef)

    # extra functions specific to Boolector
    # And requires exactly two arguments in Boolector.
    # creating a reduction for ease of use
    def And(self, *args):
        if isinstance(args[0], list):
            args = args[0]

        result = reduce(lambda x, y: self._btor.And(x, y), args)
        return result

    def Or(self, *args):
        if isinstance(args[0], list):
            args = args[0]

        result = reduce(lambda x, y: self._btor.Or(x, y), args)
        return result

    def Sll(self, bv, shift):
        if not isinstance(shift, int):
            shift = int(shift.bits, base=2)
        slice_bv = bv[bv.width-1-shift:]
        zeros = self._btor.Const(0, shift)
        return self._btor.Concat(slice_bv, zeros)

    def Srl(self, bv, shift):
        if not isinstance(shift, int):
            shift = int(shift.bits, base=2)
        slice_bv = bv[:shift]
        zeros = self._btor.Const(0, shift)
        return self._btor.Concat(zeros, slice_bv)

    def Sra(self, bv, shift):
        if not isinstance(shift, int):
            shift = int(shift.bits, base=2)
        slice_bv = bv[:shift]
        zeros = self._btor.Const(0, shift)
        ones = self._btor.Const('1'*shift)
        msb = bv[bv.width-1:bv.width-1]
        ones_concat = self._btor.Concat(ones, slice_bv)
        zeros_concat = self._btor.Concat(zeros, slice_bv)
        return self._btor.Cond(msb == 0b1, ones_concat, zeros_concat)

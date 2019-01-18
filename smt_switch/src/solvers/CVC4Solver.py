# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from .. import sorts
from ..functions import func_enum
from .solverbase import SolverBase
from fractions import Fraction
from smt_switch.util import reversabledict
from collections import Sequence
import os


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?

    def __init__(self, strict):
        super().__init__(strict)

        opts = self.module.Options()
        opts.setOutputLanguage(self.module.OUTPUT_LANG_SMTLIB_V2_5)
        self._em = self.module.ExprManager(opts)

        self._smt = self.module.SmtEngine(self._em)
        self.temp_file_name = "cvc4-out.smt2"
        self._smt.setOption("dump-to", self.module.SExpr(self.temp_file_name))
        self._smt.setOption("dump", self.module.SExpr("raw-benchmark"))

        self._CVC4Sorts = {sorts.BitVec: self._em.mkBitVectorType,
                           sorts.Int: self._em.integerType,
                           sorts.Real: self._em.realType,
                           sorts.Bool: self._em.booleanType,
                           sorts.Array: self._em.mkArrayType}

        # def create_array_sort(idxsort, dsort):
        #     # get parameterized sorts
        #     cvc4_idxsort = self._CVC4Sorts[idxsort.__class__](*idxsort.params)
        #     cvc4_dsort = self._CVC4Sorts[dsort.__class__](*dsort.params)
        #     return self._em.mkArrayType(cvc4_idxsort, cvc4_dsort)

        # self._CVC4Sorts[sorts.Array] = create_array_sort

        # this attribute is used by an inherited function to translate sorts
        self._tosorts = self._CVC4Sorts

        self._CVC4Funs = \
          reversabledict({func_enum.Extract: self.module.BitVectorExtract,
                          func_enum.Concat: self.module.BITVECTOR_CONCAT,
                          func_enum.ZeroExt: self.module.BITVECTOR_ZERO_EXTEND,
                          func_enum.Equals: self.module.EQUAL,
                          func_enum.Not: self.module.NOT,
                          func_enum.And: self.module.AND,
                          func_enum.Or: self.module.OR,
                          func_enum.Ite: self.module.ITE,
                          func_enum.Sub: self.module.MINUS,
                          func_enum.Add: self.module.PLUS,
                          func_enum.LT: self.module.LT,
                          func_enum.LEQ: self.module.LEQ,
                          func_enum.GT: self.module.GT,
                          func_enum.GEQ: self.module.GEQ,
                          func_enum.BVAnd: self.module.BITVECTOR_AND,
                          func_enum.BVOr: self.module.BITVECTOR_OR,
                          func_enum.BVXor: self.module.BITVECTOR_XOR,
                          func_enum.BVAdd: self.module.BITVECTOR_PLUS,
                          func_enum.BVSub: self.module.BITVECTOR_SUB,
                          func_enum.BVMul: self.module.BITVECTOR_MULT,
                          func_enum.BVUdiv: self.module.BITVECTOR_UDIV,
                          func_enum.BVUrem: self.module.BITVECTOR_UREM,
                          func_enum.BVShl: self.module.BITVECTOR_SHL,
                          func_enum.BVAshr: self.module.BITVECTOR_ASHR,
                          func_enum.BVLshr: self.module.BITVECTOR_LSHR,
                          func_enum.BVUlt: self.module.BITVECTOR_ULT,
                          func_enum.BVUle: self.module.BITVECTOR_ULE,
                          func_enum.BVUgt: self.module.BITVECTOR_UGT,
                          func_enum.BVUge: self.module.BITVECTOR_UGE,
                          func_enum.BVSlt: self.module.BITVECTOR_SLT,
                          func_enum.BVSle: self.module.BITVECTOR_SLE,
                          func_enum.BVSgt: self.module.BITVECTOR_SGT,
                          func_enum.BVSge: self.module.BITVECTOR_SGE,
                          func_enum.BVNot: self.module.BITVECTOR_NOT,
                          func_enum.BVNeg: self.module.BITVECTOR_NEG,
                          func_enum._ApplyUF: self.module.APPLY_UF,
                          func_enum.Select: self.module.SELECT,
                          func_enum.Store: self.module.STORE,
                          func_enum.Distinct: self.module.DISTINCT
          })

        # all constants are No_op
        self._CVC4InvOps = {self.module.VARIABLE: func_enum.No_op,
                            self.module.CONST_RATIONAL: func_enum.No_op,
                            self.module.CONST_BITVECTOR: func_enum.No_op,
                            self.module.CONST_BOOLEAN: func_enum.No_op,
                            self.module.BOUND_VARIABLE: func_enum.No_op,
                            # Note: losing info about op of applied function
                            # TODO: see if can extract function definition
                            self.module.APPLY: func_enum.No_op,
                            self.module.BITVECTOR_EXTRACT: func_enum.Extract}

        # Theory constant functions
        def create_bv(width, value):
            return self._em.mkConst(self.module.BitVector(width, value))

        def create_int(value):
            return self._em.mkConst(self.module.Rational(value))

        def create_real(value):
            if not isinstance(value, Fraction):
                value = Fraction(value).limit_denominator()
            return self._em.mkConst(self.module.Rational(value.numerator, value.denominator))

        def create_bool(value):
            return self._em.mkBoolConst(value)

        self._CVC4Consts = {sorts.BitVec: create_bv,
                            sorts.Int: create_int,
                            sorts.Real: create_real,
                            sorts.Bool: create_bool}

    @classmethod
    def _import_func(cls):
        return __import__('CVC4')

    def Reset(self):
        self._smt.reset()
        self._smt.setOption("dump-to", self.module.SExpr(self.temp_file_name))
        self._smt.setOption("dump", self.module.SExpr("raw-benchmark"))


    def CheckSat(self):
        # rely on Assert for now
        # chose this way so user can get Assertions, but also aren't added twice
        # for constraint in self.constraints:
        #    self._smt.assertFormula(constraint)
        self.Sat = self._smt.checkSat().isSat() == 1
        return self.Sat

    def SetLogic(self, logicstr):
        self._smt.setLogic(logicstr)

    def SetOption(self, optionstr, value):
        self._smt.setOption(optionstr, self.module.SExpr(value))

    def DeclareFun(self, name, inputsorts, outputsort):
        assert isinstance(inputsorts, Sequence), \
          "Expecting a non-empty list of input sorts"

        cvc4sorts = [self._translate_sorts(sort) for sort in inputsorts]
        outsort = self._translate_sorts(outputsort)

        funtype = self._em.mkFunctionType(cvc4sorts, outsort)
        lam = self._em.mkVar(name, funtype)
        return lam

    def DeclareConst(self, name, sort):
        cvc4sort = self._translate_sorts(sort)
        cvc4const = self._em.mkVar(name, cvc4sort)
        return cvc4const

    def TheoryConst(self, sort, value):
        cvc4tconst = self._CVC4Consts[sort.__class__](*(sort.params + (value,)))
        return cvc4tconst

    def ApplyFun(self, f_enum, indices, *args):

        if f_enum not in self._CVC4Funs:
            raise NotImplementedError("{} has not been implemented in CVC4 yet".format(f_enum))

        cvc4fun = self._CVC4Funs[f_enum]

        # check if just indexer or needs to be evaluated
        # TODO: handle situation where all args together
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*indices))
        cvc4expr = self._em.mkExpr(cvc4fun, args)
        return cvc4expr

    def ApplyCustomFun(self, func, *args):
        '''
           Apply a custom function. Don't need to look up corresponding function
           -- assume func is a CVC4 function.
        '''
        if self._smt.isDefinedFunction(func):
            cvc4expr = self._em.mkExpr(self.module.APPLY, func, *args)
        else:
            cvc4expr = self._em.mkExpr(func, *args)

        return cvc4expr

    def Assert(self, c):
            self._smt.assertFormula(c)

    def Assertions(self):
        # TODO: fix iter error
        # Wanted these to be an iter but CVC4 threw an exception
        return [expr.toString() for expr in self._smt.getAssertions()]

    def GetModel(self):
        if self.Sat:
            # TODO: Fix this
            return self._smt.getValue
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def GetValue(self, var):
        if self.Sat:
            return self._smt.getValue(var)
        elif self.Sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def ToSmt2(self, filename):
        wd = os.getcwd()
        os.rename(os.getcwd() + "/" + self.temp_file_name, filename)

    def Symbol(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        return self._em.mkBoundVar(name, cvc4sort)

    def DefineFun(self, name, sortlist, paramlist, fundef):
        cvc4sorts = [self._CVC4Sorts[sort.__class__](*sort.params)
                         for sort in sortlist]
        outsort = cvc4sorts[-1]
        cvc4sorts = cvc4sorts[:-1]
        funtype = self._em.mkFunctionType(cvc4sorts, outsort)
        lam = self._em.mkVar(name, funtype)
        self._smt.defineFunction(lam, paramlist, fundef)
        return lam

    def Push(self):
        self._smt.push()

    def Pop(self):
        self._smt.pop()

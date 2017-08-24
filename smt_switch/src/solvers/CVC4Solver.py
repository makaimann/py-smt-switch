from .. import sorts
from ..functions import func_enum
from .solverbase import SolverBase
from fractions import Fraction
from smt_switch.config import config
from smt_switch.util import reversabledict


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?

    def __init__(self, lang='auto'):
        super().__init__()

        # import CVC4
        self.CVC4 = __import__('CVC4')
        # set output language to smt2.5
        if config.strict:
            opts = self.CVC4.Options()
            opts.setOutputLanguage(eval('self.CVC4.OUTPUT_LANG_SMTLIB_V2_5'))
            self._em = self.CVC4.ExprManager(opts)
        else:
            self._em = self.CVC4.ExprManager()
        self._smt = self.CVC4.SmtEngine(self._em)
        self._CVC4Sorts = {sorts.BitVec: self._em.mkBitVectorType,
                           sorts.Int: self._em.integerType,
                           sorts.Real: self._em.realType,
                           sorts.Bool: self._em.booleanType}

        self._CVC4Funs = \
          reversabledict({func_enum.Extract: self.CVC4.BitVectorExtract,
                          func_enum.Concat: self.CVC4.BITVECTOR_CONCAT,
                          func_enum.ZeroExt: self.CVC4.BITVECTOR_ZERO_EXTEND,
                          func_enum.Equals: self.CVC4.EQUAL,
                          func_enum.Not: self.CVC4.NOT,
                          func_enum.And: self.CVC4.AND,
                          func_enum.Or: self.CVC4.OR,
                          func_enum.Ite: self.CVC4.ITE,
                          func_enum.Sub: self.CVC4.MINUS,
                          func_enum.Add: self.CVC4.PLUS,
                          func_enum.LT: self.CVC4.LT,
                          func_enum.LEQ: self.CVC4.LEQ,
                          func_enum.GT: self.CVC4.GT,
                          func_enum.GEQ: self.CVC4.GEQ,
                          func_enum.BVAnd: self.CVC4.BITVECTOR_AND,
                          func_enum.BVOr: self.CVC4.BITVECTOR_OR,
                          func_enum.BVXor: self.CVC4.BITVECTOR_XOR,
                          func_enum.BVAdd: self.CVC4.BITVECTOR_PLUS,
                          func_enum.BVSub: self.CVC4.BITVECTOR_SUB,
                          func_enum.BVMul: self.CVC4.BITVECTOR_MULT,
                          func_enum.BVUdiv: self.CVC4.BITVECTOR_UDIV,
                          func_enum.BVUrem: self.CVC4.BITVECTOR_UREM,
                          func_enum.BVShl: self.CVC4.BITVECTOR_SHL,
                          func_enum.BVAshr: self.CVC4.BITVECTOR_ASHR,
                          func_enum.BVLshr: self.CVC4.BITVECTOR_LSHR,
                          func_enum.BVUlt: self.CVC4.BITVECTOR_ULT,
                          func_enum.BVUle: self.CVC4.BITVECTOR_ULE,
                          func_enum.BVUgt: self.CVC4.BITVECTOR_UGT,
                          func_enum.BVUge: self.CVC4.BITVECTOR_UGE,
                          func_enum.BVSlt: self.CVC4.BITVECTOR_SLT,
                          func_enum.BVSle: self.CVC4.BITVECTOR_SLE,
                          func_enum.BVSgt: self.CVC4.BITVECTOR_SGT,
                          func_enum.BVSge: self.CVC4.BITVECTOR_SGE,
                          func_enum.BVNot: self.CVC4.BITVECTOR_NOT,
                          func_enum.BVNeg: self.CVC4.BITVECTOR_NEG})

        # all constants are No_op
        self._CVC4InvOps = {self.CVC4.VARIABLE: func_enum.No_op,
                            self.CVC4.CONST_RATIONAL: func_enum.No_op,
                            self.CVC4.CONST_BITVECTOR: func_enum.No_op,
                            self.CVC4.BITVECTOR_EXTRACT: func_enum.Extract}

        # Theory constant functions
        def create_bv(width, value):
            return self._em.mkConst(self.CVC4.BitVector(width, value))

        def create_int(value):
            return self._em.mkConst(self.CVC4.Rational(value))

        def create_real(value):
            if not isinstance(value, Fraction):
                value = Fraction(value).limit_denominator()
            return self._em.mkConst(self.CVC4.Rational(value.numerator, value.denominator))

        def create_bool(value):
            return self._em.mkBoolConst(value)

        self._CVC4Consts = {sorts.BitVec: create_bv,
                            sorts.Int: create_int,
                            sorts.Real: create_real,
                            sorts.Bool: create_bool}

    def Reset(self):
        self._smt.Reset()

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
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    def DeclareConst(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        cvc4const = self._em.mkVar(name, cvc4sort)
        return cvc4const

    def TheoryConst(self, sort, value):
        cvc4tconst = self._CVC4Consts[sort.__class__](*(sort.params + (value,)))
        return cvc4tconst

    # if config strict, check arity and don't allow python objects as arguments
    def ApplyFun(self, f_enum, indices, *args):

        cvc4fun = self._CVC4Funs[f_enum]

        # check if just indexer or needs to be evaluated
        # TODO: handle situation where all args together
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*indices))
        cvc4expr = self._em.mkExpr(cvc4fun, args)
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

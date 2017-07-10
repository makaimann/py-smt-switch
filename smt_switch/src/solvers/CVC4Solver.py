from .. import sorts
from .solverbase import SolverBase
from fractions import Fraction
from smt_switch.config import config


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

        self._CVC4Funs = {'Extract': self.CVC4.BitVectorExtract,
                          'Concat': self.CVC4.BITVECTOR_CONCAT,
                          'Zero_extend': self.CVC4.BITVECTOR_ZERO_EXTEND,
                          'Equals': self.CVC4.EQUAL,
                          'Not': self.CVC4.NOT,
                          'And': self.CVC4.AND,
                          'Or': self.CVC4.OR,
                          'Ite': self.CVC4.ITE,
                          'Sub': self.CVC4.MINUS,
                          'Add': self.CVC4.PLUS,
                          'LT': self.CVC4.LT,
                          'LEQ': self.CVC4.LEQ,
                          'GT': self.CVC4.GT,
                          'GEQ': self.CVC4.GEQ,
                          'BVAnd': self.CVC4.BITVECTOR_AND,
                          'BVOr': self.CVC4.BITVECTOR_OR,
                          'BVXor': self.CVC4.BITVECTOR_XOR,
                          'BVAdd': self.CVC4.BITVECTOR_PLUS,
                          'BVSub': self.CVC4.BITVECTOR_SUB,
                          'BVMul': self.CVC4.BITVECTOR_MULT,
                          'BVUdiv': self.CVC4.BITVECTOR_UDIV,
                          'BVUrem': self.CVC4.BITVECTOR_UREM,
                          'BVShl': self.CVC4.BITVECTOR_SHL,
                          'BVAshr': self.CVC4.BITVECTOR_ASHR,
                          'BVLshr': self.CVC4.BITVECTOR_LSHR,
                          'BVUlt': self.CVC4.BITVECTOR_ULT,
                          'BVUle': self.CVC4.BITVECTOR_ULE,
                          'BVUgt': self.CVC4.BITVECTOR_UGT,
                          'BVUge': self.CVC4.BITVECTOR_UGE,
                          'BVSlt': self.CVC4.BITVECTOR_SLT,
                          'BVSle': self.CVC4.BITVECTOR_SLE,
                          'BVSgt': self.CVC4.BITVECTOR_SGT,
                          'BVSge': self.CVC4.BITVECTOR_SGE,
                          'BVNot': self.CVC4.BITVECTOR_NOT,
                          'BVNeg': self.CVC4.BITVECTOR_NEG}

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

    def reset(self):
        self._smt.reset()

    def check_sat(self):
        # rely on Assert for now
        # chose this way so user can get assertions, but also aren't added twice
        # for constraint in self.constraints:
        #    self._smt.assertFormula(constraint)
        self.sat = self._smt.checkSat().isSat() == 1
        return self.sat

    def set_logic(self, logicstr):
        self._smt.setLogic(logicstr)

    # TODO: Need to make this more general.
    # I don't think we always create an SExpr from the value...
    # Also need to check if optionstr is a standard option
    def set_option(self, optionstr, value):
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    # Note: currently not different than set_option
    def set_nonstandard_option(self, optionstr, value):
        self._smt.setOption(optionstr, self.CVC4.SExpr(value))

    def declare_const(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        cvc4const = self._em.mkVar(name, cvc4sort)
        return cvc4const

    def theory_const(self, sort, value):
        cvc4tconst = self._CVC4Consts[sort.__class__](*(sort.params + (value,)))
        return cvc4tconst

    # if config strict, check arity and don't allow python objects as arguments
    def apply_fun(self, fname, indices, *args):

        # commented out while updating functions
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        cvc4fun = self._CVC4Funs[fname]

        # if config.strict:
        #     solver_args = [arg.solver_term for arg in args]
        # else:
        #     # find a cvc4 term to infer the sort
        #     # TODO: make this more robust
        #     cvc4term = list(filter(lambda x: isinstance(x, terms.CVC4Term), args))[-1]
        #     solver_args = tuple(map(lambda arg: arg.solver_term
        #                             if isinstance(arg, terms.CVC4Term)
        #                             else
        #                             self.theory_const(cvc4term.sort, arg).solver_term,
        #                             args))

        # check if just indexer or needs to be evaluated
        # TODO: handle situation where all args together
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*indices))
        cvc4expr = self._em.mkExpr(cvc4fun, args)
        return cvc4expr

    def Assert(self, c):
            self._smt.assertFormula(c)

    def assertions(self):
        # TODO: fix iter error
        # Wanted these to be an iter but CVC4 threw an exception
        return [expr.toString() for expr in self._smt.getAssertions()]

    def get_model(self):
        if self.sat:
            # TODO: Fix this
            return self._smt.getValue
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._smt.getValue(var)
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

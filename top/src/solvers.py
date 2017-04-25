from abc import ABCMeta, abstractmethod, abstractproperty
import CVC4
import z3
from src import sorts
from src import functions
from src import terms
from fractions import Fraction
from config import config


class SolverBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self):
        self.constraints = []
        self.sat = None

    def add(self, c):
        self.constraints.append(c)

    def reset(self):
        self.constraints = []
        self.sat = None

    @abstractmethod
    def check_sat(self):
        pass

    @abstractmethod
    def set_logic(self, logicstr):
        pass

    @abstractmethod
    def set_option(self, optionstr, value):
        pass

    # right now this doesn't do anything different than set_option in CVC4 implementation
    # because not doing any checks on optionstr in set_option yet
    @abstractmethod
    def set_nonstandard_option(self, optionstr, value):
        pass

    @abstractmethod
    def declare_const(self, name, sort):
        pass

    @abstractmethod
    def theory_const(self, sort, value):
        pass

    @abstractmethod
    def apply_fun(self, fun, *args):
        pass

    @abstractmethod
    def Assert(cls, *pargs, **kwargs):
        return cls.Assert(*pargs, **kwargs)

    @abstractproperty
    def assertions(self):
        pass

    @abstractmethod
    def get_model(self):
        pass

    @abstractmethod
    def get_value(self, var):
        pass


class Z3Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?
    _z3Sorts = {sorts.BitVec: z3.BitVec,
                sorts.Int: z3.Int,
                sorts.Real: z3.Real,
                sorts.Bool: z3.Bool}
    _z3Funs = {functions.extract: z3.Extract,
               functions.Not: z3.Not,
               functions.Equals: lambda arg1, arg2: arg1 == arg2,
               functions.And: z3.And,
               functions.Or: z3.Or,
               functions.Ite: z3.If,
               functions.Sub: lambda arg1, arg2: arg1 - arg2,
               functions.Plus: lambda arg1, arg2: arg1 + arg2,
               functions.LT: lambda arg1, arg2: arg1 < arg2,
               functions.LEQ: lambda arg1, arg2: arg1 <= arg2,
               functions.GT: lambda arg1, arg2: arg1 > arg2,
               functions.GEQ: lambda arg1, arg2: arg1 >= arg2,
               functions.bvand: lambda arg1, arg2: arg1 & arg2,
               functions.bvor: lambda arg1, arg2: arg1 | arg2,
               functions.bvadd: lambda arg1, arg2: arg1 + arg2,
               functions.bvmul: lambda arg1, arg2: arg1*arg2,
               functions.bvudiv: z3.UDiv,
               functions.bvurem: z3.URem,
               functions.bvshl: lambda arg1, arg2: arg1 << arg2,
               functions.bvlshr: z3.LShR,
               functions.bvnot: lambda arg: ~arg,
               functions.bvneg: lambda arg: -arg}
    _z3Consts = {sorts.BitVec: z3.BitVecVal,
                 sorts.Int: z3.IntVal,
                 sorts.Real: z3.RealVal}
    _z3Options = {'produce-models': 'model'}

    def __init__(self):
        super().__init__()
        self._solver = z3.Solver()

    def check_sat(self):
        # rely on Assert for now
        # chose this way so user can get assertions, but also aren't added twice
        # self._solver.add(self.constraints)
        self.sat = self._solver.check() == z3.sat
        return self.sat

    def set_logic(self, logicstr):
        self._solver.set(logic=logicstr)

    def set_option(self, optionstr, value):
        # check if option is defined (some options are always on in z3)
        if optionstr in self._z3Options:
            z3.set_param(self._z3Options[optionstr], value)

    def set_nonstandard_option(self, optionstr, value):
        z3.set_param(self, optionstr, value)

    def declare_const(self, name, sort):
        z3const = self._z3Sorts[sort.__class__](name, *sort.params)
        # should there be a no-op or just use None?
        const = terms.Z3Term(self, functions.No_op, z3const, sort, [])
        return const

    def theory_const(self, sort, value):
        # Note: order of arguments is opposite what I would expect
        # if it becomes a problem, might need to use keywords
        z3tconst = self._z3Consts[sort.__class__](value, *sort.params)
        tconst = terms.Z3Term(self, functions.No_op, z3tconst, sort, [])
        return tconst

    # if config strict, check arity of function
    def apply_fun(self, fun, *args):
        if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
            raise ValueError('In strict mode you must respect function arity:' +
                             ' {}: arity = {}'.format(fun, fun.arity))

        solver_args = list(map(lambda arg:
                               arg.solver_term if isinstance(arg, terms.Z3Term)
                               else arg, args))
        z3expr = self._z3Funs[fun.__class__](*fun.params, *solver_args)
        expr = terms.Z3Term(self, fun, z3expr, fun.osort(*args), list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            # get z3 termss
            for constraint in constraints:
                if constraint.sort != 'Bool':
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(constraint.sort))
                self._solver.add(constraints)
        else:
            if constraints.sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(constraints.sort))
            self._solver.add(constraints.solver_term)

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
            if config.strict:
                return self._solver.model().eval(var.solver_term).sexpr()
            else:
                return self._solver.model().eval(var.solver_term).__repr__()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?

    def __init__(self, lang='auto'):
        super().__init__()
        # set output language to smt2.5
        if config.strict:
            opts = CVC4.Options()
            opts.setOutputLanguage(eval('CVC4.OUTPUT_LANG_SMTLIB_V2_5'))
            self._em = CVC4.ExprManager(opts)
        else:
            self._em = CVC4.ExprManager()
        self._smt = CVC4.SmtEngine(self._em)
        self._CVC4Sorts = {sorts.BitVec: self._em.mkBitVectorType,
                           sorts.Int: self._em.integerType,
                           sorts.Real: self._em.realType,
                           sorts.Bool: self._em.booleanType}
        self._CVC4Funs = {functions.extract: CVC4.BitVectorExtract,
                          functions.Equals: CVC4.EQUAL,
                          functions.Not: CVC4.NOT,
                          functions.And: CVC4.AND,
                          functions.Or: CVC4.OR,
                          functions.Ite: CVC4.ITE,
                          functions.Sub: CVC4.MINUS,
                          functions.Plus: CVC4.PLUS,
                          functions.LT: CVC4.LT,
                          functions.LEQ: CVC4.LEQ,
                          functions.GT: CVC4.GT,
                          functions.GEQ: CVC4.GEQ,
                          functions.bvand: CVC4.BITVECTOR_AND,
                          functions.bvor: CVC4.BITVECTOR_OR,
                          functions.bvadd: CVC4.BITVECTOR_PLUS,
                          functions.bvmul: CVC4.BITVECTOR_MULT,
                          functions.bvudiv: CVC4.BITVECTOR_UDIV,
                          functions.bvurem: CVC4.BITVECTOR_UREM,
                          functions.bvshl: CVC4.BITVECTOR_SHL,
                          functions.bvlshr: CVC4.BITVECTOR_LSHR,
                          functions.bvnot: CVC4.BITVECTOR_NOT,
                          functions.bvneg: CVC4.BITVECTOR_NEG}

        # Theory constant functions
        def create_bv(width, value):
            return self._em.mkConst(CVC4.BitVector(width, value))

        def create_int(value):
            return self._em.mkConst(CVC4.Rational(value))

        def create_real(value):
            if not isinstance(value, Fraction):
                value = Fraction(value).limit_denominator()
            return self._em.mkConst(CVC4.Rational(value.numerator, value.denominator))

        def create_bool(value):
            return self._em.mkBoolConst(value)

        self._CVC4Consts = {sorts.BitVec: create_bv,
                            sorts.Int: create_int,
                            sorts.Real: create_real,
                            sorts.Bool: create_bool}

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
        self._smt.setOption(optionstr, CVC4.SExpr(value))

    # Note: currently not different than set_option
    def set_nonstandard_option(self, optionstr, value):
        self._smt.setOption(optionstr, CVC4.SExpr(value))

    def declare_const(self, name, sort):
        cvc4sort = self._CVC4Sorts[sort.__class__](*sort.params)
        cvc4const = self._em.mkVar(name, cvc4sort)
        const = terms.CVC4Term(self, functions.No_op, cvc4const, sort, [])
        return const

    def theory_const(self, sort, value):
        cvc4tconst = self._CVC4Consts[sort.__class__](*sort.params, value)
        tconst = terms.CVC4Term(self, functions.No_op, cvc4tconst, sort, [])
        return tconst

    # if config strict, check arity and don't allow python objects as arguments
    def apply_fun(self, fun, *args):
        if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
            raise ValueError('In strict mode you must respect function arity:' +
                             ' {}: arity = {}'.format(fun, fun.arity))

        cvc4fun = self._CVC4Funs[fun.__class__]
        # handle list argument
        if isinstance(args[0], list):
            args = args[0]

        if config.strict:
            solver_args = [arg.solver_term for arg in args]
        else:
            # find a cvc4 term to infer the sort
            # TODO: make this more robust
            cvc4term = list(filter(lambda x: isinstance(x, terms.CVC4Term), args))[-1]
            solver_args = list(map(lambda arg: arg.solver_term
                               if isinstance(arg, terms.CVC4Term)
                               else
                               self.theory_const(cvc4term.sort, arg).solver_term,
                               args))

        # check if just indexer or needs to be evaluated
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*fun.params))
        cvc4terms = self._em.mkExpr(cvc4fun, solver_args)
        expr = terms.CVC4Term(self, fun, cvc4terms, fun.osort(*args), list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            for constraint in constraints:
                if constraint.sort != 'Bool':
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(constraint.sort))
                self._smt.assertFormula(constraint.solver_term)
        else:
            if constraints.sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(constraints.sort))
            self._smt.assertFormula(constraints.solver_term)

    def assertions(self):
        # TODO: fix iter error
        # Wanted these to be an iter but CVC4 threw an exception
        return [expr.toString() for expr in self._smt.getAssertions()]

    def get_model(self):
        if self.sat:
            return self._smt.getValue
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._smt.getValue(var.solver_term).toString()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')


# dictionary of solvers
# useful for running with multiple solvers
solvers = {'Z3': Z3Solver,
           'CVC4': CVC4Solver}

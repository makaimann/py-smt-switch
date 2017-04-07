from abc import ABCMeta, abstractmethod, abstractproperty
import CVC4
import z3
import sorts
import functions
import term


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
               functions.GEQ: lambda arg1, arg2: arg1 >= arg2}
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
        z3const = self._z3Sorts[sort.__class__.__name__](name, *sort.params)
        # should there be a no-op or just use None?
        const = term.Z3Term(self, None, z3const)
        return const

    def theory_const(self, sort, value):
        # Note: order of arguments is opposite what I would expect
        # if it becomes a problem, might need to use keywords
        return self._z3Consts[sort.__class__](value, *sort.params)

    def apply_fun(self, fun, *args):
        return self._z3Funs[fun.__class__](*fun.params, *args)

    def Assert(self, constraints):
        self._solver.add(constraints)

    def assertions(self):
        return self._solver.assertions()

    def get_model(self):
        if self.sat:
            return self._solver.model()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._solver.model().eval(var).as_string()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')


class CVC4Solver(SolverBase):
    # could also use class name instead of class itself as key
    # probably better for memory reasons?
    def __init__(self):
        super().__init__()
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
                          functions.GEQ: CVC4.GEQ}
        self._CVC4Consts = {sorts.BitVec: CVC4.BitVector,
                            sorts.Int: CVC4.Integer,
                            sorts.Real: CVC4.Rational}

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
        return self._em.mkVar(name, cvc4sort)

    def theory_const(self, sort, value):
        return self._em.mkConst(self._CVC4Consts[sort.__class__](*sort.params, value))

    def apply_fun(self, fun, *args):
        cvc4fun = self._CVC4Funs[fun.__class__]
        # check if just indexer or needs to be evaluated
        if not isinstance(cvc4fun, int):
            cvc4fun = self._em.mkConst(cvc4fun(*fun.params))
        return self._em.mkExpr(cvc4fun, *args)

    def Assert(self, constraints):
        if isinstance(constraints, list):
            for constraint in constraints:
                self._smt.assertFormula(constraint)
        else:
            self._smt.assertFormula(constraints)

    def assertions(self):
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
            return self._smt.getValue(var).toString()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

from .. import sorts
from .. import functions
from .. import terms
from .. import results
from .solverbase import SolverBase
from smt_switch.config import config
from functools import reduce
from math import ceil, log2


class BoolectorSolver(SolverBase):
    def __init__(self):
        self.boolector = __import__('boolector')
        self._btor = self.boolector.Boolector()

        # keeping track of assertions because couldn't figure out
        # how to print a list of assertions (other than dumping to stdout/a file)
        self._assertions = []

        self._BoolectorSorts = {sorts.BitVec: self._btor.BitVecSort,
                                sorts.Bool: lambda: self._btor.BitVecSort(1)}
        self._BoolectorFuns = {functions.Equals.func: self._btor.Eq,
                               functions.And.func: self.And,
                               functions.Or.func: self.Or,
                               functions.Ite.func: self._btor.Cond,
                               functions.Not.func: self._btor.Not,
                               # indexed operators are already raw representation so don't need to use .func
                               functions.Extract: self._btor.Slice,
                               functions.Concat.func: self._btor.Concat,
                               functions.BVAnd.func: self._btor.And,
                               functions.BVOr.func: self._btor.Or,
                               functions.BVXor.func: self._btor.Xor,
                               functions.BVAdd.func: self._btor.Add,
                               functions.BVSub.func: self._btor.Sub,
                               functions.BVMul.func: self._btor.Mul,
                               functions.BVUdiv.func: self._btor.Udiv,
                               functions.BVUrem.func: self._btor.Urem,
                               functions.BVShl.func: self.Sll,
                               functions.BVAshr.func: self.Sra,
                               functions.BVLshr.func: self.Srl,
                               functions.BVUlt.func: self._btor.Ult,
                               functions.BVUle.func: self._btor.Ulte,
                               functions.BVUgt.func: self._btor.Ugt,
                               functions.BVUge.func: self._btor.Ugte,
                               functions.BVSlt.func: self._btor.Slt,
                               functions.BVSle.func: self._btor.Slte,
                               functions.BVSgt.func: self._btor.Sgt,
                               functions.BVSge.func: self._btor.Sgte,
                               functions.BVNot.func: self._btor.Not,
                               functions.BVNeg.func: self._btor.Neg}

        self._BoolectorConsts = {sorts.BitVec: self._btor.Const,
                                 sorts.Bool: self._btor.Const}
        # Note: Boolector does not distinguish between Bools and (_ BitVec 1)
        #       so smt_switch is not either (specifically for Boolector)
        self._BoolectorResults = {sorts.BitVec: results.BoolectorBitVecResult,
                                  sorts.Bool: results.BoolectorBitVecResult}
        self._BoolectorOptions = {'produce-models': self.boolector.BTOR_OPT_MODEL_GEN}

        # am I missing any?
        self._BoolectorLogics = ['QF_BV', 'QF_ABV']

    def reset(self):
        self.__init__()

    def check_sat(self):
        if self._btor.Sat() == self._btor.SAT:
            self.sat = True
        else:
            self.sat = False
        return self.sat

    def set_logic(self, logicstr):
        if logicstr not in self._BoolectorLogics:
            raise ValueError('Boolector does not support {} '.format(logicstr) +
                             'If you believe this is incorrect, please contact a ' +
                             'developer or modify the class yourself (see _BoolectorLogics)')

    def set_option(self, optionstr, value):
        if optionstr in self._BoolectorOptions:
            self._btor.Set_opt(self._BoolectorOptions[optionstr], bool(value))

    def set_nonstandard_option(self, optionstr, value):
        self._btor.Set_opt(eval('boolector.{}'.format(optionstr)), value)

    def declare_const(self, name, sort):
        btorsort = self._BoolectorSorts[sort.__class__](*sort.params)
        btorconst = self._btor.Var(btorsort, name)
        const = terms.BoolectorTerm(self, functions.No_op, btorconst, [sort])
        return const

    def theory_const(self, sort, value):
        btortconst = self._BoolectorConsts[sort.__class__](*((value,) + sort.params))
        tconst = terms.BoolectorTerm(self, functions.No_op, btortconst, [sort])
        return tconst

    def apply_fun(self, op, *args):
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        # handle list argument
        if isinstance(args[0], list):
            args = args[0]

        solver_args = tuple(getattr(arg, 'solver_term', arg) for arg in args)
        btor_expr = self._BoolectorFuns[op.func](*(solver_args + op.args))
        expr = terms.BoolectorTerm(self, op, btor_expr, list(args))
        return expr

    def Assert(self, constraints):
        if isinstance(constraints, list):
            for constraint in constraints:
                sort = getattr(constraint, 'sort', type(constraint))
                if sort != bool and sort != sorts.Bool():
                    raise ValueError('Can only assert formulas of sort Bool. ' +
                                     'Received sort: {}'.format(constraint.sort))
                # getattr default was running and causing an error even if attribute existed
                btorconstraint = constraint.solver_term if hasattr(constraint, 'solver_term') \
                                 else self._btor.Const(constraint)
                self._btor.Assert(btorconstraint)
                # for now adding raw assertion to match other solvers
                # in the future add the wrapped assertion
                self._assertions.append(btorconstraint)
        else:
            sort = getattr(constraints, 'sort', type(constraints))
            if sort != bool and sort != sorts.Bool():
                raise ValueError('Can only assert formulas of sort Bool. ' +
                                 'Received sort: {}'.format(constraints.sort))
            # getattr default was running and causing an error even if attribute existed
            btorconstraint = constraints.solver_term if hasattr(constraints, 'solver_term') \
                             else self._btor.Const(constraints)
            self._btor.Assert(btorconstraint)
            # for now adding raw assertion to match other solvers
            # in the future add the wrapped assertion
            self._assertions.append(btorconstraint)

    def assertions(self):
        return self._assertions

    def get_model(self):
        if self.sat:
            return self._btor.Print_model()
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

    def get_value(self, var):
        if self.sat:
            return self._BoolectorResults[var.sort.__class__](var.solver_term)
        elif self.sat is not None:
            raise RuntimeError('Problem is unsat')
        else:
            raise RuntimeError('Solver has not been run')

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

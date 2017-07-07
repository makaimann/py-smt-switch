from .. import sorts
from .solverbase import SolverBase
from functools import reduce


class BoolectorSolver(SolverBase):
    def __init__(self):
        self.boolector = __import__('boolector')
        self._btor = self.boolector.Boolector()

        # keeping track of assertions because couldn't figure out
        # how to print a list of assertions (other than dumping to stdout/a file)
        self._assertions = []

        self._BoolectorSorts = {sorts.BitVec: self._btor.BitVecSort,
                                sorts.Bool: lambda: self._btor.BitVecSort(1)}
        self._BoolectorFuns = {'Equals': self._btor.Eq,
                               'And': self.And,
                               'Or': self.Or,
                               'Ite': self._btor.Cond,
                               'Not': self._btor.Not,
                               'Extract': self._btor.Slice,
                               'Concat': self._btor.Concat,
                               'BVAnd': self._btor.And,
                               'BVOr': self._btor.Or,
                               'BVXor': self._btor.Xor,
                               'BVAdd': self._btor.Add,
                               'BVSub': self._btor.Sub,
                               'BVMul': self._btor.Mul,
                               'BVUdiv': self._btor.Udiv,
                               'BVUrem': self._btor.Urem,
                               'BVShl': self.Sll,
                               'BVAshr': self.Sra,
                               'BVLshr': self.Srl,
                               'BVUlt': self._btor.Ult,
                               'BVUle': self._btor.Ulte,
                               'BVUgt': self._btor.Ugt,
                               'BVUge': self._btor.Ugte,
                               'BVSlt': self._btor.Slt,
                               'BVSle': self._btor.Slte,
                               'BVSgt': self._btor.Sgt,
                               'BVSge': self._btor.Sgte,
                               'BVNot': self._btor.Not,
                               'BVNeg': self._btor.Neg}

        self._BoolectorConsts = {sorts.BitVec: self._btor.Const,
                                 sorts.Bool: self._btor.Const}
        # Note: Boolector does not distinguish between Bools and (_ BitVec 1)
        #       so smt_switch is not either (specifically for Boolector)
        # self._BoolectorResults = {sorts.BitVec: results.BoolectorBitVecResult,
        #                           sorts.Bool: results.BoolectorBitVecResult}
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
        return btorconst

    def theory_const(self, sort, value):
        btortconst = self._BoolectorConsts[sort.__class__](*((value,) + sort.params))
        return btortconst

    def apply_fun(self, fname, indices, *args):
        # if config.strict and len(args) < fun.arity['min'] or len(args) > fun.arity['max']:
        #     raise ValueError('In strict mode you must respect function arity:' +
        #                      ' {}: arity = {}'.format(fun, fun.arity))

        # handle list argument

        btor_expr = self._BoolectorFuns[fname](*(args + indices))
        return btor_expr

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
            # The value will be wrapped at the api level
            return var
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

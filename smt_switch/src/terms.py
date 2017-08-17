from abc import ABCMeta
from . import sorts
from ..config import config
from fractions import Fraction
from .functions import func_enum, func_symbols, operator
import re


class TermBase(metaclass=ABCMeta):
    def __init__(self, smt, op, solver_term, children):
        self._smt = smt
        self._op = op
        self._solver_term = solver_term
        self._value = None
        # Note: instead of querying solvers and translating,
        #       it's easier to just pass this information
        #       directly since it's always known when
        #       instantiating a term
        # have to pass in sort instead of getting from op
        # because of No_op case i.e. when constructing a const
        # -- There are no arguments, so sort information is lost
        # unless passed in directly
        if op != smt.No_op:
            self._children = children
        else:
            self._children = []

    @property
    def children(self):
        return self._children

    @property
    def sort(self):
        return self._sort

    @property
    def op(self):
        return self._op

    @property
    def solver_term(self):
        return self._solver_term

    def __eq__(self, other):
        return self._smt.ApplyFun(self._smt.Equals, self, other)

    def __ne__(self, other):
        return self._smt.ApplyFun(self._smt.Not, self == other)

    def __add__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVAdd, self, other)
        else:
            return self._smt.ApplyFun(self._smt.Add, self, other)

    def __sub__(self, other):
        # override for bitvectors
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVSub, self, other)
        else:
            return self._smt.ApplyFun(self._smt.Sub, self, other)

    def __neg__(self):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.ApplyFun(self._smt.BVNeg, self)
        else:
            zero = self._smt.TheoryConst(self.sort, 0)
            return self._smt.ApplyFun(self._smt.Sub, zero, self)

    def __lt__(self, other):
        return self._smt.ApplyFun(self._smt.LT, self, other)

    def __le__(self, other):
        return self._smt.ApplyFun(self._smt.LEQ, self, other)

    def __gt__(self, other):
        return self._smt.ApplyFun(self._smt.GT, self, other)

    def __ge__(self, other):
        return self._smt.ApplyFun(self._smt.GEQ, self, other)

    # bit operations
    def __and__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVAnd, self, other)

    def __or__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVOr, self, other)

    def __xor__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVXor, self, other)

    def __lshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVShl, self, other)

    def __rshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.TheoryConst(self.sort, other)
        return self._smt.ApplyFun(self._smt.BVAshr, self, other)

    def __getitem__(self, idx):
        if self.sort.__class__ != self._smt.BitVec:
            raise ValueError('Slicing only defined for BitVec sorts')

        if isinstance(idx, slice):
            if idx.step and idx.step != 1:
                raise ValueError('Extract does not support step != 1')

            if idx.start < 0 or idx.start >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx.start, self.sort.width))

            if idx.stop < 0 or idx.stop >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx.stop, self.sort.width))

            if idx.start < idx.stop:
                raise ValueError('Extract is defined as [bith:bitl]')

            return self._smt.ApplyFun(self._smt.Extract(idx.start, idx.stop), self)

        elif isinstance(idx, int):
            if idx < 0 or idx >= self.sort.width:
                raise ValueError('{} is not a valid index for BitVec width {}'.format(idx, self.sort.width))

            return self._smt.ApplyFun(self._smt.Extract(idx, idx), self)
        else:
            raise ValueError('Slicing not defined for {}'.format(idx))


class CVC4Term(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)
        self._str2sort = {'int': lambda p: sorts.Int(),
                          'real': lambda p: sorts.Real(),
                          'bitvector': lambda p: sorts.BitVec(int(p)),
                          'bitvec': lambda p: sorts.BitVec(int(p)),
                          'bool': lambda p: sorts.Bool()}

        p = re.compile('\(?(_ )?(?P<sort>int|real|bitvector|bitvec|bool)\s?\(?(?P<param>\d+)?\)?')

        cvc4sortstr = solver_term.getType().toString().lower()
        match = p.search(cvc4sortstr)

        if not match:
            raise ValueError("Unknown type {}".format(cvc4sortstr))

        assert match.group('sort') in self._str2sort, 'Found {} for string {}'.format(match.group('sort'), cvc4sortstr)

        if match.group('sort') == 'BITVECTOR':
            assert match.group('param'), 'BitVecs must have a width'

        self._sort = self._str2sort[match.group('sort')](match.group('param'))

        # query children from solver
        self._children = []
        for c in solver_term.getChildren():
            # get the op
            k = c.getKind()
            if k in smt.solver._CVC4Funs.rev:
                enum_op = smt.solver._CVC4Funs.rev[k]
            elif k in smt.solver._CVC4InvOps:
                enum_op = smt.solver._CVC4InvOps[k]
            else:
                raise KeyError('{} not a recognized CVC4 enum'.format(k))
            op = operator(smt, enum_op, func_symbols[enum_op.name])
            self._children.append(CVC4Term(smt, op, c, []))

    def __repr__(self):
        return self.solver_term.toString()

    def as_int(self):
        if self.sort == self._smt.Int():
            return int(self._value.getConstRational().getDouble())

        elif self.sort.__class__ == self._smt.BitVec:
            return self._value.getConstBitVector().toInteger().toUnsignedInt()

        else:
            raise ValueError('Mismatched sort for request')

    def as_double(self):
        if self.sort == self._smt.Real:
            return self._value.getConstRational().getDouble()
        else:
            raise ValueError

    def as_fraction(self):
        if self.sort != self._smt.Real():
            raise ValueError
        r = self._value.getConstRational()
        return Fraction(r.getNumerator().toSignedInt(),
                        r.getDenominator().toSignedInt())

    def as_bool(self):
        if self.sort != self._smt.Bool():
            raise ValueError

        return self._value.getConstBoolean()

    def as_bitstr(self):
        return self._value.getConstBitVector().toString()

    @property
    def sort(self):
        return self._sort


class Z3Term(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)

        z3 = smt.solver.z3
        sortmap = {z3.Z3_BOOL_SORT: sorts.Bool(),
                   z3.Z3_INT_SORT: sorts.Int(),
                   z3.Z3_REAL_SORT: sorts.Real()}

        sts = solver_term.sort()

        if sts.kind() == z3.Z3_BV_SORT:
            self._sort = sorts.BitVec(sts.size())
        elif sts.kind() in sortmap:
            self._sort = sortmap[sts.kind()]
        else:
            raise ValueError('Unable to determine sort of {}'.format(self))

        # create children
        self._children = []
        for c in solver_term.children():
            enum_op = smt.solver._z3Funs2swFuns[c.decl().kind()]
            op = operator(smt, enum_op, func_symbols[enum_op.name])
            self._children.append(Z3Term(smt, op, c, []))

    def __repr__(self):
        if config.strict:
            return self.solver_term.sexpr()
        else:
            return self.solver_term.__repr__()

    def as_int(self):
        return self._value.as_long()

    def as_double(self):
        return float(self.value.as_fraction())

    def as_fraction(self):
        return self._value.as_fraction()

    def as_bool(self):
        if self.sort != self._smt.Bool():
            raise ValueError

        return bool(self._value)

    def as_bitstr(self):
        return '{0:b}'.format(int(self._value.as_string())).zfill(self.sort.width)

    @property
    def children(self):
        return self._children


class BoolectorTerm(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)
        boolector = smt.solver.boolector
        sortmap = {boolector.BoolectorBVNode: lambda w: sorts.BitVec(w),
                   boolector.BoolectorConstNode: lambda w: sorts.BitVec(w)}
        # Need BoolSort too -- BoolectorBoolNode
        self._sort = sortmap[type(solver_term)](solver_term.width)

    def __repr__(self):
        # This isn't the best solution, but boolector's __str__ and __repr__ are not implemented
        return self.solver_term.symbol

    def __str__(self):
        return self.solver_term.symbol

    def as_int(self):
        return int(self._value.assignment, base=2)

    def as_bool(self):
        if self._value.width != 1:
            raise ValueError("Can't interpret BitVec of width > 1 as a bool")

        return bool(self._value.assignment)

    def as_bitstr(self):
        return self._value.assignment

    @property
    def sort(self):
        return self._sort


def __bool_fun(*args):
    return sorts.Bool()


fun2sort = {func_enum.And: __bool_fun,
            func_enum.Or: __bool_fun,
            func_enum.No_op: sorts.get_sort,
            func_enum.Equals: __bool_fun,
            func_enum.Not: __bool_fun,
            func_enum.LT: __bool_fun,
            func_enum.GT: __bool_fun,
            func_enum.LEQ: __bool_fun,
            func_enum.GEQ: __bool_fun,
            func_enum.BVUlt: __bool_fun,
            func_enum.BVUle: __bool_fun,
            func_enum.BVUgt: __bool_fun,
            func_enum.BVUge: __bool_fun,
            func_enum.BVSlt: __bool_fun,
            func_enum.BVSle: __bool_fun,
            func_enum.BVSgt: __bool_fun,
            func_enum.BVSge: __bool_fun,
            func_enum.BVNot: sorts.get_sort,
            func_enum.BVNeg: sorts.get_sort,
            func_enum.Ite: lambda *args: sorts.get_sort(*args[1:]),
            func_enum.Sub: sorts.get_sort,
            func_enum.Add: sorts.get_sort,
            func_enum.Extract: lambda ub, lb, arg: sorts.BitVec(ub - lb + 1),
            func_enum.Concat: lambda b1, b2: sorts.BitVec(b1.sort.width + b2.sort.width),
            func_enum.ZeroExt: lambda bv, pad_width: sorts.BitVec(bv.sort.width + pad_width),
            func_enum.BVAnd: sorts.get_sort,
            func_enum.BVOr: sorts.get_sort,
            func_enum.BVXor: sorts.get_sort,
            func_enum.BVAdd: sorts.get_sort,
            func_enum.BVSub: sorts.get_sort,
            func_enum.BVMul: sorts.get_sort,
            func_enum.BVUdiv: sorts.get_sort,
            func_enum.BVUrem: sorts.get_sort,
            func_enum.BVShl: sorts.get_sort,
            func_enum.BVAshr: sorts.get_sort,
            func_enum.BVLshr: sorts.get_sort}

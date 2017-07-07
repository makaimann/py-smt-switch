from abc import ABCMeta
from . import sorts
from ..config import config


class TermBase(metaclass=ABCMeta):
    def __init__(self, smt, op, solver_term, children):
        self._smt = smt
        self._op = op
        self._solver_term = solver_term
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

        # Note: for now, fun is always a partial function
        self._sort = smt.fun2sort[op.fname](*(op.args + tuple(children)))

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

    # def _make_overloaded_op(self, function, *args):
    #     if config.strict:
    #         raise ValueError('Can\'t use overloaded operators in strict mode.' +
    #                          'Instead, use smt.apply_fun({}, args)'.format(function))
    #     self._smt.apply_fun(function, *args)

    # Overloaded operators
    # might use these someday
    #__eq__ = self._make_overloaded_op(smt.Equals(), self, other)
    #__ne__ = self._make_overloaded_op(smt.Not(), self == other)
    #__add__ = self._make_overloaded_op(smt.Add(), self, other)
    #__sub__ = self._make_overloaded_op(smt.Sub(), self, other)
    #__lt__ = self._make_overloaded_op(smt.LT(), self, other)
    #__le__ = self._make_overloaded_op(smt.LEQ(), self, other)
    #__gt__ = self._make_overloaded_op(smt.GT(), self, other)
    #__ge__ = self._make_overloaded_op(smt.GEQ(), self, other)

    def __eq__(self, other):
        return self._smt.apply_fun(self._smt.Equals, self, other)

    def __ne__(self, other):
        return self._smt.apply_fun(self._smt.Not, self == other)

    def __add__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.apply_fun(self._smt.BVAdd, self, other)
        else:
            return self._smt.apply_fun(self._smt.Add, self, other)

    def __sub__(self, other):
        # override for bitvectors
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.apply_fun(self._smt.BVSub, self, other)
        else:
            return self._smt.apply_fun(self._smt.Sub, self, other)

    def __neg__(self):
        if self.sort.__class__ == sorts.BitVec:
            return self._smt.apply_fun(self._smt.BVNeg, self)
        else:
            zero = self._smt.theory_const(self.sort, 0)
            return self._smt.apply_fun(smt.Sub, zero, self)

    def __lt__(self, other):
        return self._smt.apply_fun(self._smt.LT, self, other)

    def __le__(self, other):
        return self._smt.apply_fun(self._smt.LEQ, self, other)

    def __gt__(self, other):
        return self._smt.apply_fun(self._smt.GT, self, other)

    def __ge__(self, other):
        return self._smt.apply_fun(self._smt.GEQ, self, other)

    # bit operations
    def __and__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.theory_const(self.sort, other)
        return self._smt.apply_fun(self._smt.BVAnd, self, other)

    def __or__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.theory_const(self.sort, other)
        return self._smt.apply_fun(self._smt.BVOr, self, other)

    def __xor__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.theory_const(self.sort, other)
        return self._smt.apply_fun(self._smt.BVXor, self, other)

    def __lshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.theory_const(self.sort, other)
        return self._smt.apply_fun(self._smt.BVShl, self, other)

    def __rshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._smt.theory_const(self.sort, other)
        return self._smt.apply_fun(self._smt.BVAshr, self, other)


class CVC4Term(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)

    def __repr__(self):
        return self.solver_term.toString()


class Z3Term(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)

    def __repr__(self):
        if config.strict:
            return self.solver_term.sexpr()
        else:
            return self.solver_term.__repr__()


class BoolectorTerm(TermBase):
    def __init__(self, smt, op, solver_term, children):
        super().__init__(smt, op, solver_term, children)

    def __repr__(self):
        # This isn't the best solution, but boolector's __str__ and __repr__ are not implemented
        return self.solver_term.symbol

    def __str__(self):
        return self.solver_term.symbol

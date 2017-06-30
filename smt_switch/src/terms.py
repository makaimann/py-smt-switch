from abc import ABCMeta
from . import functions
from . import sorts
from ..config import config


class TermBase(metaclass=ABCMeta):
    def __init__(self, solver, op, solver_term, children):
        self._solver = solver
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
        if op != functions.No_op:
            self._children = children
        else:
            self._children = []

        # Note: for now, fun is always a partial function
        self._sort = fun2sort[op.func](*(op.args + tuple(children)))

    @property
    def children(self):
        return self._children

    @property
    def sort(self):
        return self._sort

    @property
    def solver(self):
        return self._solver

    @property
    def op(self):
        return self._op

    @property
    def solver_term(self):
        return self._solver_term

    def _make_overloaded_op(function, *args):
        if config.strict:
            raise ValueError('Can\'t use overloaded operators in strict mode.' +
                             'Instead, use solver.apply_fun({}, args)'.format(function))
        self._solver.apply_fun(function, *args)

    # Overloaded operators
    # might use these someday
    #__eq__ = self._make_overloaded_op(functions.Equals(), self, other)
    #__ne__ = self._make_overloaded_op(functions.Not(), self == other)
    #__add__ = self._make_overloaded_op(functions.Plus(), self, other)
    #__sub__ = self._make_overloaded_op(functions.Sub(), self, other)
    #__lt__ = self._make_overloaded_op(functions.LT(), self, other)
    #__le__ = self._make_overloaded_op(functions.LEQ(), self, other)
    #__gt__ = self._make_overloaded_op(functions.GT(), self, other)
    #__ge__ = self._make_overloaded_op(functions.GEQ(), self, other)

    def __eq__(self, other):
        return self._solver.apply_fun(functions.Equals(), self, other)

    def __ne__(self, other):
        return self._solver.apply_fun(functions.Not(), self == other)

    def __add__(self, other):
        if self.sort.__class__ == sorts.BitVec:
            return self._solver.apply_fun(functions.bvadd(), self, other)
        else:
            return self._solver.apply_fun(functions.Plus(), self, other)

    def __sub__(self, other):
        # override for bitvectors
        if self.sort.__class__ == sorts.BitVec:
            return self._solver.apply_fun(functions.bvsub(), self, other)
        else:
            return self._solver.apply_fun(functions.Sub(), self, other)

    def __neg__(self):
        if self.sort.__class__ == sorts.BitVec:
            return self._solver.apply_fun(functions.bvneg(), self)
        else:
            zero = self._solver.theory_const(self.sort, 0)
            return self._solver.apply_fun(functions.Sub(), zero, self)

    def __lt__(self, other):
        return self._solver.apply_fun(functions.LT(), self, other)

    def __le__(self, other):
        return self._solver.apply_fun(functions.LEQ(), self, other)

    def __gt__(self, other):
        return self._solver.apply_fun(functions.GT(), self, other)

    def __ge__(self, other):
        return self._solver.apply_fun(functions.GEQ(), self, other)

    # bit operations
    def __and__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._solver.theory_const(self.sort, other)
        return self._solver.apply_fun(functions.bvand(), self, other)

    def __or__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._solver.theory_const(self.sort, other)
        return self._solver.apply_fun(functions.bvor(), self, other)

    def __xor__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._solver.theory_const(self.sort, other)
        return self._solver.apply_fun(functions.bvxor(), self, other)

    def __lshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._solver.theory_const(self.sort, other)
        return self._solver.apply_fun(functions.bvshl(), self, other)

    def __rshift__(self, other):
        if not issubclass(other.__class__, TermBase):
            other = self._solver.theory_const(self.sort, other)
        return self._solver.apply_fun(functions.bvashr(), self, other)


class CVC4Term(TermBase):
    def __init__(self, solver, op, solver_term, children):
        super().__init__(solver, op, solver_term, children)

    def __repr__(self):
        return self.solver_term.toString()


class Z3Term(TermBase):
    def __init__(self, solver, op, solver_term, children):
        super().__init__(solver, op, solver_term, children)

    def __repr__(self):
        if config.strict:
            return self.solver_term.sexpr()
        else:
            return self.solver_term.__repr__()


class BoolectorTerm(TermBase):
    def __init__(self, solver, op, solver_term, children):
        super().__init__(solver, op, solver_term, children)

    def __repr__(self):
        # This isn't the best solution, but boolector's __str__ and __repr__ are not implemented
        return self.solver_term.symbol

    def __str__(self):
        return self.solver_term.symbol


def _bool_fun(*args):
    return sorts.Bool()


fun2sort = {functions.And.func: _bool_fun,
            functions.Or.func: _bool_fun,
            functions.No_op.func: sorts.get_sort,
            functions.Equals.func: _bool_fun,
            functions.Not.func: _bool_fun,
            functions.LT.func: _bool_fun,
            functions.GT.func: _bool_fun,
            functions.LEQ.func: _bool_fun,
            functions.GEQ.func: _bool_fun,
            functions.bvult.func: _bool_fun,
            functions.bvule.func: _bool_fun,
            functions.bvugt.func: _bool_fun,
            functions.bvuge.func: _bool_fun,
            functions.bvslt.func: _bool_fun,
            functions.bvsle.func: _bool_fun,
            functions.bvsgt.func: _bool_fun,
            functions.bvsge.func: _bool_fun,
            functions.bvnot.func: sorts.get_sort,
            functions.bvneg.func: sorts.get_sort,
            functions.Ite.func: lambda *args: sorts.get_sort(*args[1:]),
            functions.Sub.func: sorts.get_sort,
            functions.Plus.func: sorts.get_sort,
            # indexed functions don't need to access internal func
            functions.extract: lambda ub, lb, arg: sorts.BitVec(ub - lb + 1),
            functions.concat.func: lambda b1, b2: sorts.BitVec(b1.sort.width + b2.sort.width),
            functions.zero_extend.func: lambda bv, pad_width: sorts.BitVec(bv.sort.width + pad_width),
            functions.bvand.func: sorts.get_sort,
            functions.bvor.func: sorts.get_sort,
            functions.bvxor.func: sorts.get_sort,
            functions.bvadd.func: sorts.get_sort,
            functions.bvsub.func: sorts.get_sort,
            functions.bvmul.func: sorts.get_sort,
            functions.bvudiv.func: sorts.get_sort,
            functions.bvurem.func: sorts.get_sort,
            functions.bvshl.func: sorts.get_sort,
            functions.bvashr.func: sorts.get_sort,
            functions.bvlshr.func: sorts.get_sort}

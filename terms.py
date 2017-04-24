from abc import ABCMeta
import functions
import config


class TermBase(metaclass=ABCMeta):
    def __init__(self, solver, op, solver_term, sort, children):
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
        self._sort = sort
        self._children = children

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
        return self._solver.apply_fun(functions.Plus(), self, other)

    def __sub__(self, other):
        return self._solver.apply_fun(functions.Sub(), self, other)

    def __neg__(self):
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


class CVC4Term(TermBase):
    def __init__(self, solver, op, solver_term, sort, children):
        super().__init__(solver, op, solver_term, sort, children)

    def __repr__(self):
        return self.solver_term.toString()


class Z3Term(TermBase):
    def __init__(self, solver, op, solver_term, sort, children):
        super().__init__(solver, op, solver_term, sort, children)

    def __repr__(self):
        if config.strict:
            return self.solver_term.sexpr()
        else:
            return self.solver_term.__repr__()

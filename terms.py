from abc import ABCMeta, abstractproperty
import functions


class TermBase(metaclass=ABCMeta):
    def __init__(self, solver, op, solver_term, children):
        self._solver = solver
        self._op = op
        self._solver_term = solver_term
        # Note: instead of querying solvers and translating,
        #       it's easier to just pass this information
        #       directly since it's always known when
        #       instantiating a term
        self._children = children

    @property
    def children(self):
        return self._children

    @abstractproperty
    def sort(self):
        pass

    @property
    def solver(self):
        return self._solver

    @property
    def op(self):
        return self._op

    @property
    def solver_term(self):
        return self._solver_term

    # Overloaded operators
    def __eq__(self, other):
        return self._solver.apply_fun(functions.Equals(), self, other)

    def __ne__(self, other):
        return self._solver.apply_fun(functions.Not(), self == other)

    def __add__(self, other):
        return self._solver.apply_fun(functions.Plus(), self, other)

    def __sub__(self, other):
        return self._solver.apply_fun(functions.Sub(), self, other)

    def __lt__(self, other):
        return self._solver.apply_fun(functions.LT(), self, other)

    def __le__(self, other):
        return self._solver.apply_fun(functions.LEQ(), self, other)

    def __gt__(self, other):
        return self._solver.apply_fun(functions.GT(), self, other)

    def __ge__(self, other):
        return self._solver.apply_fun(functions.GEQ(), self, other)
        

class CVC4Term(TermBase):
    def __init__(self, solver, op, solver_term, children):
        super().__init__(solver, op, solver_term, children)

    # for now just returns a string
    # will evenutally translate back to sort
    @property
    def sort(self):
        return self.solver_term.getType().toString()

    def __repr__(self):
        return self.solver_term.toString()


class Z3Term(TermBase):
    def __init__(self, solver, op, solver_term, children):
        super().__init__(solver, op, solver_term, children)

    # for now just returns a string
    # will eventually translate back to sort
    @property
    def sort(self):
        return self.solver_term.sort().sexpr()

    def __repr__(self):
        return self.solver_term.sexpr()

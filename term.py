from abc import ABCMeta, abstractproperty


class TermBase(metaclass=ABCMeta):
    def __init__(self, solver, op, solver_term):
        self._solver = solver
        self._op = op
        self._solver_term = solver_term

    @abstractproperty
    def children(self):
        pass

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


class CVC4Term(TermBase):
    def __init__(self, solver, op, solver_term):
        super().__init__(solver, op, solver_term)

    def children(self):
        raise NotImplementedError

    def sort():
        raise NotImplementedError


class Z3Term(TermBase):
    def __init__(self, solver, op, solver_term):
        super().__init__(solver, op, solver_term)

    def children(self):
        raise NotImplementedError

    def sort():
        raise NotImplementedError

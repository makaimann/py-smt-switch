from abc import ABCMeta, abstractproperty


class TermBase(metaclass=ABCMeta):
    def __init__(self, solver, op, *args):
        self._solver = solver
        self._op = op
        self._args = args

    @abstractproperty
    def children(self):
        raise NotImplementedError

    @property
    def op(self):
        return self._op

    @property
    def args(self):
        return self._args

    @property
    def solver(self):
        return self._solver


class CVC4Term(TermBase):
    def __init__(self, solver, op, *args):
        super().__init__(solver, op, *args)


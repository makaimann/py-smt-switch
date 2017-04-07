from abc import ABCMeta, abstractproperty


class Term(metaclass=ABCMeta):
    def __init__(self, op, args, solver):
        self._op = op
        self._args = args
        self._solver = solver

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


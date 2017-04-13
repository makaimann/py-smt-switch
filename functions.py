from abc import ABCMeta
from math import inf
import inspect


class FunctionBase(metaclass=ABCMeta):
    def __init__(self, arity, usage):
        self._arity = arity
        self._usage = usage

    @property
    def arity(self):
        return self._arity

    @property
    def usage(self):
        return self._usage

    @property
    def params(self):
        return ()

    def __call__(self, *args):
        if args and isinstance(args[0], list):
            args = args[0]
            return args[0].solver.apply_fun(self, *args)
        elif args:
            return args[0].solver.apply_fun(self, *args)
        else:
            raise ValueError('Can\'t call a 0-arity function.')

    def __repr__(self):
        return self.__class__.__name__


class extract(FunctionBase):
    arity = 1

    def __init__(self, ub, lb):
        super().__init__(self.arity, '(extract BitVec)')
        self._ub = ub
        self._lb = lb

    @property
    def ub(self):
        return self._ub

    @property
    def lb(self):
        return self._lb

    @property
    def width(self):
        return self._ub - self._lb + 1

    @property
    def params(self):
        return (self._ub, self._lb)


class Equals(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(= arg1 arg2)')


class Not(FunctionBase):
    arity = 1

    def __init__(self):
        super().__init__(self.arity, '(! formula)')


class And(FunctionBase):
    arity = inf  # not sure this is the best way

    def __init__(self):
        super().__init__(self.arity, '(and args)')

    # Overloading callable FunctionBase
    def __call__(self, *args):
        if args and isinstance(args[0], list):
            args = args[0]

        # With strict=False, (and arg1) --> arg1, (and ) --> True
        if len(args) > 1:
            return args[0].solver.apply_fun(self, *args)
        elif len(args) == 1:
            return args[0]
        else:
            return True


class Or(FunctionBase):
    arity = inf  # not sure this is the best way

    def __init__(self):
        super().__init__(self.arity, '(or args)')


class Ite(FunctionBase):
    arity = 3

    def __init__(self):
        super().__init__(self.arity, '(ite cond arg1 arg2)')


class Sub(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(- arg1 arg2)')


class Plus(FunctionBase):
    arity = 2  # or does smt lib allow for arbitrary number of arguments?

    def __init__(self):
        super().__init__(self.arity, '(+ arg1 arg2)')


class LT(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(< arg1 arg2)')


class LEQ(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(<= arg1 arg2)')


class GT(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(> arg1 arg2)')


class GEQ(FunctionBase):
    arity = 2

    def __init__(self):
        super().__init__(self.arity, '(>= arg1 arg2)')


def declare_fun(identifier, *args):
    if isinstance(identifier, str):
        if identifier[0] == '(':
            # TODO: Parse S expression
            raise NotImplementedError
        else:
            return eval(identifier)(*args)
    elif inspect.isclass(identifier):
        return identifier(*args)
    else:
        raise ValueError('Expected [str | Sort] and received {}.'.format(type(identifier)))

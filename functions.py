from abc import ABCMeta, abstractmethod
from math import inf
import inspect
import sorts
import config


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

    @abstractmethod
    def osort(self, *args):
        pass

    def __call__(self, *args):
        # handle list argument
        if args and isinstance(args[0], list):
            args = args[0]

        if args:
            return args[0].solver.apply_fun(self, *args)
        else:
            if config.strict:
                raise ValueError('In strict mode, you must respect function arity: ' +
                                 '{}: arity = {}'.format(self.__class__.__name__, self.arity))
            else:
                raise ValueError('Incorrect number of arguments for' +
                                 'function: {}'.format(self.__class__.__name__))

    def __repr__(self):
        return self.__class__.__name__


class No_op(FunctionBase):
    arity = {'min': 0,
             'max': 0}

    def __init__(self):
        super().__init__(self.arity, 'No_op')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError('No_op is used when constructing constants. ' +
                             'Therefore its output sort is parameterized by a Term.' +
                             'Need to provide an argument to determine output sort')
        else:
            return args[0].sort


class extract(FunctionBase):
    arity = {'min': 0,
             'max': 0}

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

    def osort(self, *args):
        return sorts.BitVec(self.width)


class Equals(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class Not(FunctionBase):
    arity = {'min': 1,
             'max': 1}

    def __init__(self):
        super().__init__(self.arity, '(not formula)')

    def osort(self, *args):
        return sorts.Bool()


class And(FunctionBase):
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(and args)')

    def osort(self, *args):
        return sorts.Bool()

    # Overloading callable FunctionBase
    if not config.strict:
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
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(or args)')

    def osort(self, *args):
        return sorts.Bool()

    # Overloading callable FunctionBase
    if not config.strict:
        def __call__(self, *args):
            if args and isinstance(args[0], list):
                args = args[0]

            # With strict=False, (and arg1) --> arg1, (and ) --> True
            if len(args) > 1:
                return args[0].solver.apply_fun(self, *args)
            elif len(args) == 1:
                return args[0]
            else:
                return False


class Ite(FunctionBase):
    arity = {'min': 3,
             'max': 3}

    def __init__(self):
        super().__init__(self.arity, '(ite cond arg1 arg2)')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need an argument to determine output sort.')
        return args[0].sort


class Sub(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(- arg1 arg2)')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need an argument to determine output sort.')
        return args[0].sort


class Plus(FunctionBase):
    arity = {'min': 2,
             'max': inf}

    def __init__(self):
        super().__init__(self.arity, '(+ arg1 arg2)')

    def osort(self, *args):
        if len(args) == 0:
            raise ValueError(self.__class__name +
                             '\'s output sort is parameterized by its arguments. ' +
                             'Need an argument to determine output sort.')
        return args[0].sort


class LT(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(< arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class LEQ(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(<= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class GT(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(> arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


class GEQ(FunctionBase):
    arity = {'min': 2,
             'max': 2}

    def __init__(self):
        super().__init__(self.arity, '(>= arg1 arg2)')

    def osort(self, *args):
        return sorts.Bool()


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

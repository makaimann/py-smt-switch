from abc import ABCMeta
# from enum import Enum  # not being used any more. Keeping around for now just in case
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

    def __repr__(self):
        return '({} {})'.format(self.__class__.__name__, self.params)


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


class Or(FunctionBase):
    arity = inf  # not sure this is the best way

    def __init__(self):
        super().__init__(self.arity, '(or args)')


class Ite(FunctionBase):
    arity = 3

    def __init__(self):
        super().__init__(self.arity, '(ite cond arg1 arg2)')


class Sub(FunctionBase):
    arity = 2  # or does smt lib allow for arbitrary number of arguments?

    def __init__(self):
        super().__init__(self.arity, '(- arg1 arg2)')


class Plus(FunctionBase):
    arity = 2

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


# deprecated -- leaving here just in case
# slightly worried about potential misuse of classes when used as symbols
#class Symbol(Enum):
#    extract = extract
#    Equals = Equals
#    Not = Not
#    And = And
#    Or = Or
#    Ite = Ite
#    Sub = Sub
#    Plus = Plus
#    LT = LT
#    LEQ = LEQ
#    GT = GT
#    GEQ = GEQ


def declare_fun(identifier, *args):
    # Deprecated Symbol -- keeping around for now in case we switch back
    # if isinstance(identifier, Symbol):
    #     return identifier.value(*args)
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

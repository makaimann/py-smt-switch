from abc import ABCMeta, abstractmethod
# from enum import Enum  # no longer being used
import inspect


class SortBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, sexpr, children):
        self._sexpr = sexpr
        self._children = children
        self._indexedID = None

    @property
    def sexpr(self):
        return self._sexpr

    @property
    def children(self):
        return self._children

    @property
    def params(self):
        return ()

    def __repr__(self):
        return self._sexpr

    def __eq__(self, other):
        return isinstance(other, type(self)) and self._sexpr == other.sexpr

    def __ne__(self, other):
        return not isinstance(other, type(self)) or not self._sexpr == other.sexpr

    def __hash__(self):
        return hash(self._sexpr)


class BitVec(SortBase):
    def __init__(self, width):
        super().__init__('(_ BitVec {})'.format(width), [])
        self._width = width

    @property
    def width(self):
        return self._width

    @property
    def params(self):
        return (self._width,)


class Int(SortBase):
    def __init__(self):
        super().__init__('Int', [])


class Real(SortBase):
    def __init__(self):
        super().__init__('Real', [])


class Bool(SortBase):
    def __init__(self):
        super().__init__('Bool', [])

#deprecated -- using functions themselves as identifiers
#class Symbol(Enum):
#    BitVec = BitVec
#    Int = Int
#    Real = Real
#    Bool = Bool


def construct_sort(identifier, *args):
    #if isinstance(identifier, Symbol):
        # The value attribute is actually a sort class
        # This is instantiating a class
    #    return identifier.value(*args)
    if isinstance(identifier, str):
        if identifier[0] == '(':
            # TODO: parse S expression
            raise NotImplementedError
        else:
            return eval(identifier)(*args)
    elif inspect.isclass(identifier):
        return identifier(*args)
    else:
        raise ValueError('Expected [str | Sort] and received {}.'.format(type(identifier)))

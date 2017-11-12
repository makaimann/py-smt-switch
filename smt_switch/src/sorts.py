# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from abc import ABCMeta, abstractmethod
import inspect


__all__ = ['BitVec', 'Int', 'Real', 'Bool', 'Array']

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


class Array(SortBase):
    def __init__(self, idxsort, dsort):
        super().__init__('(Array {} {})'.format(idxsort, dsort), [])
        self._idxsort = idxsort
        self._dsort = dsort

    @property
    def idxsort(self):
        return self._idxsort

    @property
    def dsort(self):
        return self._dsort

    @property
    def params(self):
        return (self._idxsort, self._dsort)

# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from functools import update_wrapper
import collections

'''
Useful utility classes and functions
'''

__all__ = ['withrepr', 'namedtuple_with_defaults']


def namedtuple_with_defaults(typename, field_names, default_values=()):
    '''
       Creates namedtuple with default values
       From:
           https://stackoverflow.com/questions/11351032/named-tuple-and-optional-keyword-arguments
    '''
    T = collections.namedtuple(typename, field_names)
    T.__new__.__defaults__ = (None,) * len(T._fields)
    if isinstance(default_values, collections.Mapping):
        prototype = T(**default_values)
    else:
        prototype = T(*default_values)
    T.__new__.__defaults__ = tuple(prototype)
    return T


class reprwrapper(object):
    def __init__(self, repr, func):
        self._repr = repr
        self._func = func
        update_wrapper(self, func)
    def __call__(self, *args, **kw):
        return self._func(*args, **kw)
    def __repr__(self):
        return self._repr(self._func)


def withrepr(reprfun):
    def _wrap(func):
        return reprwrapper(reprfun, func)
    return _wrap

from functools import partial, update_wrapper
from collections import namedtuple
import sys
from ..config import config
from . import sorts


__all__ = ['And', 'Or'] # append to list in generate functions


fdata = namedtuple('fdata', 'num_indices, min_arity, max_arity')
__MAXARGS__ = 6000

funcs = {'No_op': fdata(0, 0, 0), 'Equals': fdata(0, 2, 2), 'Not': fdata(0, 1, 1), 'Ite': fdata(0, 3, 3),
         'Sub': fdata(0, 2, 2), 'Plus': fdata(0, 2, __MAXARGS__), 'LT': fdata(0, 2, 2),
         'GT': fdata(0, 2, 2), 'LEQ': fdata(0, 2, 2), 'GEQ': fdata(0, 2, 2),
         'extract': fdata(2, 1, 1), 'concat': fdata(0, 2, 2), 'zero_extend': fdata(0, 2, 2),
         'bvand': fdata(0, 2, 2), 'bvor': fdata(0, 2, 2), 'bvxor': fdata(0, 2, 2),
         'bvadd': fdata(0, 2, 2), 'bvsub': fdata(0, 2, 2), 'bvmul': fdata(0, 2, 2),
         'bvudiv': fdata(0, 2, 2), 'bvurem': fdata(0, 2, 2), 'bvshl': fdata(0, 2, 2),
         'bvashr': fdata(0, 2, 2), 'bvlshr': fdata(0, 2, 2), 'bvult': fdata(0, 2, 2),
         'bvule': fdata(0, 2, 2), 'bvugt': fdata(0, 2, 2), 'bvuge': fdata(0, 2, 2),
         'bvule': fdata(0, 2, 2), 'bvslt': fdata(0, 2, 2), 'bvsle': fdata(0, 2, 2),
         'bvsgt': fdata(0, 2, 2), 'bvsge': fdata(0, 2, 2), 'bvnot': fdata(0, 1, 1),
         'bvneg': fdata(0, 1, 1)}


class operator(partial):
    def __init__(self, fun, *args, **kwargs):
        self._p = partial(fun, *args, **kwargs)

    def __eq__(self, other):
        return self._p.func == other._p.func and self._p.args == other._p.args and self._p.keywords == other._p.keywords

    def __ne__(self, other):
        return self._p.func != other._p.func or self._p.args != other._p.args or self._p.keywords != other._p.keywords

    @property
    def func(self):
        return self._p.func

    @property
    def args(self):
        return self._p.args

    @property
    def keywords(self):
        return self._p.keywords

    def __repr__(self):
        return '<operator: {}, {} {}>'.format(self._p.func.__repr__(), self._p.args, self._p.keywords)

    def __call__(self, *args, **kwargs):
        return self._p(*args, **kwargs)

    def __hash__(self):
        return self.func.__hash__()


def _gen_operator(fun, fdata, *args, **kwargs):

    # expand out args if list
    if args and isinstance(args[0], list):
        args = args[0]

    if args:
        # Not pretty but trying to avoid circular dependency
        s_terms = list(filter(lambda arg: 'TermBase' in
                              [base.__name__ for base in arg.__class__.__bases__], args))

    if fun.__class__ == operator:
        # maybe handle keyword args here too?
        # if already an operator, then all indices should be assigned
        assert len(fun.args) == fdata.num_indices

        if not s_terms:
            raise ValueError('There needs to be at least one argument of type [Solver Name]Term')
        
        return s_terms[0].solver.apply_fun(fun, *args, **kwargs)

    elif len(args) == fdata.num_indices:
        return operator(fun, *args, **kwargs)

    elif len(args) > fdata.num_indices:
        # always pass a partial function with the minumum number of arguments
        # this is for CVC4 to construct the function
        return s_terms[0].solver.apply_fun(operator(fun, *args[:fdata.num_indices]), *args[fdata.num_indices:], **kwargs)

    else:
        raise ValueError('Expected {} inputs to indexed operator but received'.format(fdata.num_indices, len(args)))


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


def _generate_function(name, fdata):

    @withrepr(lambda x: "%s" % name)
    def func(*args):
        return _gen_operator(func, fdata, *args)
    func.__name__ = name

    if fdata.num_indices > 0:
        return func

    elif fdata.num_indices == 0:
        # in this case, return operator with no indices
        f = func()
        return f

    else:
        raise ValueError('Invalid expected num_indices in operator {}'.format(name))

namespace = sys._getframe(0).f_globals
for name, m in funcs.items():
    f = _generate_function(name, m)
    namespace[name] = f
    __all__.append(name)


# def _No_op():
#     return 'No_op'


# No_op = operator(_No_op)


def _And(*args):
    if config.strict:
        return _gen_operator(And, 2, *args)
    else:
        if args and isinstance(args[0], list):
            args = args[0]

        if len(args) > 1:
            return _gen_operator(And, 2, *args)
        elif len(args) == 1:
            return args[0].solver.apply_fun(And, *args)
        else:
            return True


def _Or(*args):
    if config.strict:
        return _gen_operator(Or, 2, *args)
    else:
        if args and isinstance(args[0], list):
            args = args[0]

        if len(args) > 1:
            return _gen_operator(And, 2, *args)
        elif len(args) == 1:
            return args[0].solver.apply_fun(Or, *args)
        else:
            return True


And = _gen_operator(_And, fdata(0, 0, __MAXARGS__))
Or = _gen_operator(_Or, fdata(0, 0, __MAXARGS__))


def construct_fun(fun, *args):
    # partial function evaluation all handled internally
    return fun(*args)

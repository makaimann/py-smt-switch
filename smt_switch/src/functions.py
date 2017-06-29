from functools import partial, update_wrapper
import sys
from ..config import config


__all__ = ['No_op', 'And', 'Or'] # append to list in generate functions


class mypartial(partial):
    def __init__(self, fun, *args, **kwargs):
        self._p = partial(fun, *args, **kwargs)

    def __eq__(self, other):
        return self._p.func == other._p.func and self._p.args == other._p.args and self._p.keywords == other._p.keywords

    def __repr__(self):
        return '<mypartial: {}, {} {}>'.format(self._p.func.__repr__(), self._p.args, self._p.keywords)


def _partial_eval(fun, m, *args, **kwargs):

    # expand out args if list
    if args and isinstance(args[0], list):
        args = args[0]

    # expand arguments if partial function input
    if fun.__class__ == partial:
        args = fun.args + args
        kwargs = {**fun.keywords, **kwargs}

    if len(args) < m:
        return partial(fun, *args, **kwargs)

    else:
        if args:
            # Not pretty but trying to avoid circular dependency
            s_terms = list(filter(lambda arg: 'TermBase' in [base.__name__ for base in arg.__class__.__bases__], args))
            if not s_terms:
                raise ValueError('There needs to be at least one argument of type [Solver Name]Term')
            return s_terms[0].solver.apply_fun(fun, *args, **kwargs)

        # execution should never reach this code
        assert True == False, 'An invariant is broken'


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
    

def _generate_function(name, m):
    @withrepr(lambda x: "<Func: %s>" % name)
    def func(*args):
        return _partial_eval(func, m, *args)

    func.__name__ == name
    return func


funcs = {'Equals': 2, 'Not': 1, 'Ite': 3, 'Sub': 2, 'Plus': 2, 'LT': 2,
         'GT': 2, 'LEQ': 2, 'GEQ': 2, 'extract': 3, 'concat': 2,
         'zero_extend': 2, 'bvand': 2, 'bvor': 2, 'bvxor': 2, 'bvadd': 2,
         'bvsub': 2, 'bvmul': 2, 'bvudiv': 2, 'bvurem': 2, 'bvshl': 2,
         'bvashr': 2, 'bvlshr': 2, 'bvult': 2, 'bvule': 2, 'bvugt': 2,
         'bvuge': 2, 'bvule': 2, 'bvslt': 2, 'bvsle': 2, 'bvsgt': 2,
         'bvsge': 2, 'bvnot': 1, 'bvneg': 1}


namespace = sys._getframe(0).f_globals
for name, m in funcs.items():
    f = _generate_function(name, m)
    namespace[name] = f
    __all__.append(name)


def No_op():
    return 'No_op'


def And(*args):
    if config.strict:
        return _partial_eval(And, 2, *args)
    else:
        if args and isinstance(args[0], list):
            args = args[0]

        if len(args) > 1:
            return _partial_eval(And, 2, *args)
        elif len(args) == 1:
            return args[0].solver.apply_fun(And, *args)
        else:
            return True


def Or(*args):
    if config.strict:
        return _partial_eval(Or, 2, *args)
    else:
        if args and isinstance(args[0], list):
            args = args[0]

        if len(args) > 1:
            return _partial_eval(And, 2, *args)
        elif len(args) == 1:
            return args[0].solver.apply_fun(Or, *args)
        else:
            return True


def declare_fun(fun, *args):
    # partial function evaluation all handled internally
    return fun(*args)

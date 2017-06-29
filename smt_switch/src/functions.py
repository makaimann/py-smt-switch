from functools import partial, update_wrapper
from collections import namedtuple
import sys
from ..config import config
from . import sorts


__all__ = ['And', 'Or']  # append to list in generate functions


fdata = namedtuple('fdata', 'num_indices, min_arity, max_arity')
__MAXARGS__ = 6000

funcs = {'Equals': fdata(0, 2, 2), 'Not': fdata(0, 1, 1), 'Ite': fdata(0, 3, 3),
         'Sub': fdata(0, 2, 2), 'Plus': fdata(0, 2, __MAXARGS__), 'LT': fdata(0, 2, 2),
         'GT': fdata(0, 2, 2), 'LEQ': fdata(0, 2, 2), 'GEQ': fdata(0, 2, 2),
         'extract': fdata(2, 1, 1), 'concat': fdata(0, 2, 2), 'zero_extend': fdata(0, 2, 2),
         'bvand': fdata(0, 2, 2), 'bvor': fdata(0, 2, 2), 'bvxor': fdata(0, 2, 2),
         'bvadd': fdata(0, 2, 2), 'bvsub': fdata(0, 2, 2), 'bvmul': fdata(0, 2, 2),
         'bvudiv': fdata(0, 2, 2), 'bvurem': fdata(0, 2, 2), 'bvshl': fdata(0, 2, 2),
         'bvashr': fdata(0, 2, 2), 'bvlshr': fdata(0, 2, 2), 'bvult': fdata(0, 2, 2),
         'bvule': fdata(0, 2, 2), 'bvugt': fdata(0, 2, 2), 'bvuge': fdata(0, 2, 2),
         'bvslt': fdata(0, 2, 2), 'bvsle': fdata(0, 2, 2), 'bvsgt': fdata(0, 2, 2),
         'bvsge': fdata(0, 2, 2), 'bvnot': fdata(0, 1, 1), 'bvneg': fdata(0, 1, 1),
         'No_op': fdata(0, 0, 0), }


class operator(partial):
    '''
       Class that wraps all operators

       Allows for partial evaluations

       _gen_operator ensures that the partial evaluations are only for the number
       of indexes in an indexed operator (normal operators have num_index == 0)

       e.g. bvult can not be partially evaluated except with 0 arguments (because it is not indexed)
            on the other hand, extract can be partially evaluated with it's high and low bits

            ex4_2 = functions.extract(4, 2)
            ex4_2(bv)

            is equivalent to:

            functions.extract(4, 2, bv)

            ex4_2 == functions.extract(4, 2) will return True
    '''

    def __init__(self, fun, *args, **kwargs):
        self._p = partial(fun, *args, **kwargs)

    def __eq__(self, other):
        return self._p.func == other._p.func and self._p.args == other._p.args \
                               and self._p.keywords == other._p.keywords

    def __ne__(self, other):
        return self._p.func != other._p.func or self._p.args != other._p.args \
                               or self._p.keywords != other._p.keywords

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
        return '<operator: {}, {} {}>'.format(self._p.func.__name__, self._p.args, self._p.keywords)

    def __call__(self, *args, **kwargs):
        return self._p(*args, **kwargs)

    def __hash__(self):
        return self.func.__hash__()


def _gen_operator(fun, fdata, *args, **kwargs):
    '''
       Takes a function creates an operator for it. All functions are instantiated as an operator
       If the function is not an indexed operator, then it just has no args

       i.e. bvult is  <operator: bvult () {}>  <-- operator with no args

       The operators are callable, and can be used by solver.apply_fun(operator, *args)
    '''

    # expand out args if list
    if args and isinstance(args[0], list):
        args = args[0]

    if args:
        # Not pretty but trying to avoid circular dependency
        s_terms = list(filter(lambda arg: 'TermBase' in
                              [base.__name__ for base in arg.__class__.__bases__], args))

    if fun.__class__ == operator:
        # TODO: Also allow keyword arguments -- not urgent

        # if already an operator, then all indices should be assigned
        assert len(fun.args) == fdata.num_indices

        if len(args) > fdata.min_arity:
            if not s_terms:
                raise ValueError('There needs to be at least one argument' +
                                 ' of type [Solver Name]Term')

            if config.strict and len(args) > fdata.max_arity:
                raise ValueError('In strict mode and received {} args when max arity = '
                                 .format(len(args), fdata.max_arity))

            return s_terms[0].solver.apply_fun(fun, *args, **kwargs)

        else:
            return operator(fun.func, *args, **kwargs)

    elif len(args) == fdata.num_indices:
        return operator(fun, *args, **kwargs)

    elif len(args) >= fdata.num_indices + fdata.min_arity:

        if config.strict and len(args) > fdata.max_arity:
            raise ValueError('In strict mode and received {} args when max arity = '
                             .format(len(args), fdata.max_arity))

        # always pass a partial function with the minumum number of arguments
        # this is for CVC4 to construct the function
        return s_terms[0].solver.apply_fun(operator(fun, *args[:fdata.num_indices]),
                                           *args[fdata.num_indices:], **kwargs)

    else:
        raise ValueError('Expected {} inputs to indexed operator but received'
                         .format(fdata.num_indices, len(args)))


def _generate_function(name, fdata):

    '''
       Generates functions based on the dictionary funcs with the namedtuple
       fdata which contains num_indices, min_arity and max_arity
    '''

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


# add functions to namespace and to __all__
namespace = sys._getframe(0).f_globals
for name, m in funcs.items():
    f = _generate_function(name, m)
    namespace[name] = f
    __all__.append(name)


# special definitions for And/Or
# this is just to support the And([]) --> True case

def _And(*args):
    if config.strict:
        return _gen_operator(And, fdata(0, 2, __MAXARGS__), *args)
    else:
        if args and isinstance(args[0], list):
            if not args[0]:
                return True

            args = args[0]

        if len(args) == 1:
            return args[0]

        else:
            return _gen_operator(_And, fdata(0, 1, __MAXARGS__), *args)


def _Or(*args):
    if config.strict:
        return _gen_operator(Or, fdata(0, 2, __MAXARGS__), *args)
    else:
        if args and isinstance(args[0], list):
            if not args[0]:
                return False

            args = args[0]

        if len(args) == 1:
            return args[0]
        else:
            return _gen_operator(_Or, fdata(0, 1, __MAXARGS__), *args)


# make them operators
And = _gen_operator(_And, fdata(0, 1, __MAXARGS__))
Or = _gen_operator(_Or, fdata(0, 1, __MAXARGS__))


# construct a function in strict mode
def construct_fun(fun, *args):
    # partial function evaluation all handled internally
    return fun(*args)

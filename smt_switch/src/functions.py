import sys
import enum
from collections import OrderedDict
from functools import partial
from ..config import config
from ..util import namedtuple_with_defaults


fdata = namedtuple_with_defaults('fdata', 'num_indices, min_arity, max_arity, custom')


# special definitions for And/Or
# this is just to support the And([]) --> True case
def _And(*args):
    '''
       Custom and function defined for And([]) --> True, and And(x) --> x

    '''

    if len(args) == 0:
        return True

    elif len(args) == 1:
        return args[0]

    else:
        raise ValueError('Custom And should not be called with >= 2 args')


def _Or(*args):

    if len(args) == 0:
        return False

    elif len(args) == 1:
        return args[0]

    else:
        raise ValueError('Custom Or should not be called with >= 2 args')


# Use strings here so that enums are automatically generated
# if used enum here, would have to write function twice
# once in enum and once to connect with data

# make it an OrderedDict so that enum values are always the same
func_symbols = OrderedDict([('And', fdata(0, 2, sys.maxsize, _And)),
                            ('Or', fdata(0, 2, sys.maxsize, _Or)),
                            ('Equals', fdata(0, 2, 2)),
                            ('Not', fdata(0, 1, 1)),
                            ('Ite', fdata(0, 3, 3)),
                            ('Sub', fdata(0, 2, 2)),
                            ('Add', fdata(0, 2, sys.maxsize)),
                            ('LT', fdata(0, 2, 2)),
                            ('GT', fdata(0, 2, 2)),
                            ('LEQ', fdata(0, 2, 2)),
                            ('GEQ', fdata(0, 2, 2)),
                            ('Extract', fdata(2, 1, 1)),
                            ('Concat', fdata(0, 2, 2)),
                            ('Zero_extend', fdata(0, 2, 2)),
                            ('BVAnd', fdata(0, 2, 2)),
                            ('BVOr', fdata(0, 2, 2)),
                            ('BVXor', fdata(0, 2, 2)),
                            ('BVAdd', fdata(0, 2, 2)),
                            ('BVSub', fdata(0, 2, 2)),
                            ('BVMul', fdata(0, 2, 2)),
                            ('BVUdiv', fdata(0, 2, 2)),
                            ('BVUrem', fdata(0, 2, 2)),
                            ('BVShl', fdata(0, 2, 2)),
                            ('BVAshr', fdata(0, 2, 2)),
                            ('BVLshr', fdata(0, 2, 2)),
                            ('BVUlt', fdata(0, 2, 2)),
                            ('BVUle', fdata(0, 2, 2)),
                            ('BVUgt', fdata(0, 2, 2)),
                            ('BVUge', fdata(0, 2, 2)),
                            ('BVSlt', fdata(0, 2, 2)),
                            ('BVSle', fdata(0, 2, 2)),
                            ('BVSgt', fdata(0, 2, 2)),
                            ('BVSge', fdata(0, 2, 2)),
                            ('BVNot', fdata(0, 1, 1)),
                            ('BVNeg', fdata(0, 1, 1)),
                            ('No_op', fdata(0, 0, 0))])


# generate enums for each of these function symbols
func_d = dict()

for fname, i in zip(func_symbols.keys(), range(0, len(func_symbols))):
    func_d[fname] = i

func_enum = enum.Enum('func_enum', func_d)


class operator:
    '''
       Class that wraps all functions

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
        self._fname = fun.__name__
        self._enum = func_enum[fun.__name__]

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
    def fname(self):
        return self._fname

    @property
    def enum(self):
        return self._enum

    @property
    def args(self):
        return self._p.args

    @property
    def keywords(self):
        return self._p.keywords

    def __repr__(self):
        return '<operator: {}, {} {}>'.format(self._fname, self._p.args, self._p.keywords)

    def __call__(self, *args, **kwargs):
        return self._p(*args, **kwargs)

    def __hash__(self):
        return self.func.__hash__()


# generators
def __op_eval(smt, fun, fdata, *args, **kwargs):
    '''
       Takes a function creates an operator for it. All functions are instantiated as an operator
       If the function is not an indexed operator, then it just has no args

       i.e. bvult is  <operator: bvult () {}>  <-- operator with no args

       The operators are callable, and can be used by solver.ApplyFun(operator, *args)
    '''

    # expand out args if list
    if args and isinstance(args[0], list):
        args = args[0]

    # if args:
    #     # Not pretty but trying to avoid circular dependency
    #     s_terms = list(filter(lambda arg: 'TermBase' in
    #                           [base.__name__ for base in arg.__class__.__bases__], args))

    if fun.__class__ == operator:
        # TODO: Also allow keyword arguments -- not urgent

        # if already an operator, then all indices should be assigned
        assert len(fun.args) == fdata.num_indices

        if len(args) > fdata.min_arity:

            if config.strict and len(args) > fdata.max_arity:
                raise ValueError('In strict mode and received {} args when max arity = '
                                 .format(len(args), fdata.max_arity))

            return smt.ApplyFun(fun, *args, **kwargs)

        else:
            return operator(fun.func, *args, **kwargs)

    elif len(args) == fdata.num_indices:

        # check for custom function behavior
        if fdata.num_indices == 0 and fdata.custom and not config.strict:
            return fdata.custom(*args)

        else:
            return operator(fun, *args, **kwargs)

    elif len(args) >= fdata.num_indices + fdata.min_arity:

        if config.strict and len(args) > fdata.max_arity:
            raise ValueError('In strict mode and received {} args when max arity = '
                             .format(len(args), fdata.max_arity))

        # always pass a partial function with the minumum number of arguments
        # this is for CVC4 to construct the function
        return smt.ApplyFun(operator(fun, *args[:fdata.num_indices]),
                            *args[fdata.num_indices:], **kwargs)

    else:
        # check for custom function behavior
        if fdata.custom and not config.strict:
            return fdata.custom(*args)

        elif fdata.num_indices == 0:
            # non-indexed operator
            raise ValueError('Expected {} inputs to operator but received {}'
                             .format(fdata.min_arity, len(args)))
        else:
            raise ValueError('Expected {} or {} inputs to operator but received {}'
                             .format(fdata.num_indices,
                                     fdata.num_indices + fdata.min_arity, len(args)))


def _gen_operator(smt, name, fdata):

    '''
       Generates functions based on the dictionary funcs with the namedtuple
       fdata which contains num_indices, min_arity and max_arity
    '''

    def func(*args):
        return __op_eval(smt, func, fdata, *args)

    func.__name__ = name

    if fdata.num_indices < 0:
        raise ValueError('Invalid expected num_indices in operator {}'.format(name))

    # return function wrapped by operator class
    return operator(func)

from . import sorts
from functools import partial
from ..config import config



def sorts_list(consts):
    '''
       Returns a list of sorts based on the input consts.
       If sort for a particular const is unknown, replaces element with None.
    '''
    return list(map(lambda arg: getattr(arg, 'sort',
                    sorts.py2sort[type(arg)]() if type(arg) in sorts.py2sort
                    else None), consts))


class operator:
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
        self._fname = fun.__name__

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

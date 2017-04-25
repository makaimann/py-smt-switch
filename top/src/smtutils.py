from src import terms
from src import sorts


def sorts_list(consts):
    '''
       Returns a list of sorts based on the input consts.
       If sort for a particular const is unknown, replaces element with None.
    '''
    return list(map(lambda arg:
                    arg.sort if issubclass(arg.__class__, terms.TermBase)
                    else sorts.py2sort[type(arg)]() if type(arg) in sorts.py2sort
                    else None, consts))

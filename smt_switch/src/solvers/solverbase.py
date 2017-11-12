# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from abc import ABCMeta, abstractmethod, abstractproperty
from .. import sorts


class SolverBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, strict):
        self.constraints = []
        self.Sat = None
        self._strict = strict
        self._tosorts = None
        
    @property
    def strict(self):
        return self._strict

    @abstractmethod
    def Reset(self):
        pass

    @abstractmethod
    def CheckSat(self):
        pass

    @abstractmethod
    def SetLogic(self, logicstr):
        pass

    @abstractmethod
    def SetOption(self, optionstr, value):
        pass

    @abstractmethod
    def DeclareFun(self, name, inputsorts, outputsort):
        pass

    @abstractmethod
    def DeclareConst(self, name, sort):
        pass

    @abstractmethod
    def TheoryConst(self, sort, value):
        pass

    @abstractmethod
    def ApplyFun(self, fun, *args):
        pass

    @abstractmethod
    def ApplyCustomFun(self, fun, *args):
        pass

    @abstractmethod
    def Assert(cls, *pargs, **kwargs):
        return cls.Assert(*pargs, **kwargs)

    @abstractproperty
    def Assertions(self):
        pass

    @abstractmethod
    def GetModel(self):
        pass

    @abstractmethod
    def GetValue(self, var):
        pass

    @abstractmethod
    def ToSmt2(self, filename):
        pass

    @abstractmethod
    def Symbol(self, name, sort):
        pass

    @abstractmethod
    def DefineFun(self, name, sortlist, paramlist, fundef):
        pass

    def _translate_sorts(self, sort):
        '''
        Recursive function for translating parameterized sorts
        Hopefully there aren't sorts nested deep enough to
        require more than than the python recursion limit
        --> I would hope not!
        '''

        assert self._tosorts and isinstance(self._tosorts, dict), \
          "Expecting self._tosorts to be defined by subclass"

        if not issubclass(sort.__class__, sorts.SortBase):
            return sort
        elif len(sort.params) == 0:
            return self._tosorts[sort.__class__]()
        else:
            paramlist = [self._translate_sorts(p) for p in sort.params]
            return self._tosorts[sort.__class__](*paramlist)

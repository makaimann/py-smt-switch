# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

from abc import ABCMeta, abstractmethod, abstractproperty


class SolverBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self):
        self.constraints = []
        self.Sat = None

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

from abc import ABCMeta, abstractmethod, abstractproperty


class SolverBase(metaclass=ABCMeta):
    @abstractmethod
    def __init__(self):
        self.constraints = []
        self.sat = None

    def add(self, c):
        ''' Alias for Assert '''
        self.Assert(c)

    @abstractmethod
    def reset(self):
        pass

    @abstractmethod
    def check_sat(self):
        pass

    @abstractmethod
    def set_logic(self, logicstr):
        pass

    @abstractmethod
    def set_option(self, optionstr, value):
        pass

    # right now this doesn't do anything different than set_option in CVC4 implementation
    # because not doing any checks on optionstr in set_option yet
    @abstractmethod
    def set_nonstandard_option(self, optionstr, value):
        pass

    @abstractmethod
    def declare_const(self, name, sort):
        pass

    @abstractmethod
    def theory_const(self, sort, value):
        pass

    @abstractmethod
    def apply_fun(self, fun, *args):
        pass

    @abstractmethod
    def Assert(cls, *pargs, **kwargs):
        return cls.Assert(*pargs, **kwargs)

    @abstractproperty
    def assertions(self):
        pass

    @abstractmethod
    def get_model(self):
        pass

    @abstractmethod
    def get_value(self, var):
        pass

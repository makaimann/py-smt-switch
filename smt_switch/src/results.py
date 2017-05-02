from abc import ABCMeta, abstractmethod


class ResultBase(metaclass=ABCMeta):
    def __init__(self, value):
        self._value = value

    @property
    def value(self):
        return self._value


class CVC4BitVecResult(ResultBase):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return self.value.getConstBitVector().toInteger().toUnsignedInt()


class Z3BitVecResult(ResultBase):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return self.value.as_long()

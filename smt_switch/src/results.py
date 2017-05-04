from abc import ABCMeta
from fractions import Fraction
from ..config import config


class ResultBase(metaclass=ABCMeta):
    def __init__(self, value):
        self._value = value

    @property
    def value(self):
        return self._value


class CVC4Result(ResultBase):
    def __init__(self, value):
        super().__init__(value)

    def __repr__(self):
        return self.value.toString()


class Z3Result(ResultBase):
    def __init__(self, value):
        super().__init__(value)

    def __repr__(self):
        if config.strict:
            return self.value.sexpr()
        else:
            return self.value.__repr__()


class CVC4BitVecResult(CVC4Result):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return self.value.getConstBitVector().toInteger().toUnsignedInt()


class Z3BitVecResult(Z3Result):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return self.value.as_long()

    
class CVC4IntResult(CVC4Result):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return int(self.value.getConstRational().getDouble())


class Z3IntResult(Z3Result):
    def __init__(self, value):
        super().__init__(value)

    def as_int(self):
        return self.value.as_long()


class CVC4RealResult(CVC4Result):
    def __init__(self, value):
        super().__init__(value)

    def as_double(self):
        return self.value.getConstRational().getDouble()

    def as_fraction(self):
        r = self.value.getConstRational()
        return Fraction(r.getNumerator().toUnsignedInt(), r.getDenominator().toUnsignedInt())


class Z3RealResult(Z3Result):
    def __init__(self, value):
        super().__init__(value)

    def as_double(self):
        return float(self.value.as_fraction())

    def as_fraction(self):
        return self.value.as_fraction()


class CVC4BoolResult(CVC4Result):
    def __init__(self, value):
        super().__init__(value)

    def as_bool(self):
        return self.value.getConstBoolean()

    def __bool__(self):
        return self.as_bool()


class Z3BoolResult(Z3Result):
    def __init__(self, value):
        super().__init__(value)

    def as_bool(self):
        return self.value.__bool__()

    def __bool__(self):
        return self.value.__bool__()


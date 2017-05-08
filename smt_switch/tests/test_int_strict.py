import pytest
from smt_switch.config import config
from smt_switch import sorts
from smt_switch import functions
from smt_switch import terms  # used in eval
from . import all_solvers

And = functions.And()
Or = functions.Or()
Ite = functions.Ite()
LT = functions.LT()
LEQ = functions.LEQ()
GT = functions.GT()
GEQ = functions.GEQ()
Plus = functions.Plus()
Sub = functions.Sub()
Equals = functions.Equals()


def test_lia():
    '''
       Solves:              formula #
              i1 + i2 <= 6          1
              i3 - i2 >= 2          2
              i1 == 3               3
              i2 > 0                4
              i3 < 2                5
       Expect UNSAT
    '''
    # set the strict variable before importing other modules
    config.strict = True
    
    for name, solver in all_solvers.items():  # iterate through the solvers
        s = solver()
        s.set_logic('QF_LIA')
        isort = sorts.construct_sort(sorts.Int)
        i1 = s.declare_const('i1', isort)
        i2 = s.declare_const('i2', isort)
        i3 = s.declare_const('i3', isort)
        assert isinstance(i1, eval('terms.{}Term'.format(name)))

        i1plusi2 = s.apply_fun(Plus, i1, i2)
        i3minusi2 = s.apply_fun(Sub, i3, i2)

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == Plus

        six = s.theory_const(isort, 6)
        two = s.theory_const(isort, 2)
        three = s.theory_const(isort, 3)
        zero = s.theory_const(isort, 2)

        formula1 = s.apply_fun(LEQ, i1plusi2, six)
        formula2 = s.apply_fun(GEQ, i3minusi2, two)
        formula3 = s.apply_fun(Equals, i1, three)
        formula4 = s.apply_fun(GT, i2, zero)
        formula5 = s.apply_fun(LT, i3, two)

        assert isinstance(formula1, eval('terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op == LEQ
        assert formula1.sort == sorts.Bool()

        s.Assert(formula1)
        s.Assert(formula2)
        s.Assert(formula3)
        s.Assert(formula4)
        s.Assert(formula5)

        # check satisfiability
        s.check_sat()

        # expect UNSAT
        assert not s.sat

def test_ite():
    '''
       Solves:
              y1 = (ite (> x1 0) x1 0)
              y2 = (ite (> x2 0) x2 0)
              y1 + y2 >= 3
              y1 <= 2
              x2 < 0
       Expect UNSAT
    '''
    config.strict = True

    for name, solver in all_solvers.items():
        s = solver()

        # demonstrating that you don't need to use sorts.construct_sort
        isort = sorts.Int()

        x1 = s.declare_const('x1', isort)
        x2 = s.declare_const('x2', isort)
        assert x1.sort == sorts.Int()
        
        zero = s.theory_const(isort, 0)
        assert isinstance(zero, eval('terms.{}Term'.format(name)))

        x1pos = s.apply_fun(GT, x1, zero)
        x2pos = s.apply_fun(GT, x2, zero)
        assert x1pos.op == GT
        assert x1pos.sort == sorts.Bool()
        assert zero in x1pos.children

        y1 = s.apply_fun(Ite, x1pos, x1, zero)
        y2 = s.apply_fun(Ite, x2pos, x2, zero)
        assert isinstance(y1, eval('terms.{}Term'.format(name)))
        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == sorts.Int()

        y1plusy2 = s.apply_fun(Plus, y1, y2)

        three = s.theory_const(isort, 3)
        y1plusy2GEQ3 = s.apply_fun(GEQ, y1plusy2, three)
        assert y1plusy2GEQ3.op == GEQ
        assert three in y1plusy2GEQ3.children

        two = s.theory_const(isort, 2)
        y1leq2 = s.apply_fun(LEQ, y1, two)
        assert y1leq2.sort == sorts.Bool()

        x2neg = s.apply_fun(LT, x2, zero)
        assert x2neg.__repr__() == '(< x2 0)' or x2neg.__repr__() == '(> 0 x2)'

        # make assertions in solver
        s.Assert(y1plusy2GEQ3)
        s.Assert(y1leq2)
        s.Assert(x2neg)

        # check that sat is not assigned
        assert s.sat is None

        # check satisfiability
        s.check_sat()

        # expect UNSAT
        assert not s.sat


if __name__ == "__main__":
    test_lia()
    test_ite()

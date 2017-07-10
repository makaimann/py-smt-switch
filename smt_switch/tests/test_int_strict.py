import pytest
import smt_switch
from smt_switch.config import config
from smt_switch.tests import all_solvers


smt = smt_switch.smt

And = smt.And
Or = smt.Or
Ite = smt.Ite
LT = smt.LT
LEQ = smt.LEQ
GT = smt.GT
GEQ = smt.GEQ
Add = smt.Add
Sub = smt.Sub
Equals = smt.Equals


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

    for name in all_solvers:  # iterate through the solvers
        smt.set_solver(name)
        smt.set_logic('QF_LIA')
        isort = smt.construct_sort(smt.Int)
        i1 = smt.declare_const('i1', isort)
        i2 = smt.declare_const('i2', isort)
        i3 = smt.declare_const('i3', isort)
        assert isinstance(i1, eval('smt_switch.terms.{}Term'.format(name)))

        i1plusi2 = smt.apply_fun(Add, i1, i2)
        i3minusi2 = smt.apply_fun(Sub, i3, i2)

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == Add

        six = smt.theory_const(isort, 6)
        two = smt.theory_const(isort, 2)
        three = smt.theory_const(isort, 3)
        zero = smt.theory_const(isort, 2)

        formula1 = smt.apply_fun(LEQ, i1plusi2, six)
        formula2 = smt.apply_fun(GEQ, i3minusi2, two)
        formula3 = smt.apply_fun(Equals, i1, three)
        formula4 = smt.apply_fun(GT, i2, zero)
        formula5 = smt.apply_fun(LT, i3, two)

        assert isinstance(formula1, eval('smt_switch.terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op == LEQ
        assert formula1.sort == smt.Bool()

        smt.Assert(formula1)
        smt.Assert(formula2)
        smt.Assert(formula3)
        smt.Assert(formula4)
        smt.Assert(formula5)

        # check satisfiability
        smt.check_sat()

        # expect UNSAT
        assert not smt.sat


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

    for name in all_solvers:
        smt.set_solver(name)

        # demonstrating that you don't need to use smt.construct_sort
        isort = smt.Int()

        x1 = smt.declare_const('x1', isort)
        x2 = smt.declare_const('x2', isort)
        assert x1.sort == smt.Int()
        
        zero = smt.theory_const(isort, 0)
        assert isinstance(zero, eval('smt_switch.terms.{}Term'.format(name)))

        x1pos = smt.apply_fun(GT, x1, zero)
        x2pos = smt.apply_fun(GT, x2, zero)
        assert x1pos.op == GT
        assert x1pos.sort == smt.Bool()
        assert zero in x1pos.children

        y1 = smt.apply_fun(Ite, x1pos, x1, zero)
        y2 = smt.apply_fun(Ite, x2pos, x2, zero)
        assert isinstance(y1, eval('smt_switch.terms.{}Term'.format(name)))
        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == smt.Int()

        y1plusy2 = smt.apply_fun(Add, y1, y2)

        three = smt.theory_const(isort, 3)
        y1plusy2GEQ3 = smt.apply_fun(GEQ, y1plusy2, three)
        assert y1plusy2GEQ3.op == GEQ
        assert three in y1plusy2GEQ3.children

        two = smt.theory_const(isort, 2)
        y1leq2 = smt.apply_fun(LEQ, y1, two)
        assert y1leq2.sort == smt.Bool()

        x2neg = smt.apply_fun(LT, x2, zero)
        assert x2neg.__repr__() == '(< x2 0)' or x2neg.__repr__() == '(> 0 x2)'

        # make assertions in solver
        smt.Assert(y1plusy2GEQ3)
        smt.Assert(y1leq2)
        smt.Assert(x2neg)

        # check that sat is not assigned
        assert smt.sat is None

        # check satisfiability
        smt.check_sat()

        # expect UNSAT
        assert not smt.sat


if __name__ == "__main__":
    test_lia()
    test_ite()

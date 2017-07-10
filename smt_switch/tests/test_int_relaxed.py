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

    config.strict = False

    for name in all_solvers:  # iterate through the solvers
        smt.set_solver(name)
        smt.set_logic('QF_LIA')
        isort = smt.construct_sort(smt.Int)
        i1 = smt.declare_const('i1', isort)
        i2 = smt.declare_const('i2', isort)
        i3 = smt.declare_const('i3', isort)
        assert isinstance(i1, eval('smt_switch.terms.{}Term'.format(name)))

        i1plusi2 = i1 + i2

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == Add

        # demonstrate interpreted python constants
        formula1 = smt.apply_fun(LEQ, i1plusi2, 6)

        # demonstrate overloaded operators
        formula2 = i3 - i2 >= 2

        assert isinstance(formula1, eval('smt_switch.terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op == LEQ
        assert formula1.sort == smt.Bool()

        smt.Assert(formula1)
        smt.Assert(formula2)

        # demonstrate more overloaded operators
        smt.Assert(i1 == 3)
        smt.Assert(i2 > 0)
        smt.Assert(i3 < 2)

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

    config.strict = False

    for name in all_solvers:
        smt.set_solver(name)

        x1 = smt.declare_const('x1', smt.Int())
        x2 = smt.declare_const('x2', smt.Int())
        assert x1.sort == smt.Int()

        x1pos = x1 > 0
        assert x1pos.op == GT
        assert x1pos.sort == smt.Bool()

        y1 = smt.apply_fun(Ite, x1pos, x1, 0)
        assert isinstance(y1, eval('smt_switch.terms.{}Term'.format(name)))

        # demonstrate callable functions 
        y2 = Ite(x2 > 0, x2, 0)

        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == smt.Int()

        y1plusy2GEQ3 = y1 + y2 >= 3
        assert y1plusy2GEQ3.op == GEQ
        three = smt.theory_const(smt.Int(), 3)
        assert three in y1plusy2GEQ3.children
        assert y1plusy2GEQ3.sort == smt.Bool()

        x2neg = smt.apply_fun(LT, x2, 0)
        assert x2neg.__repr__() == 'x2 < 0' or x2neg.__repr__() == '0 > x2'

        # make assertions in solver
        smt.Assert(y1plusy2GEQ3)
        smt.Assert(y1 <= 2)
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

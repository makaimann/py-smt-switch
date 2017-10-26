import pytest
import smt_switch
from smt_switch.tests import all_solvers


smt = smt_switch.smt


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

    for name in all_solvers:  # iterate through the solvers
        s = smt(name)
        s.SetLogic('QF_LIA')
        isort = s.ConstructSort(s.Int)
        i1 = s.DeclareConst('i1', isort)
        i2 = s.DeclareConst('i2', isort)
        i3 = s.DeclareConst('i3', isort)
        assert isinstance(i1, eval('smt_switch.terms.{}Term'.format(name)))

        i1plusi2 = i1 + i2

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == s.Add

        # demonstrate interpreted python constants
        formula1 = s.ApplyFun(s.LEQ, i1plusi2, 6)

        # demonstrate overloaded operators
        formula2 = i3 - i2 >= 2

        assert isinstance(formula1, eval('smt_switch.terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op in {s.LEQ, s.GEQ}  # could be rewritten
        assert formula1.sort == s.Bool()

        s.Assert(formula1)
        s.Assert(formula2)

        # demonstrate more overloaded operators
        s.Assert(i1 == 3)
        s.Assert(i2 > 0)
        s.Assert(i3 < 2)

        # check satisfiability
        s.CheckSat()

        # expect UNSAT
        assert not s.Sat


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

    for name in all_solvers:
        s = smt(name)

        x1 = s.DeclareConst('x1', s.Int())
        x2 = s.DeclareConst('x2', s.Int())
        assert x1.sort == s.Int()

        x1pos = x1 > 0
        assert x1pos.op in {s.GT, s.LT}  # could be rewritten
        assert x1pos.sort == s.Bool()

        y1 = s.ApplyFun(s.Ite, x1pos, x1, 0)
        assert isinstance(y1, eval('smt_switch.terms.{}Term'.format(name)))

        # demonstrate callable functions 
        y2 = s.Ite(x2 > 0, x2, 0)

        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == s.Int()

        y1plusy2GEQ3 = y1 + y2 >= 3
        assert y1plusy2GEQ3.op in {s.GEQ, s.LEQ}  # could be rewritten
        three = s.TheoryConst(s.Int(), 3)
        assert three in y1plusy2GEQ3.children
        assert y1plusy2GEQ3.sort == s.Bool()

        x2neg = s.ApplyFun(s.LT, x2, 0)

        # make Assertions in solver
        s.Assert(y1plusy2GEQ3)
        s.Assert(y1 <= 2)
        s.Assert(x2neg)

        # check that sat is not assigned
        assert s.Sat is None

        # check satisfiability
        s.CheckSat()

        # expect UNSAT
        assert not s.Sat


if __name__ == "__main__":
    test_lia()
    test_ite()

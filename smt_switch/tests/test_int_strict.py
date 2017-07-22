import pytest
import smt_switch
from smt_switch.config import config
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
    # set the strict variable before importing other modules
    config.strict = True

    for name in all_solvers:  # iterate through the solvers
        s = smt(name)
        s.SetLogic('QF_LIA')
        isort = s.ConstructSort(s.Int)
        i1 = s.DeclareConst('i1', isort)
        i2 = s.DeclareConst('i2', isort)
        i3 = s.DeclareConst('i3', isort)
        assert isinstance(i1, eval('smt_switch.terms.{}Term'.format(name)))

        i1plusi2 = s.ApplyFun(s.Add, i1, i2)
        i3minusi2 = s.ApplyFun(s.Sub, i3, i2)

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == s.Add

        six = s.TheoryConst(isort, 6)
        two = s.TheoryConst(isort, 2)
        three = s.TheoryConst(isort, 3)
        zero = s.TheoryConst(isort, 2)

        formula1 = s.ApplyFun(s.LEQ, i1plusi2, six)
        formula2 = s.ApplyFun(s.GEQ, i3minusi2, two)
        formula3 = s.ApplyFun(s.Equals, i1, three)
        formula4 = s.ApplyFun(s.GT, i2, zero)
        formula5 = s.ApplyFun(s.LT, i3, two)

        assert isinstance(formula1, eval('smt_switch.terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op == s.LEQ
        assert formula1.sort == s.Bool()

        s.Assert(formula1)
        s.Assert(formula2)
        s.Assert(formula3)
        s.Assert(formula4)
        s.Assert(formula5)

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
    config.strict = True

    for name in all_solvers:
        s = smt(name)

        # demonstrating that you don't need to use s.ConstructSort
        isort = s.Int()

        x1 = s.DeclareConst('x1', isort)
        x2 = s.DeclareConst('x2', isort)
        assert x1.sort == s.Int()
        
        zero = s.TheoryConst(isort, 0)
        assert isinstance(zero, eval('smt_switch.terms.{}Term'.format(name)))

        x1pos = s.ApplyFun(s.GT, x1, zero)
        x2pos = s.ApplyFun(s.GT, x2, zero)
        assert x1pos.op == s.GT
        assert x1pos.sort == s.Bool()
        assert zero in x1pos.children

        y1 = s.ApplyFun(s.Ite, x1pos, x1, zero)
        y2 = s.ApplyFun(s.Ite, x2pos, x2, zero)
        assert isinstance(y1, eval('smt_switch.terms.{}Term'.format(name)))
        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == s.Int()

        y1plusy2 = s.ApplyFun(s.Add, y1, y2)

        three = s.TheoryConst(isort, 3)
        y1plusy2GEQ3 = s.ApplyFun(s.GEQ, y1plusy2, three)
        assert y1plusy2GEQ3.op == s.GEQ
        assert three in y1plusy2GEQ3.children

        two = s.TheoryConst(isort, 2)
        y1leq2 = s.ApplyFun(s.LEQ, y1, two)
        assert y1leq2.sort == s.Bool()

        x2neg = s.ApplyFun(s.LT, x2, zero)
        assert x2neg.__repr__() == '(< x2 0)' or x2neg.__repr__() == '(> 0 x2)'

        # make Assertions in solver
        s.Assert(y1plusy2GEQ3)
        s.Assert(y1leq2)
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

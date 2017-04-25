import pytest
from smt_switch.config import config
from smt_switch import solvers
from smt_switch import sorts
from smt_switch import functions
from smt_switch import terms  # used in eval

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

    config.strict = False
    
    for name, solver in solvers.solvers.items():  # iterate through the solvers
        s = solver()
        s.set_logic('QF_LIA')
        isort = sorts.construct_sort(sorts.Int)
        i1 = s.declare_const('i1', isort)
        i2 = s.declare_const('i2', isort)
        i3 = s.declare_const('i3', isort)
        assert isinstance(i1, eval('terms.{}Term'.format(name)))

        i1plusi2 = i1 + i2

        assert i1 in i1plusi2.children
        assert i2 in i1plusi2.children
        assert i1plusi2.op == Plus

        # demonstrate interpreted python constants
        formula1 = s.apply_fun(LEQ, i1plusi2, 6)

        # demonstrate overloaded operators
        formula2 = i3 - i2 >= 2
    
        assert isinstance(formula1, eval('terms.{}Term'.format(name)))
        assert i1plusi2 in formula1.children
        assert formula1.op == LEQ
        assert formula1.sort == sorts.Bool()

        s.Assert(formula1)
        s.Assert(formula2)

        # demonstrate more overloaded operators
        s.Assert(i1 == 3)
        s.Assert(i2 > 0)
        s.Assert(i3 < 2)

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

    config.strict = False

    for name, solver in solvers.solvers.items():
        s = solver()

        x1 = s.declare_const('x1', sorts.Int())
        x2 = s.declare_const('x2', sorts.Int())
        assert x1.sort == sorts.Int()

        x1pos = x1 > 0
        assert x1pos.op == GT
        assert x1pos.sort == sorts.Bool()

        y1 = s.apply_fun(Ite, x1pos, x1, 0)
        assert isinstance(y1, eval('terms.{}Term'.format(name)))
        
        # demonstrate callable functions 
        y2 = Ite(x2 > 0, x2, 0)
        
        assert x1 in y1.children
        assert x1pos in y1.children
        assert y1.sort == sorts.Int()

        y1plusy2GEQ3 = y1 + y2 >= 3
        assert y1plusy2GEQ3.op == GEQ
        three = s.theory_const(sorts.Int(), 3)
        assert three in y1plusy2GEQ3.children
        assert y1plusy2GEQ3.sort == sorts.Bool()

        x2neg = s.apply_fun(LT, x2, 0)
        assert x2neg.__repr__() == 'x2 < 0' or x2neg.__repr__() == '0 > x2'

        # make assertions in solver
        s.Assert(y1plusy2GEQ3)
        s.Assert(y1 <= 2)
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

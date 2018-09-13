import pytest
from smt_switch import smt
from smt_switch.tests import bv_solvers, all_logic_solvers
import itertools

def test_consts():
    '''
    Check that there are no errors creating constants

    Instantiate two identical constants and check that they're not equal
        expecting unsat of course.

    Also checking that there are no unhandled cases or exceptions.
    '''

    for name in bv_solvers:
        s = smt(name)
        s.SetLogic('QF_BV')
        a = s.TheoryConst(s.BitVec(4), 5)
        b = s.TheoryConst(s.BitVec(4), 5)
        s.Assert(a != b)
        assert not s.CheckSat(), "Expected unsat for simple constant test. Solver={}".format(name)

    consts = [(s.Int, 2), (s.Real, 4.5)]

    for name, t in itertools.product(all_logic_solvers, consts):
        s = smt(name)
        sort, const = t
        a = s.TheoryConst(sort(), const)
        b = s.TheoryConst(sort(), const)
        s.Assert(a != b)
        assert not s.CheckSat(), "Expected unsat for simple constant test. Solver={}".format(name)


if __name__ == "__main__":
    test_consts()

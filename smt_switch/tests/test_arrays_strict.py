import pytest
from smt_switch import smt
from smt_switch.tests import all_logic_solvers


def test_unsat_array():
    '''
    Simple example demonstrating array axiom
    '''

    for name in all_logic_solvers:
        s = smt(name)
        s.SetLogic('QF_ABV')

        bvsort8 = s.ConstructSort(s.BitVec, 8)
        bvsort4 = s.ConstructSort(s.BitVec, 4)
        arrsort = s.ConstructSort(s.Array, bvsort8, bvsort4)

        A = s.DeclareConst('A', arrsort)

        bvidx = s.DeclareConst("bvidx", bvsort8)
        bv_d1 = s.DeclareConst("bv_d1", bvsort4)
        bv_d2 = s.DeclareConst("bv_d2", bvsort4)

        newA = s.ApplyFun(s.Store, A, bvidx, bv_d1)
        s.Assert(s.ApplyFun(s.Not, s.ApplyFun(s.Equals, bv_d1, bv_d2)))
        bvatidx = s.ApplyFun(s.Select, newA, bvidx)
        s.Assert(s.ApplyFun(s.Equals, bvatidx, bv_d2))

        assert not s.CheckSat()


def test_sat_array():
    '''
    Simple array test
    '''
    for name in all_logic_solvers:
        s = smt(name)
        s.SetLogic('QF_ABV')
        s.SetOption("produce-models", 'true')

        bvsort8 = s.ConstructSort(s.BitVec, 8)
        bvsort4 = s.ConstructSort(s.BitVec, 4)
        arrsort = s.ConstructSort(s.Array, bvsort8, bvsort4)

        A = s.DeclareConst('A', arrsort)

        bvidx = s.DeclareConst("bvidx", bvsort8)
        bvidx2 = s.DeclareConst("bvidx2", bvsort8)
        bv_d1 = s.DeclareConst("bv_d1", bvsort4)
        bv_d2 = s.DeclareConst("bv_d2", bvsort4)

        A1 = s.ApplyFun(s.Store, A, bvidx, bv_d1)
        A2 = s.ApplyFun(s.Store, A1, bvidx2, bv_d2)

        bvidxp2 = s.ApplyFun(s.BVAdd, bvidx, s.TheoryConst(bvsort8, 2))
        s.Assert(s.ApplyFun(s.Equals, bvidx2, bvidxp2))

        bv_d2sh1 = s.ApplyFun(s.BVLshr, bv_d2, s.TheoryConst(bvsort4, 1))
        s.Assert(s.ApplyFun(s.Equals, bv_d1, bv_d2sh1))

        s.CheckSat()

        av = s.GetValue(A2).as_list() # returns list of tuples


if __name__ == "__main__":
    test_unsat_array()
    test_sat_array()

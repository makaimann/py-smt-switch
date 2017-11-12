import pytest
from smt_switch import smt
from smt_switch.tests import all_logic_solvers


def test_definefun():

    # z3 does not support function macros through api
    for name in ["CVC4", "Boolector"]:
        s = smt(name)
        s.SetLogic("QF_BV")

        s.SetOption("produce-models", "true")

        bv1s = s.Symbol("bv1s", s.BitVec(4))
        bv2s = s.Symbol("bv2s", s.BitVec(4))

        f = s.DefineFun("f", [bv1s, bv2s], bv1s + bv2s)

        bv1 = s.DeclareConst("bv1", s.BitVec(4))
        bv2 = s.DeclareConst("bv2", s.BitVec(4))
        bv3 = s.DeclareConst("bv3", s.BitVec(4))

        s.Assert(bv1 == 4)

        s.Assert(f(bv1, bv2) == bv3)

        assert s.CheckSat()

        bv1v = s.GetValue(bv1).as_int()
        bv2v = s.GetValue(bv2).as_int()
        bv3v = s.GetValue(bv3).as_int()

        assert bv3v == bv1v + bv2v


if __name__ == "__main__":
    test_definefun()

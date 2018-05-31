import pytest
from smt_switch import smt
from smt_switch.tests import fp_solvers

def test_basic():
    '''
    Very basic floating point test
    '''

    for name in fp_solvers:
        s = smt(name, strict=True)
        s.SetLogic("QF_FP")

        bvsort1 = s.ConstructSort(s.BitVec, 1)
        bvsort8 = s.ConstructSort(s.BitVec, 8)
        bvsort24 = s.ConstructSort(s.BitVec, 24)

        fpsort8_24 = s.ConstructSort(s.FP, 8, 24)

        b0 = s.TheoryConst(bvsort1, 0)
        b200 = s.TheoryConst(bvsort8, 200)
        b468 = s.TheoryConst(bvsort24, 468)

        f = s.TheoryConst(fpsort8_24, b0, b200, b468)
        f2 = s.TheoryConst(fpsort8_24, b0, b200, b468)

        fc = s.DeclareConst("fc", fpsort8_24)

        fpf2 = s.ApplyFun(s.FPAdd, s.Round.RNE, f, f2)

if __name__ == "__main__":
    test_basic()

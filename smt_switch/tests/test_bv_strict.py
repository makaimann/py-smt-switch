import pytest
from smt_switch import smt
from smt_switch.tests import bv_solvers


def test_bv_extract():
    '''
       Simple bitvector example based on CVC4 extract.cpp example
    '''

    for name in bv_solvers:
        s = smt(name, strict=True)

        # create bitvector type of width 32
        bvsort = s.ConstructSort(s.BitVec, 32)

        s.SetLogic('QF_BV')

        x = s.DeclareConst('x', bvsort)

        ext_31_1 = s.ConstructFun(s.Extract, 31, 1)
        x_31_1 = s.ApplyFun(ext_31_1, x)

        ext_30_0 = s.ConstructFun(s.Extract, 30, 0)
        x_30_0 = s.ApplyFun(ext_30_0, x)

        ext_31_31 = s.ConstructFun(s.Extract, 31, 31)
        x_31_31 = s.ApplyFun(ext_31_31, x)

        ext_0_0 = s.ConstructFun(s.Extract, 0, 0)
        x_0_0 = s.ApplyFun(ext_0_0, x)

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        assert x_31_1.sort == s.BitVec(31)

        eq = s.ApplyFun(s.Equals, x_31_1, x_30_0)

        if name != 'Boolector':
            # boolector does not keep string representation of formulas
            print('Asserting', eq)
            # Boolector is streamlined/optimized and does not keep track of op
            assert x_31_31.op == s.Extract(31, 31)

    
        s.Assert(eq)

        eq2 = s.ApplyFun(s.Equals, x_31_31, x_0_0)
        s.Assert(eq2)

        s.CheckSat()

        assert s.Sat  # in fact it's actually valid


def test_bv_boolops():
    '''
       Sets
           bv1 = 00001111
           bv2 = 11110000
           bv3 = 01010101
       Then computes:
           bv1 and bv2
           bv2 or bv3
           not bv3
    '''

    for name in bv_solvers:
        s = smt(name, strict=True)

        bvand = s.BVAnd
        bvor = s.BVOr
        bvnot = s.BVNot
        Equals = s.Equals

        bvsort = s.BitVec(8)

        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bv1 = s.DeclareConst('bv1', bvsort)
        bv2 = s.DeclareConst('bv2', bvsort)
        bv3 = s.DeclareConst('bv3', bvsort)

        bvresult = s.DeclareConst('bvresult', bvsort)
        bvresult2 = s.DeclareConst('bvresult2', bvsort)
        bvnotresult = s.DeclareConst('bvnotresult', bvsort)

        bv1andbv2 = s.ApplyFun(bvand, bv1, bv2)
        bv2orbv3 = s.ApplyFun(bvor, bv2, bv3)
        notbv3 = s.ApplyFun(bvnot, bv3)

        assert bv2orbv3.sort == s.BitVec(8)

        if name != 'Boolector':
            assert bv2orbv3.op == bvor

        bvresulteq = s.ApplyFun(Equals, bvresult, bv1andbv2)
        bvresult2eq = s.ApplyFun(Equals, bvresult2, bv2orbv3)

        bvnotresulteq = s.ApplyFun(Equals, bvnotresult, notbv3)

        assert bvnotresulteq.sort == s.Bool() or bvnotresulteq.sort == s.BitVec(1)

        fifteen = s.TheoryConst(bvsort, 15)
        twoforty = s.TheoryConst(bvsort, 240)
        eightyfive = s.TheoryConst(bvsort, 85)

        bv1eq = s.ApplyFun(Equals, bv1, fifteen)
        bv2eq = s.ApplyFun(Equals, bv2, twoforty)
        bv3eq = s.ApplyFun(Equals, bv3, eightyfive)

        # Assert formulas
        s.Assert(bvresulteq)
        s.Assert(bvresult2eq)
        s.Assert(bvnotresulteq)
        s.Assert(bv1eq)
        s.Assert(bv2eq)
        s.Assert(bv3eq)

        # check satisfiability
        s.CheckSat()

        # now query for the values
        bvr1 = s.GetValue(bvresult)
        bvr2 = s.GetValue(bvresult2)
        bvnr = s.GetValue(bvnotresult)

        # make Assertions about values
        # still figuring out how to get z3 and boolector to print s-lib format for results
        # assert bvr1.__repr__() == '(_ bv0 8)' or bvr1.__repr__() == '#x00'
        # assert bvr2.__repr__() == '(_ bv245 8)' or bvr2.__repr__() == '#xf5'
        # assert bvnr.__repr__() == '(_ bv170 8)' or bvnr.__repr__() == '#xaa'
        assert bvr1.as_int() == 0
        assert bvr2.as_int() == 245
        assert bvnr.as_int() == 170


def test_bv_arithops():
    '''
       Set 
          bv1 = 0001
          bv2 = 0010
          bv3 = 0101
       Then compute:
          bv1 + bv2
          bv2*bv3
          bv3 >> 1
    '''

    for name in bv_solvers:
        s = smt(name, strict=True)

        bvadd = s.BVAdd
        bvmul = s.BVMul
        bvlshr = s.BVLshr
        Equals = s.Equals

        bvsort = s.BitVec(4)

        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bv1 = s.DeclareConst('bv1', bvsort)
        bv2 = s.DeclareConst('bv2', bvsort)
        bv3 = s.DeclareConst('bv3', bvsort)

        one = s.TheoryConst(bvsort, 1)
        two = s.TheoryConst(bvsort, 2)
        five = s.TheoryConst(bvsort, 5)

        bv1eq = s.ApplyFun(Equals, bv1, one)
        bv2eq = s.ApplyFun(Equals, bv2, two)
        bv3eq = s.ApplyFun(Equals, bv3, five)

        bvsum = s.DeclareConst('bvsum', bvsort)
        bvprod = s.DeclareConst('bvprod', bvsort)
        bvshifted = s.DeclareConst('bvshifted', bvsort)

        bvsumval = s.ApplyFun(bvadd, bv1, bv2)
        bvprodval = s.ApplyFun(bvmul, bv2, bv3)
        bvshiftedval = s.ApplyFun(bvlshr, bv3, one)

        bvsumeq = s.ApplyFun(Equals, bvsum, bvsumval)
        bvprodeq = s.ApplyFun(Equals, bvprod, bvprodval)
        bvshiftedeq = s.ApplyFun(Equals, bvshifted, bvshiftedval)

        #make Assertions
        s.Assert(bv1eq)
        s.Assert(bv2eq)
        s.Assert(bv3eq)
        s.Assert(bvsumeq)
        s.Assert(bvprodeq)
        s.Assert(bvshiftedeq)

        # check satisfiability
        s.CheckSat()

        bvsumr = s.GetValue(bvsum)
        bvprodr = s.GetValue(bvprod)
        bvshiftedr = s.GetValue(bvshifted)

        # still figuring out how to get z3 and boolector to print s-lib format for results
        # assert bvsumr.__repr__() == '(_ bv3 4)' or bvsumr.__repr__() == '#x3'
        # assert bvprodr.__repr__() == '(_ bv10 4)' or bvprodr.__repr__() == '#xa'
        # assert bvshiftedr.as_int() == 2
        assert bvsumr.as_int() == 3
        assert bvprodr.as_int() == 10
        assert bvshiftedr.as_int() == 2


if __name__ == "__main__":
    test_bv_extract()
    test_bv_boolops()
    test_bv_arithops()

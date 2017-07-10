import pytest
from smt_switch import smt
from smt_switch.config import config
from smt_switch.tests import bv_solvers


def test_bv_extract():
    '''
       Simple bitvector example based on CVC4 extract.cpp example
    '''
    config.strict = True

    # create bitvector type of width 32
    bvsort = smt.construct_sort(smt.BitVec, 32)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')

        x = smt.declare_const('x', bvsort)

        ext_31_1 = smt.construct_fun(smt.Extract, 31, 1)
        x_31_1 = smt.apply_fun(ext_31_1, x)

        ext_30_0 = smt.construct_fun(smt.Extract, 30, 0)
        x_30_0 = smt.apply_fun(ext_30_0, x)

        ext_31_31 = smt.construct_fun(smt.Extract, 31, 31)
        x_31_31 = smt.apply_fun(ext_31_31, x)

        ext_0_0 = smt.construct_fun(smt.Extract, 0, 0)
        x_0_0 = smt.apply_fun(ext_0_0, x)

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        assert x_31_1.sort == smt.BitVec(31)

        assert x_31_31.op == smt.Extract(31, 31)

        eq = smt.apply_fun(smt.Equals, x_31_1, x_30_0)

        if name != 'Boolector':
            # boolector does not keep string representation of formulas
            # eventually I'll just implement this myself
            print('Asserting', eq)
    
        smt.Assert(eq)

        eq2 = smt.apply_fun(smt.Equals, x_31_31, x_0_0)
        smt.Assert(eq2)

        smt.check_sat()

        assert smt.sat  # in fact it's actually valid


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
    config.strict = True

    bvand = smt.BVAnd
    bvor = smt.BVOr
    bvnot = smt.BVNot
    Equals = smt.Equals

    bvsort = smt.BitVec(8)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')
        smt.set_option('produce-models', 'true')

        bv1 = smt.declare_const('bv1', bvsort)
        bv2 = smt.declare_const('bv2', bvsort)
        bv3 = smt.declare_const('bv3', bvsort)

        bvresult = smt.declare_const('bvresult', bvsort)
        bvresult2 = smt.declare_const('bvresult2', bvsort)
        bvnotresult = smt.declare_const('bvnotresult', bvsort)

        bv1andbv2 = smt.apply_fun(bvand, bv1, bv2)
        bv2orbv3 = smt.apply_fun(bvor, bv2, bv3)
        notbv3 = smt.apply_fun(bvnot, bv3)

        assert bv2orbv3.sort == smt.BitVec(8)
        assert bv2orbv3.op == bvor

        bvresulteq = smt.apply_fun(Equals, bvresult, bv1andbv2)
        bvresult2eq = smt.apply_fun(Equals, bvresult2, bv2orbv3)

        bvnotresulteq = smt.apply_fun(Equals, bvnotresult, notbv3)

        assert bvnotresulteq.sort == smt.Bool()

        fifteen = smt.theory_const(bvsort, 15)
        twoforty = smt.theory_const(bvsort, 240)
        eightyfive = smt.theory_const(bvsort, 85)

        bv1eq = smt.apply_fun(Equals, bv1, fifteen)
        bv2eq = smt.apply_fun(Equals, bv2, twoforty)
        bv3eq = smt.apply_fun(Equals, bv3, eightyfive)

        # Assert formulas
        smt.Assert(bvresulteq)
        smt.Assert(bvresult2eq)
        smt.Assert(bvnotresulteq)
        smt.Assert(bv1eq)
        smt.Assert(bv2eq)
        smt.Assert(bv3eq)

        # check satisfiability
        smt.check_sat()

        # now query for the values
        bvr1 = smt.get_value(bvresult)
        bvr2 = smt.get_value(bvresult2)
        bvnr = smt.get_value(bvnotresult)

        # make assertions about values
        # still figuring out how to get z3 and boolector to print smt-lib format for results
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

    bvadd = smt.BVAdd
    bvmul = smt.BVMul
    bvlshr = smt.BVLshr
    Equals = smt.Equals

    bvsort = smt.BitVec(4)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')
        smt.set_option('produce-models', 'true')

        bv1 = smt.declare_const('bv1', bvsort)
        bv2 = smt.declare_const('bv2', bvsort)
        bv3 = smt.declare_const('bv3', bvsort)

        one = smt.theory_const(bvsort, 1)
        two = smt.theory_const(bvsort, 2)
        five = smt.theory_const(bvsort, 5)

        bv1eq = smt.apply_fun(Equals, bv1, one)
        bv2eq = smt.apply_fun(Equals, bv2, two)
        bv3eq = smt.apply_fun(Equals, bv3, five)

        bvsum = smt.declare_const('bvsum', bvsort)
        bvprod = smt.declare_const('bvprod', bvsort)
        bvshifted = smt.declare_const('bvshifted', bvsort)

        bvsumval = smt.apply_fun(bvadd, bv1, bv2)
        bvprodval = smt.apply_fun(bvmul, bv2, bv3)
        bvshiftedval = smt.apply_fun(bvlshr, bv3, one)

        bvsumeq = smt.apply_fun(Equals, bvsum, bvsumval)
        bvprodeq = smt.apply_fun(Equals, bvprod, bvprodval)
        bvshiftedeq = smt.apply_fun(Equals, bvshifted, bvshiftedval)

        #make assertions
        smt.Assert(bv1eq)
        smt.Assert(bv2eq)
        smt.Assert(bv3eq)
        smt.Assert(bvsumeq)
        smt.Assert(bvprodeq)
        smt.Assert(bvshiftedeq)

        # check satisfiability
        smt.check_sat()

        bvsumr = smt.get_value(bvsum)
        bvprodr = smt.get_value(bvprod)
        bvshiftedr = smt.get_value(bvshifted)

        # still figuring out how to get z3 and boolector to print smt-lib format for results
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

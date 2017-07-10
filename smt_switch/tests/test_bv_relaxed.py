import pytest
from smt_switch import smt
from smt_switch.config import config
from smt_switch.tests import bv_solvers


Equals = smt.Equals
bvuge = smt.BVUge
And = smt.And


def test_bv_ops():
    '''
       bitvector example using overloaded operators
    '''

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')
        smt.set_option('produce-models', 'true')

        bv8 = smt.BitVec(8)

        bv1 = smt.declare_const('bv1', bv8)
        bv2 = smt.declare_const('bv2', smt.BitVec(8))

        c = [bvuge(bv1, 1)]

        bvs = [bv1, bv2]

        for i in range(3, 11):
            bvs.append(smt.declare_const('bv{}'.format(i), bv8))

        for b1, b2, b3 in zip(bvs, bvs[1:], bvs[2:]):
            c.append(b1 + b2 == b3)

        smt.Assert(And(c))

        smt.Assert(((bvs[9] << 4) >> 4) == bvs[6])
        smt.Assert(bvs[5] == 3)
        smt.Assert(bvs[8] - 6 == 7)

        r = smt.check_sat()
        assert r

        bvvals = [smt.get_value(bv).as_int() for bv in bvs]

        for b1, b2, b3 in zip(bvvals, bvvals[1:], bvvals[2:]):
            assert b1 + b2 == b3


def test_bv_extract():
    '''
       Simple bitvector example based on CVC4 extract.cpp example
    '''

    config.strict = False

    # create bitvector type of width 32
    bvsort = smt.construct_sort(smt.BitVec, 32)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')

        x = smt.declare_const('x', bvsort)

        ext_31_1 = smt.construct_fun(smt.Extract, 31, 1)
        x_31_1 = ext_31_1(x)

        ext_30_0 = smt.construct_fun(smt.Extract, 30, 0)
        x_30_0 = ext_30_0(x)

        x_31_31 = smt.Extract(31, 31, x)

        x_0_0 = smt.Extract(0, 0, x)

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        assert x_31_1.op == smt.Extract(31, 1)

        assert x_31_1.sort == smt.BitVec(31)

        print('Asserting x_31_1 == x_30_0')
        smt.Assert(x_31_1 == x_30_0)

        eq2 = x_31_31 == x_0_0
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
    config.strict = False
    
    bvand = smt.BVAnd
    bvor = smt.BVOr
    bvnot = smt.BVNot

    bvsort = smt.BitVec(8)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')
        smt.set_option('produce-models', 'true')
        
        bv1 = smt.declare_const('bv1', bvsort)
        bv2 = smt.declare_const('bv2', bvsort)
        bv3 = smt.declare_const('bv3', bvsort)

        bvresult = bvand(bv1, bv2)
        bvresult2 = bvor(bv2, bv3)
        bvnotresult = bvnot(bv3)

        assert bvresult2.sort == smt.BitVec(8)
        assert bvresult2.op == bvor

        # Assert formulas
        smt.Assert(bv1 == 15)
        smt.Assert(bv2 == 240)
        smt.Assert(bv3 == 85)

        # check satisfiability
        smt.check_sat()

        # now query for the values
        bvr1 = smt.get_value(bvresult)
        bvr2 = smt.get_value(bvresult2)
        bvnr = smt.get_value(bvnotresult)

        # make assertions about values
        # still figuring out how to get z3 and boolector to print smt-lib format for results
        # assert bvr1.__repr__() == '0' or bvr1.__repr__() == '0bin00000000'
        # assert bvr2.__repr__() == '245' or bvr2.__repr__() == '0bin11110101'
        # assert bvnr.__repr__() == '170' or bvnr.__repr__() == '0bin10101010'
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
    config.strict = False

    bvmul = smt.BVMul

    bvsort = smt.BitVec(4)

    for name in bv_solvers:
        smt.set_solver(name)
        smt.set_logic('QF_BV')
        smt.set_option('produce-models', 'true')
        
        bv1 = smt.declare_const('bv1', bvsort)
        bv2 = smt.declare_const('bv2', bvsort)
        bv3 = smt.declare_const('bv3', bvsort)

        bvsum = bv1 + bv2
        bvprod = bvmul(bv2, bv3)
        bvshifted = bv3 >> 1

        # make assertions
        smt.Assert(bv1 == 1)
        smt.Assert(bv2 == 2)
        smt.Assert(bv3 == 5)

        # check satisfiability
        smt.check_sat()

        bvsumr = smt.get_value(bvsum)
        bvprodr = smt.get_value(bvprod)
        bvshiftedr = smt.get_value(bvshifted)

        # still figuring out how to get z3 and boolector to print smt-lib format for results
        # assert bvsumr.__repr__() == '3' or bvsumr.__repr__() == '0bin0011'
        # assert bvprodr.__repr__() == '10' or bvprodr.__repr__() == '0bin1010'
        # assert bvshiftedr.as_int() == 2
        assert bvsumr.as_int() == 3
        assert bvprodr.as_int() == 10
        assert bvshiftedr.as_int() == 2

if __name__ == "__main__":
    test_bv_ops()
    test_bv_extract()
    test_bv_boolops()
    test_bv_arithops()

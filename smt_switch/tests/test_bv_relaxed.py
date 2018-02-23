import pytest
from smt_switch import smt
from smt_switch.tests import bv_solvers


def test_bv_ops():
    '''
       bitvector example using overloaded operators
    '''

    for name in bv_solvers:
        s = smt(name)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bvuge = s.BVUge
        And = s.And

        bv8 = s.BitVec(8)

        bv1 = s.DeclareConst('bv1', bv8)
        bv2 = s.DeclareConst('bv2', s.BitVec(8))

        c = [bvuge(bv1, 1)]

        bvs = [bv1, bv2]

        for i in range(3, 11):
            bvs.append(s.DeclareConst('bv{}'.format(i), bv8))

        for b1, b2, b3 in zip(bvs, bvs[1:], bvs[2:]):
            c.append(b1 + b2 == b3)

        s.Assert(And(c))

        s.Assert(((bvs[9] << 4) >> 4) == bvs[6])
        s.Assert(bvs[5] == 3)
        s.Assert(bvs[8] - 6 == 7)

        r = s.CheckSat()
        assert r

        bvvals = [s.GetValue(bv).as_int() for bv in bvs]

        for b1, b2, b3 in zip(bvvals, bvvals[1:], bvvals[2:]):
            assert b1 + b2 == b3


def test_bv_extract():
    '''
       Simple bitvector example based on CVC4 extract.cpp example
    '''

    for name in bv_solvers:
        s = smt(name)
        s.SetLogic('QF_BV')

        # create bitvector type of width 32
        bvsort = s.ConstructSort(s.BitVec, 32)

        x = s.DeclareConst('x', bvsort)

        ext_31_1 = s.ConstructFun(s.Extract, 31, 1)
        x_31_1 = ext_31_1(x)

        x_31_31 = s.Extract(31, 31, x)

        # You can also use slicing notation
        x_30_0 = x[30:0]

        # or if you just want one bit, use it as an index
        x_0_0 = x[0]

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        if name != 'Boolector':
            # Boolector is streamlined/optimized and does not keep track of op
            assert x_31_1.op == s.Extract(31, 1)

        assert x_31_1.sort == s.BitVec(31)

        print('Asserting x_31_1 == x_30_0')
        s.Assert(x_31_1 == x_30_0)

        eq2 = x_31_31 == x_0_0
        s.Assert(eq2)

        s.CheckSat()

        assert s.Sat  # in fact it's actually valid


def test_bv_multdivide():
    '''
    Simple bitvector example with multiply and divide operators
    '''
    for name in bv_solvers:
        print(name)
        s = smt(name)
        s.SetLogic("QF_BV")
        s.SetOption("produce-models", 'true')

        x = s.DeclareConst('x', s.BitVec(16))
        y = s.DeclareConst('y', s.BitVec(16))

        s.Assert(3*x + y == 16)
        s.Assert(y/5 == 2)
        s.Assert(y % 8 == 2)

        s.CheckSat()
        assert s.GetValue(x).as_int() == 2
        assert s.GetValue(y).as_int() == 10


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
        s = smt(name)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bvand = s.BVAnd
        bvor = s.BVOr
        bvnot = s.BVNot

        bvsort = s.BitVec(8)

        bv1 = s.DeclareConst('bv1', bvsort)
        bv2 = s.DeclareConst('bv2', bvsort)
        bv3 = s.DeclareConst('bv3', bvsort)

        bvresult = bvand(bv1, bv2)
        bvresult2 = bvor(bv2, bv3)
        bvnotresult = bvnot(bv3)

        assert bvresult2.sort == s.BitVec(8)

        if name != 'Boolector':
            # Boolector is streamlined/optimized and does not support querying opt
            assert bvresult2.op == bvor

        # Assert formulas
        s.Assert(bv1 == 15)
        s.Assert(bv2 == 240)
        s.Assert(bv3 == 85)

        # check satisfiability
        s.CheckSat()

        # now query for the values
        bvr1 = s.GetValue(bvresult)
        bvr2 = s.GetValue(bvresult2)
        bvnr = s.GetValue(bvnotresult)

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
        s = smt(name)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bvmul = s.BVMul
        bvsort = s.BitVec(4)

        bv1 = s.DeclareConst('bv1', bvsort)
        bv2 = s.DeclareConst('bv2', bvsort)
        bv3 = s.DeclareConst('bv3', bvsort)

        bvsum = bv1 + bv2
        bvprod = bvmul(bv2, bv3)
        bvshifted = bv3 >> 1

        # make Assertions
        s.Assert(bv1 == 1)
        s.Assert(bv2 == 2)
        s.Assert(bv3 == 5)

        # check satisfiability
        s.CheckSat()

        bvsumr = s.GetValue(bvsum)
        bvprodr = s.GetValue(bvprod)
        bvshiftedr = s.GetValue(bvshifted)

        # still figuring out how to get z3 and boolector to print s-lib format for results
        # assert bvsumr.__repr__() == '3' or bvsumr.__repr__() == '0bin0011'
        # assert bvprodr.__repr__() == '10' or bvprodr.__repr__() == '0bin1010'
        # assert bvshiftedr.as_int() == 2
        assert bvsumr.as_int() == 3
        assert bvprodr.as_int() == 10
        assert bvshiftedr.as_int() == 2

def test_bv128():
    for name in bv_solvers:
        s = smt(name)
        s.SetOption('produce-models', 'true')
        s.SetLogic('QF_BV')
        bv = s.DeclareConst('bv', s.BitVec(128))
        import sys
        bignum = s.TheoryConst(s.BitVec(128), sys.maxsize)
        s.Assert(s.BVUgt(bv, bignum))
        s.CheckSat()
        v = s.GetValue(bv)
        try:
            v.as_bitstr()
        except Exception:
            assert False, 'Issue representing bit vector of width 128'


def test_r_ops():
    for name in bv_solvers:
        s = smt(name)
        s.SetOption('produce-models', 'true')
        s.SetLogic('QF_BV')

        bvsort8 = s.BitVec(8)
        x1 = s.DeclareConst('x1', bvsort8)
        x2 = s.DeclareConst('x2', bvsort8)
        x3 = s.DeclareConst('x3', bvsort8)


if __name__ == "__main__":
    test_bv_ops()
    test_bv_multdivide()
    test_bv_extract()
    test_bv_boolops()
    test_bv_arithops()
    test_bv128()

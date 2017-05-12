import pytest
from smt_switch.config import config
from smt_switch import sorts
from smt_switch import functions
from smt_switch.tests import bv_solvers


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


def test_bv_extract():
    '''
       Simple bitvector example based on CVC4 extract.cpp example
    '''
    config.strict = True
    
    # create bitvector type of width 32
    bvsort = sorts.construct_sort(sorts.BitVec, 32)

    for name, solver in bv_solvers.items():
        s = solver()
        s.set_logic('QF_BV')

        x = s.declare_const('x', bvsort)

        ext_31_1 = functions.declare_fun(functions.extract, 31, 1)
        x_31_1 = s.apply_fun(ext_31_1, x)

        ext_30_0 = functions.declare_fun(functions.extract, 30, 0)
        x_30_0 = s.apply_fun(ext_30_0, x)

        ext_31_31 = functions.declare_fun(functions.extract, 31, 31)
        x_31_31 = s.apply_fun(ext_31_31, x)

        ext_0_0 = functions.declare_fun(functions.extract, 0, 0)
        x_0_0 = s.apply_fun(ext_0_0, x)

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        assert x_31_31.op == functions.extract(31, 31)

        eq = s.apply_fun(Equals, x_31_1, x_30_0)

        if name != 'Boolector':
            # boolector does not keep string representation of formulas
            # eventually I'll just implement this myself
            print('Asserting', eq)
    
        s.Assert(eq)

        eq2 = s.apply_fun(Equals, x_31_31, x_0_0)
        s.Assert(eq2)

        s.check_sat()

        assert s.sat  # in fact it's actually valid


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
    
    bvand = functions.bvand()
    bvor = functions.bvor()
    bvnot = functions.bvnot()

    bvsort = sorts.BitVec(8)

    for name, solver in bv_solvers.items():
        s = solver()
        s.set_logic('QF_BV')
        s.set_option('produce-models', 'true')
        
        bv1 = s.declare_const('bv1', bvsort)
        bv2 = s.declare_const('bv2', bvsort)
        bv3 = s.declare_const('bv3', bvsort)

        bvresult = s.declare_const('bvresult', bvsort)
        bvresult2 = s.declare_const('bvresult2', bvsort)
        bvnotresult = s.declare_const('bvnotresult', bvsort)

        bv1andbv2 = s.apply_fun(bvand, bv1, bv2)
        bv2orbv3 = s.apply_fun(bvor, bv2, bv3)
        notbv3 = s.apply_fun(bvnot, bv3)

        assert bv2orbv3.sort == sorts.BitVec(8)
        assert bv2orbv3.op == functions.bvor()

        bvresulteq = s.apply_fun(Equals, bvresult, bv1andbv2)
        bvresult2eq = s.apply_fun(Equals, bvresult2, bv2orbv3)

        bvnotresulteq = s.apply_fun(Equals, bvnotresult, notbv3)

        assert bvnotresulteq.sort == sorts.Bool()

        fifteen = s.theory_const(bvsort, 15)
        twoforty = s.theory_const(bvsort, 240)
        eightyfive = s.theory_const(bvsort, 85)

        bv1eq = s.apply_fun(Equals, bv1, fifteen)
        bv2eq = s.apply_fun(Equals, bv2, twoforty)
        bv3eq = s.apply_fun(Equals, bv3, eightyfive)

        # Assert formulas
        s.Assert(bvresulteq)
        s.Assert(bvresult2eq)
        s.Assert(bvnotresulteq)
        s.Assert(bv1eq)
        s.Assert(bv2eq)
        s.Assert(bv3eq)

        # check satisfiability
        s.check_sat()

        # now query for the values
        bvr1 = s.get_value(bvresult)
        bvr2 = s.get_value(bvresult2)
        bvnr = s.get_value(bvnotresult)

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
    
    bvadd = functions.bvadd()
    bvmul = functions.bvmul()
    bvlshr = functions.bvlshr()

    bvsort = sorts.BitVec(4)

    for name, solver in bv_solvers.items():
        s = solver()
        s.set_logic('QF_BV')
        s.set_option('produce-models', 'true')
        
        bv1 = s.declare_const('bv1', bvsort)
        bv2 = s.declare_const('bv2', bvsort)
        bv3 = s.declare_const('bv3', bvsort)

        one = s.theory_const(bvsort, 1)
        two = s.theory_const(bvsort, 2)
        five = s.theory_const(bvsort, 5)

        bv1eq = s.apply_fun(Equals, bv1, one)
        bv2eq = s.apply_fun(Equals, bv2, two)
        bv3eq = s.apply_fun(Equals, bv3, five)

        bvsum = s.declare_const('bvsum', bvsort)
        bvprod = s.declare_const('bvprod', bvsort)
        bvshifted = s.declare_const('bvshifted', bvsort)

        bvsumval = s.apply_fun(bvadd, bv1, bv2)
        bvprodval = s.apply_fun(bvmul, bv2, bv3)
        bvshiftedval = s.apply_fun(bvlshr, bv3, one)

        bvsumeq = s.apply_fun(Equals, bvsum, bvsumval)
        bvprodeq = s.apply_fun(Equals, bvprod, bvprodval)
        bvshiftedeq = s.apply_fun(Equals, bvshifted, bvshiftedval)

        #make assertions
        s.Assert(bv1eq)
        s.Assert(bv2eq)
        s.Assert(bv3eq)
        s.Assert(bvsumeq)
        s.Assert(bvprodeq)
        s.Assert(bvshiftedeq)

        # check satisfiability
        s.check_sat()

        bvsumr = s.get_value(bvsum)
        bvprodr = s.get_value(bvprod)
        bvshiftedr = s.get_value(bvshifted)

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

import pytest
import config
# set the strict variable before importing other modules
config.strict = True

import sorts
import functions
import solvers


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

    # create bitvector type of width 32
    bvsort = sorts.construct_sort(sorts.BitVec, 32)

    for name, solver in solvers.solvers.items():
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
    bvand = functions.bvand()
    bvor = functions.bvor()
    bvnot = functions.bvnot()

    bvsort = sorts.BitVec(8)

    for name, solver in solvers.solvers.items():
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
        # note: still haven't figure out how to print smt-lib looking results with z3
        assert bvr1 == '(_ bv0 8)' or bvr1 == '#x00'
        assert bvr2 == '(_ bv245 8)' or bvr2 == '#xf5'
        assert bvnr == '(_ bv170 8)' or bvnr == '#xaa'

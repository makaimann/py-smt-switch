import pytest
import config
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

    config.strict = False

    # create bitvector type of width 32
    bvsort = sorts.construct_sort(sorts.BitVec, 32)

    for name, solver in solvers.solvers.items():
        s = solver()
        s.set_logic('QF_BV')

        x = s.declare_const('x', bvsort)

        ext_31_1 = functions.declare_fun(functions.extract, 31, 1)
        x_31_1 = ext_31_1(x)

        ext_30_0 = functions.declare_fun(functions.extract, 30, 0)
        x_30_0 = ext_30_0(x)

        x_31_31 = functions.extract(31, 31)(x)

        x_0_0 = functions.extract(0, 0)(x)

        assert x_31_1.sort == x_30_0.sort
        assert x_31_31.sort == x_0_0.sort

        assert x_31_31.op == functions.extract(31, 31)

        print('Asserting', x_31_1 == x_30_0)
        s.Assert(x_31_1 == x_30_0)

        eq2 = x_31_31 == x_0_0
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
    config.strict = False
    
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

        bvresult = bvand(bv1, bv2)
        bvresult2 = bvor(bv2, bv3)
        bvnotresult = bvnot(bv3)

        assert bvresult2.sort == sorts.BitVec(8)
        assert bvresult2.op == functions.bvor()
    
        # Assert formulas
        s.Assert(bv1 == 15)
        s.Assert(bv2 == 240)
        s.Assert(bv3 == 85)
        
        # check satisfiability
        s.check_sat()

        # now query for the values
        bvr1 = s.get_value(bvresult)
        bvr2 = s.get_value(bvresult2)
        bvnr = s.get_value(bvnotresult)

        # make assertions about values
        # haven't figured out how to print smt-lib format from z3 results yet...
        assert bvr1 == '0' or bvr1 == '0bin00000000'
        assert bvr2 == '245' or bvr2 == '0bin11110101'
        assert bvnr == '170' or bvnr == '0bin10101010'


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
    
    bvadd = functions.bvadd()
    bvmul = functions.bvmul()
    bvlshr = functions.bvlshr()

    bvsort = sorts.BitVec(4)

    for name, solver in solvers.solvers.items():
        s = solver()
        s.set_logic('QF_BV')
        s.set_option('produce-models', 'true')
        
        bv1 = s.declare_const('bv1', bvsort)
        bv2 = s.declare_const('bv2', bvsort)
        bv3 = s.declare_const('bv3', bvsort)

        one = s.theory_const(bvsort, 1)
        two = s.theory_const(bvsort, 2)
        five = s.theory_const(bvsort, 5)

        bvsum = bvadd(bv1, bv2)
        bvprod = bvmul(bv2, bv3)
        bvshifted = bvlshr(bv3, 1)

        #make assertions
        s.Assert(bv1 == 1)
        s.Assert(bv2 == 2)
        s.Assert(bv3 == 5)

        # check satisfiability
        s.check_sat()

        bvsumr = s.get_value(bvsum)
        bvprodr = s.get_value(bvprod)
        bvshiftedr = s.get_value(bvshifted)

        assert bvsumr == '3' or bvsumr == '0bin0011'
        assert bvprodr == '10' or bvprodr == '0bin1010'
        assert bvshiftedr == '2' or bvshiftedr == '0bin0010'

if __name__ == "__main__":
    test_bv_extract()
    test_bv_boolops()
    test_bv_arithops()

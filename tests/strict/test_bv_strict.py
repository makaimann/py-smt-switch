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


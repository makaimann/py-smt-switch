#!/usr/bin/env python3

# This file is part of the smt-switch project.
# See the file LICENSE in the top-level source directory for licensing information.

import sys
from smt_switch import smt

# Below are some examples and general comments to help you get started 

# To translate commands/functions from smt-lib, capitalize the first letter of
# each word and remove all dashes
# examples:
#      declare-const --> DeclareConst
#      check-sat     --> CheckSat
#
# I know this is an ugly convention...but it's the intersection of name
# consistency and avoiding syntax highlighting on keywords, e.g. not/assert/and


# Current Smt-Switch Limitations:
# As of now, there are many unsupported features and theories
#  - The only sorts thus far are BitVec, Bool, Int and Real
#  - The only options supported by all solvers are produce-models and produce-assertions
#  - There is no declare-fun equivalent, however you can write a Python function
#      to get the same behavior
#  - There is no support for incremental solving, yet
#
# Children of terms are currently kept track of at the API level
# --> in a future version, they will be queried from the SMT solver
# --> This can be important to keep up with solver level simplifications
#
# In short, this is a fairly barebones implementation, but the framework is built
# and it is designed to be easily extensible. If you are interested, see
# for_developers.md for a (brief) tutorial on adding solvers/functions/sorts/commands


#################################### EXAMPLES #################################


###############################################################################
#                   Modeling sequential code with bitvectors
#
#                   Example taken from SMT-LIB examples
#                   http://smtlib.cs.uiowa.edu/examples.shtml
#
#         We will produce the smt-switch encoding of the following smt2 example:
#
#         ; Modeling sequential code with bitvectors
#         ;; Correct swap with no temp var
#         ; int x, y;
#         ; x = x + y;
#         ; y = x - y;
#         ; x = x - y;
#
#         (set-logic QF_BV)
#         (set-option :produce-models true)
#
#         (declare-const x_0 (_ BitVec 32))
#         (declare-const x_1 (_ BitVec 32))
#         (declare-const x_2 (_ BitVec 32))
#         (declare-const y_0 (_ BitVec 32))
#         (declare-const y_1 (_ BitVec 32))
#         (assert (= x_1 (bvadd x_0 y_0)))
#         (assert (= y_1 (bvsub x_1 y_0)))
#         (assert (= x_2 (bvsub x_1 y_1)))
#
#         (assert (not
#           (and (= x_2 y_0)
#                (= y_1 x_0))))
#         (check-sat)
#         ; unsat
#         (exit)
###############################################################################


def strict_seq(solvers):

    print('Demonstrating the sequential code benchmark with strict setting')
    print('Expecting unsat')

    for n in solvers:
        # initialize an smt object with the name of the solver
        # This is the api that you interact with
        s = smt(n, strict=True)

        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bvsort32 = s.ConstructSort(s.BitVec, 32)

        x_0 = s.DeclareConst('x_0', bvsort32)
        x_1 = s.DeclareConst('x_1', bvsort32)
        x_2 = s.DeclareConst('x_2', bvsort32)
        y_0 = s.DeclareConst('y_0', bvsort32)
        y_1 = s.DeclareConst('y_1', bvsort32)

        s.Assert(s.ApplyFun(s.Equals, x_1,
                            s.ApplyFun(s.BVAdd,
                                       x_0,
                                       y_0)))

        s.Assert(s.ApplyFun(s.Equals, y_1,
                            s.ApplyFun(s.BVSub,
                                       x_1,
                                       y_0)))

        s.Assert(s.ApplyFun(s.Equals, x_2,
                            s.ApplyFun(s.BVSub,
                                       x_1,
                                       y_1)))

        x2eqy0 = s.ApplyFun(s.Equals, x_2, y_0)
        y1eqx0 = s.ApplyFun(s.Equals, y_1, x_0)

        assert y1eqx0.sort == s.Bool() or \
          n == 'Boolector' and y1eqx0.sort == s.BitVec(1)  # boolector does not distinguish between bool and BV(1)

        s.Assert(s.ApplyFun(s.Not,
                            s.ApplyFun(s.And,
                                       x2eqy0,
                                       y1eqx0)))

        if s.CheckSat():
            print('Strict sequential encoding with {} found sat'.format(n))
        else:
            print('Strict sequential encoding with {} found unsat'.format(n))

        assert not s.Sat, 'Expected unsat'

    print()


def relaxed_seq(solvers):

    print('Demonstrating the sequential code benchmark with relaxed setting')
    print('Expecting unsat')

    for n in solvers:
        s = smt(n)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        x_0 = s.DeclareConst('x_0', s.BitVec(32))
        x_1 = s.DeclareConst('x_1', s.BitVec(32))
        x_2 = s.DeclareConst('x_2', s.BitVec(32))
        y_0 = s.DeclareConst('y_0', s.BitVec(32))
        y_1 = s.DeclareConst('y_1', s.BitVec(32))

        s.Assert(x_1 == x_0 + y_0)
        s.Assert(y_1 == x_1 - y_0)
        s.Assert(x_2 == x_1 - y_1)

        s.Assert(s.Not(
            s.And(x_2 == y_0,
                  y_1 == x_0)))

        if s.CheckSat():
            print('Relaxed sequential encoding with {} found sat'.format(n))
        else:
            print('Relaxed sequential encoding with {} found unsat'.format(n))

        assert not s.Sat, 'Expected unsat'

    print()


###############################################################################
#                    Arbitrary Example
#
#             Showing off some other bitvector operations
###############################################################################

def strict_example(solvers):

    print('Demonstrating a more complex example in strict mode\n')

    for n in solvers:
        print('Solving with {}'.format(n))
        s = smt(n, strict=True)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bv_list = []

        # declare a BitVec sort of width 8
        bvsort8 = s.ConstructSort(s.BitVec, 8)

        # declare a BitVec sort of width 4
        bvsort4 = s.ConstructSort(s.BitVec, 4)

        # declare an extract function
        ext3_0 = s.ConstructFun(s.Extract, 3, 0)
        ext7_4 = s.ConstructFun(s.Extract, 7, 4)

        for i in range(10):
            bv_list.append(s.DeclareConst('bv{}'.format(i), bvsort8))

        for b1, b2 in zip(bv_list[:4], bv_list[1:]):
            b1_7_4 = s.ApplyFun(ext7_4, b1)
            b2_3_0 = s.ApplyFun(ext3_0, b2)
            b17_4eqb23_0 = s.ApplyFun(s.Equals, b1_7_4, b2_3_0)
            s.Assert(b17_4eqb23_0)

        for b1, b2 in zip(bv_list[4:], bv_list[5:]):
            b1_3_0 = s.ApplyFun(ext3_0, b1)

            # you can query the sort of terms
            assert b1_3_0.sort == s.BitVec(4)

            b1_3_0lshift1 = s.ApplyFun(s.BVShl, b1_3_0,
                                       s.TheoryConst(bvsort4, 1))

            b2_7_4 = s.ApplyFun(ext7_4, b2)

            s.Assert(s.ApplyFun(s.Equals,
                                b1_3_0lshift1,
                                b2_7_4))

        bv9plus1 = s.ApplyFun(s.BVAdd, bv_list[9], s.TheoryConst(bvsort8, 1))
        s.Assert(s.ApplyFun(s.Equals,
                            bv9plus1,
                            s.TheoryConst(bvsort8, 1)))

        bv8minusbv5 = s.ApplyFun(s.BVSub, bv_list[8], bv_list[5])
        bv8minusbv5ashr = s.ApplyFun(s.BVAshr, bv8minusbv5,
                                     s.TheoryConst(bvsort8, 2))

        s.Assert(s.ApplyFun(s.Equals, bv8minusbv5ashr, s.TheoryConst(bvsort8, 4)))

        bv3andbv2 = s.ApplyFun(s.BVAnd, bv_list[3], bv_list[2])
        s.Assert(s.ApplyFun(s.BVUge, bv3andbv2, s.TheoryConst(bvsort8, 7)))

        bv7orbv8 = s.ApplyFun(s.BVOr, bv_list[7], bv_list[8])
        s.Assert(s.ApplyFun(s.BVUgt, bv7orbv8, s.TheoryConst(bvsort8, 8)))

        if s.CheckSat():
            for i in range(10):
                # get value returns a term with the value assigned
                val = s.GetValue(bv_list[i])
                print('bv{}: 0b{}'
                      .format(i, val.as_bitstr()),
                      val.as_int())

        print('Show that extract constraints are satisfied')
        for b1, b2 in zip(bv_list[:4], bv_list[1:]):
            val1 = s.GetValue(s.Extract(7, 4, b1))
            val2 = s.GetValue(ext3_0(b2))
            if n != 'Boolector':
                print(val1.op, b1, '= 0b{}'.format(val1.as_bitstr()) + ',',
                      val2.op, b2, '= 0b{}'.format(val2.as_bitstr()))
            else:
                print(b1, '= 0b{}'.format(val1.as_bitstr()) + ',',
                      b2, '= 0b{}'.format(val2.as_bitstr()))

        print()


def relaxed_example(solvers):

    print('Demonstrating a more complex example in relaxed mode\n')

    for n in solvers:
        print('Solving with {}'.format(n))
        s = smt(n)
        s.SetLogic('QF_BV')
        s.SetOption('produce-models', 'true')

        bv_list = []
        ext3_0 = s.Extract(3, 0)

        for i in range(10):
            bv_list.append(s.DeclareConst('bv{}'.format(i), s.BitVec(8)))

        for b1, b2 in zip(bv_list[:4], bv_list[1:]):
            # show slicing for bit vector extracts and callable functions
            s.Assert(b1[7:4] == ext3_0(b2))

        for b1, b2 in zip(bv_list[4:], bv_list[5:]):
            # show calling Extract directly
            b1_3_0 = s.Extract(3, 0, b1)
            assert b1_3_0.sort == s.BitVec(4)

            s.Assert((b1_3_0 << 1) == s.Extract(7, 4, b2))

        # demonstrate building up a list of constraints
        c = []

        # Many common operators are overloaded
        c.append(bv_list[9] + 1 == 5)
        c.append((bv_list[8] - bv_list[5]) >> 2 == 4)

        # BV comparison operators are not yet overloaded
        # I was worried about it being unclear whether it is signed or unsigned
        # comparison
        c.append(s.BVUge(bv_list[3] & bv_list[2], 7))

        c.append(s.BVUgt(bv_list[7] | bv_list[8], 8))

        # can call Assert on a list of constraints
        # This is the same as looping through the list
        # and calling Assert on each element
        s.Assert(c)

        if s.CheckSat():
            for i in range(10):
                val = s.GetValue(bv_list[i])
                print('bv{}: 0b{}'
                      .format(i, val.as_bitstr()),
                      val.as_int())

        print('Show that extract constraints are satisfied')
        for b1, b2 in zip(bv_list[:4], bv_list[1:]):
            val1 = s.GetValue(b1[7:4])
            val2 = s.GetValue(ext3_0(b2))
            if n != 'Boolector':
                print(val1.op, b1, '= 0b{}'.format(val1.as_bitstr()) + ',',
                      val2.op, b2, '= 0b{}'.format(val2.as_bitstr()))
            else:
                print(b1, '= 0b{}'.format(val1.as_bitstr()) + ',',
                      b2, '= 0b{}'.format(val2.as_bitstr()))

        print()


if __name__ == '__main__':

    # you can pass solver names as command line arguments
    # to only use those solvers
    # However, they must be the same as one of the strings
    # in all_solvers
    all_solvers = ['CVC4', 'Boolector', 'Z3']
    solvers = []

    if len(sys.argv) > 1:
        for arg in sys.argv[1:]:
            if arg in all_solvers:
                solvers.append(arg)
            else:
                print('Ignoring {}, it is not the name of a supported solver\n'.format(arg))
    else:
        solvers = all_solvers

    print('Demonstrating the strict setting\n')
    strict_seq(solvers)
    strict_example(solvers)

    print('Demonstrating the relaxed setting\n')
    relaxed_seq(solvers)
    relaxed_example(solvers)

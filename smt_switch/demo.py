#!/usr/bin/env python3
from smt_switch import smt, config

# To translate commands/functions from smt-lib, capitalize the first letter of
# each word and remove all dashes
# examples:
#      declare-const --> DeclareConst
#      check-sat     --> CheckSat
#
# I know this is an ugly convention...but it's the intersection of name
# consistency and avoiding syntax highlighting on keywords, e.g. not/assert/and


def strict_example(solvers):
    config.strict = True

    for n in solvers:
        print('Solving with {}'.format(n))
        # initialize an smt object with the name of the solver
        # This is the api that you interact with
        s = smt(n)
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
            print(val1.op, b1, val1.as_bitstr() + ',', val2.op, b2, val2.as_bitstr())

        print()


def relaxed_example(solvers):
    config.strict = False

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
        # This is the same as s.Assert(s.And(c))
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
            print(val1.op, b1, val1.as_bitstr() + ',', val2.op, b2, val2.as_bitstr())

        print()


if __name__ == '__main__':
    # remove any solvers that you do not have installed
    # from the list
    solvers = ['CVC4', 'Boolector', 'Z3']
    print('Demonstrating the strict setting\n')
    strict_example(solvers)
    print('Demonstrating the relaxed setting\n')
    relaxed_example(solvers)

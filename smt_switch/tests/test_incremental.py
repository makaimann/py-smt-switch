#!/usr/bin/env python3

import pytest
from smt_switch import smt
from smt_switch.tests import all_logic_solvers, bv_solvers


def test_incremental():
    '''
    Simple example demonstrating incremental mode
    '''

    for name in bv_solvers:
        s = smt(name)
        s.SetLogic('QF_BV')
        s.SetOption('incremental', 'true')

        b1 = s.DeclareConst("b1", s.BitVec(4))
        b2 = s.DeclareConst("b2", s.BitVec(4))

        s.Assert(s.BVUlt(b1, b2))

        assert s.CheckSat(), 'Expecting satisfiable'

        s.Assert(s.BVUlt(b2, b1))

        assert not s.CheckSat(), 'Expecting unsat'


def test_pushpop():
    '''
    Same simple example but with push and pop
    '''
    
    for name in all_logic_solvers:
        s = smt(name)
        s.SetLogic('QF_BV')
        s.SetOption('incremental', 'true')

        b1 = s.DeclareConst("b1", s.BitVec(4))
        b2 = s.DeclareConst("b2", s.BitVec(4))

        s.Assert(s.BVUlt(b1, b2))
        assert s.CheckSat(), 'Expecting satisfiable'

        s.Push()

        s.Assert(s.BVUlt(b2, b1))
        assert not s.CheckSat(), 'Expecting unsat'

        s.Pop()

        assert s.CheckSat(), 'Expecting sat again'


if __name__ == "__main__":
    print("before test_incremental")
    test_incremental()
    print("before test_pushpop")
    test_pushpop()

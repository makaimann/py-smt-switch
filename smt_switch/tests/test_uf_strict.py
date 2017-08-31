import pytest
from smt_switch import smt
from smt_switch.config import config
from smt_switch.tests import all_solvers


def test_uf():
    '''
        Simple check demonstrating an axiom of uninterpreted function

        (set-option :produce-models true)
        (set-logic QF_UF)

        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
        (declare-fun f (Bool) Bool)

        (assert (= (f a) b))
        (assert (= (f a) c))

        (assert (not (= b c)))

        (check-sat)
    '''

    config.strict = True

    for name in all_solvers:
        s = smt(name)
        s.SetLogic('QF_UF')

        a = s.DeclareFun("a", [], s.Bool())

        # you can also use the shortcut DeclareConst for zero-arity functions
        b = s.DeclareConst("b", s.Bool())
        c = s.DeclareConst("c", s.Bool())

        f = s.DeclareFun("f", [s.Bool()], s.Bool())
        s.Assert(s.ApplyFun(s.Equals,
                            s.ApplyFun(f, a),
                            b))

        s.Assert(s.ApplyFun(s.Equals,
                            s.ApplyFun(f, a),
                            c))

        s.Assert(s.ApplyFun(s.Not,
                            s.ApplyFun(s.Equals,
                                       b, c)))

        assert not s.CheckSat(), "Expecting unsat"

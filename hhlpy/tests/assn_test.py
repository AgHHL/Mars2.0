"""Unit test for parallel assertions."""

import unittest

from hhlpy import assn_parser
from hhlpy.assn_parser import parse_path_inv, parse_assn
from hhlpy import parallel
from hhlpy.parallel import seq_hcsp_to_assn, add_pn_assn, sync_mult, sync_post, sync_post_tr, sync_post_both, verify_ode
from ss2hcsp.hcsp.parser import parse_hp_with_meta, parse_expr_with_meta
from hhlpy.wolframengine_wrapper import found_wolfram
from hhlpy.wolframengine_wrapper import session


class AssnTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if found_wolfram:
            session.start()

    @classmethod
    def tearDownClass(cls):
        if found_wolfram:
            session.terminate()

    def testParsePathInv(self):
        test_case = [
            "id_inv",
            "s == s0",
            "s == s0[x := v]",
        ]

        for s in test_case:
            path_inv = parse_path_inv(s)
            # print(repr(path_inv))

    def testParseAssnBasic(self):
        test_case = [
            ("init",
             "InitAssertion()"),

            ("init[x := a]",
             "VarSubstAssertion(InitAssertion(), x, VarExpr(a))"),

            ("init[y := y + x][x := a]",
             "VarSubstAssertion(VarSubstAssertion(InitAssertion(), y, OpExpr(+, (VarExpr(y), VarExpr(x)))), x, VarExpr(a))"),

            ("letrec R1, R2 where R1 = R2[x := a], R2 = R1[y := b] in R1 end",
             "LetRecAssertion(('R1', 'R2'), (('R1', VarSubstAssertion(RecursionVar(R2), x, VarExpr(a))), ('R2', VarSubstAssertion(RecursionVar(R1), y, VarExpr(b)))), RecursionVar(R1))"),
        ]

        for s, repr_s in test_case:
            assn = parse_assn(s)
            self.assertEqual(repr(assn), repr_s)

    def testParseParamAssn2(self):
        test_case = [
            ("{(d, v) => b(v == 0) && init}",
             "ParamAssertion(('d', 'v'), PureAssertion(OpExpr(==, (BoundVar(v), ConstExpr(0))), InitAssertion()))"),
        ]

        for s, repr_s in test_case:
            param_assn = assn_parser.parse_param_assn2(s)
            self.assertEqual(repr(param_assn), repr_s)

    def testParseAssn(self):
        test_case = [
            "init",

            # Example 1
            "wait_in(id_inv, ch1, {(d, v) =>"
            "  wait_outv(s == s0[x := v], ch2, v + 1, {d2 => init[x := v]})})",

            # Example 2
            "rec Q. init || wait_in(id_inv, ch1, {(d, v) => Q[y := y + x][x := v]})",

            # Example 3
            "wait_in0(id_inv, ch2, {v =>"
            "  wait(s == s0[x := v], 1, {d1 =>"
            "    wait_outv(s == s0[x := v], ch1, v, {d2 => init[x := v]})})})",

            # Example 4
            "wait_outv(s == s0[x := 0], ch1, 1, {d1 =>"
            "  wait_in(s == s0[x := 2 * t], ch2, {(d2, v) =>"
            "    init[y := v][x := x + 2 * d2][x := 0]"
            "})}) ||"
            "wait_outv(s == s0[x := 0], ch1, 2, {d1 =>"
            "  wait_in(s == s0[x := t], ch2, {(d2, v) =>"
            "    init[y := v][x := x + d2][x := 0]"
            "})})",

            # Example 5
            "rec Q. init ||"
            "wait_outv(s == s0[x := 0], ch1, 1, {d1 =>"
            "  wait_in(s == s0[x := 2 * t], ch2, {(d2, v) =>"
            "    Q[y := v][x := x + 2 * d2][x := 0]"
            "})}) ||"
            "wait_outv(s == s0[x := 0], ch1, 2, {d1 =>"
            "  wait_in(s == s0[x := t], ch2, {(d2, v) =>"
            "    Q[y := v][x := x + d2][x := 0]"
            "})})"
        ]

        for s in test_case:
            assn = parse_assn(s)
            # print(repr(assn))

    def testVarSubst(self):
        test_case = [
            ("init[x := x + 1][x := 2 * x]",
             "init[x := 2 * x + 1]"),

            ("init[x := 2 * x][x := x + 1]",
             "init[x := 2 * (x + 1)]"),

            ("init[x := 1][y := 2]",
             "init[x := 1, y := 2]"),

            ("init[y := y + x][x := v]",
             "init[y := y + v, x := v]"),
        ]

        for s, expected_res in test_case:
            assn = parse_assn(s)
            assert isinstance(assn, parallel.VarSubstAssertion)
            res = assn.start_assn.substVar(assn.var, assn.expr)
            expected_res = parse_assn(expected_res)
            self.assertEqual(res, expected_res)

    def testHcspToAssn(self):
        test_case = [
            # Example 1
            ("ch1?x; ch2!(x+1);",
             "wait_in(id_inv, ch1, {(d2, v1) => wait_outv(id_inv[x := v1], ch2, v1 + 1, {d1 => init[x := v1]})})"),

            # Example 2
            ("{ch1?x; y := y + x;}*",
             "(rec R1. (init || wait_in(id_inv, ch1, {(d1, v1) => R1[y := y + v1, x := v1]})))"),

            # Example 3
            ("ch1!x; {ch1?x; y := y + x;}*",
             "wait_outv(id_inv, ch1, x, {d2 => (rec R1. (init || wait_in(id_inv, ch1, {(d1, v1) => R1[y := y + v1, x := v1]})))})"),

            # Example 4
            ("x := 0; {ch1?x; y := y + x;}*",
             "(rec R1. (init || wait_in(id_inv, ch1, {(d1, v1) => R1[y := y + v1, x := v1]})))[x := 0]"),

            # Example 5
            ("wait(x); {ch1?x; y := y + x;}*",
             "wait(id_inv, x, {d2 => (rec R1. (init || wait_in(id_inv, ch1, {(d1, v1) => R1[y := y + v1, x := v1]})))})"),

            # Example 6
            ("wait(1); ch1?x;",
             "wait(id_inv, 1, {d2 => wait_in(id_inv, ch1, {(d1, v1) => init[x := v1]})})"),

            # Example 7 (2a)
            ("{x := x + 1; ch1!1; ++ ch2!1;}*",
             """
             (rec R1. (init || (wait_outv(id_inv[x := x + 1], ch1, 1, {d1 => R1[x := x + 1]}) ||
                                wait_outv(id_inv[x := x + 1], ch2, 1, {d2 => R1[x := x + 1]}))))
             """),

            # Example 8 (2b)
            ("{ch1?z; y := y + z;}*",
             "(rec R1. (init || wait_in(id_inv, ch1, {(d1, v1) => R1[y := y + v1, z := v1]})))"),

            # Example 9 (2c)
            ("{ch2?w; v := v + w;}*",
             "(rec R1. (init || wait_in(id_inv, ch2, {(d1, v1) => R1[v := v + v1, w := v1]})))"),

            # Example 10 (3b)
            ("{ch?x;}*",
             "(rec R1. (init || wait_in(id_inv, ch, {(d1, v1) => R1[x := v1]})))"),

            # Example 6
            # ("{x_dot = 1 & true} |> [] (ch1!x --> skip;)",
            #  "init"),

            # Example 6
            # ("{x_dot=1, y_dot=2 & x < 6 && y < 8} |> [] (ch1!x --> ch!y;) wait (5);",
            #  "init"),

            # # Example 7
            # "{x_dot=1 , y_dot=x & true} |> [] (ch1!x --> skip;, ch2?x --> skip;)",

            # # Example 8
            # ("{x_dot=1 & x < 6} {x_dot=2 & x < 8}", "init"),

            # Example 9
            # "{x_dot=2 , y_dot=1 & y<8} wait (5);",

            # Example 10
            # "{ch1?x; }*",

            # Example 11
            # "{ch1!(x+1); }*" 

            # "ch1?v;ch2?p;pp:=p+v*T+(1/2)*ad*T^2;vv:=v+da*T;if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (vv<=vl) {a:=da;} else {pp:=p+v*T; if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (v<=vl) {a:=0;} else {a:=-am;}} ch3!a;",

            # Example 12
            # "ch1?v;ch2?p;pp:=p+v*T+(1/2)*ad*T^2;vv:=v+da*T;if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (vv<=vl) {a:=da;} else {pp:=p+v*T; if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (v<=vl) {a:=0;} else {a:=-am;}} ch3!a;",

            # Example 13
            # "{y_dot=1 , x_dot=1 & x<8} invariant unsol {x,y} [y==x];",

            # Example 14
            # "{x_dot=1 , y_dot=x & x < 6} |> [] (ch1!x --> ch!y;) invariant unsol {y} [y>x];",

            # Example 15
            # "{x_dot=1 , y_dot=x & x < 6 +> ch3!x;} |> [] (ch1?x --> ch2?y;) invariant unsol {y} [y>x];",

            # Example 16
            # "{x_dot = x + y, y_dot = x * y - y^2 / 2, t_dot = -1 & t > 0} invariant [y > 0] {dbx} [y*((-104420)+(-73565)*x+18407*y) < 44444] {bc};",

            # "{x_dot = y^2+10*y+25, y_dot = 2*x*y+10*x-40*y-200,t_dot = -1& t > 0 && 5<x && x<35} invariant [5133+8*((-40)+x)*x>=4*y*(10+y)];",

            # "{x_dot = y, y_dot = -x+y*(1-x^2-y^2), t_dot = -1 & t > 0} invariant [x^2+y^2 < 1] {dbx} [346400*(x^2+y^2)>8503] {dbx};",

            # "{x_dot = -y * x, t_dot = -1 & t > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"

            # "(A: x:=1;|{}|B: x:=2;)",

            # "((A: x:=1;|{}|B: x:=2;)|{}|C: x:=2;)",

            # "((A: x:=1;|{}|B: x:=2;)|{ch4,ch5}|(C: x:=1;|{ch2}|D: x:=2;))",

            # "pre [x >= 0]; x := x+1; post [x >= 1];",

            # "pre [x >= 0]; x := x+1; post [x >= 1]; postr [x >= 1];",

            # '''
            # loopinv R1:x>0 end 
            # odeass {x_dot = -y * x, t_dot = -1 & t > 0}
            # pre [Ax >= 0]; 
            # (A: x:=1;|{}|B: x:=2;) 
            # post [Ax >= 1]; 
            # postr [Bx >= 1];''',

        ]
        for s, expected_assn in test_case:
            hp = parse_hp_with_meta(s)
            # hp = parse_hoare_triple_with_meta(s)
            expected_assn = parse_assn(expected_assn)
            # print(expected_assn)
            # print(seq_hcsp_to_assn(hp))
            # print(repr(expected_assn))
            # print(repr(seq_hcsp_to_assn(hp)))
            self.assertEqual(seq_hcsp_to_assn(hp), expected_assn)
            # print(add_pn_assn("A",seq_hcsp_to_assn(hp)))

    def testHcspToAssnODE(self):
        test_case = [
            # Example 10 (3a)
            ("{x_dot = 1 & x < T}",
             "wait(id_inv[x := x + t], T - x, {d1 => init[x := x + d1]})"),

            ("{{x_dot = 1 & x < T} x := 0;}*",
             "(rec R1. (init || wait(id_inv[x := x + t], T - x, {d1 => R1[x := 0][x := x + d1]})))")
        ]

        for s, expected_assn in test_case:
            hp = parse_hp_with_meta(s)
            # hp = parse_hoare_triple_with_meta(s)
            expected_assn = parse_assn(expected_assn)
            # print(expected_assn)
            print(seq_hcsp_to_assn(hp))
            # print(repr(expected_assn))
            # print(repr(seq_hcsp_to_assn(hp)))
            self.assertEqual(seq_hcsp_to_assn(hp), expected_assn)
            # print(add_pn_assn("A",seq_hcsp_to_assn(hp)))

    def testSyncAssnBasic(self):
        """The following tests synchronization on two assertions.

        Each test case has the form: (chs, A1, A2, res), where
        - `chs` is the set of shared channels between P1 and P2.
        - `A1` is the assertion for P1.
        - `A2` is the assertion for P2.
        - `res` is the expected result of synchronization.
        
        """
        test_case = [
            # Case wait_in || init
            # 1. in channel set
            ({"ch1"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "init",
             "false"),

            # Case wait_in || init
            # 2. not in channel set
            ({"ch2"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "init",
             "interrupt(id_inv, 0, {d1 => false}, (ch1? --> {(d, v) => init[P1_x := v]}))"),

            # Case wait_outv || init
            # 1. in channel set
            ({"ch1"},
             "wait_outv(id_inv, ch1, P1_x, {d => init})",
             "init",
             "false"),

            # Case wait_outv || init
            # 2. not in channel set
            ({"ch2"},
             "wait_outv(id_inv, ch1, P1_x, {d => init})",
             "init",
             "interrupt(id_inv, 0, {d1 => false}, (ch1!P1_x --> {d => init}))"),

            # Case wait_in || wait_outv
            # 1. paired
            ({"ch1"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "wait_outv(id_inv, ch1, P2_y, {d => init})",
             "init[P1_x := P2_y]"),

            # 2. left paired, right unpaired
            ({"ch1"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "wait_outv(id_inv, ch2, P2_y, {d1 => wait_outv(id_inv, ch1, P2_z, {d2 => init})})",
             "wait_outv(id_inv, ch2, P2_y, {d1 => init[P1_x := P2_z]})"),

            # 3. left unpaired, right paired
            ({"ch2"},
             "wait_in(id_inv, ch1, {(d, v) => wait_in(id_inv, ch2, {(d1, v1) => init[P1_x := v, P1_y := v1]})})",
             "wait_outv(id_inv, ch2, P2_y, {d2 => init})",
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v, P1_y := P2_y]})"),

            # 4. both unpaired
            ({"ch3"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "wait_outv(id_inv, ch2, P2_y, {d2 => init})",
             """
             interrupt_inf(id_inv, (ch1? --> {(d, v) => interrupt(id_inv, 0, {d1 => false}, (ch2!P2_y --> {d2 => init}))[P1_x := v]},
                                    ch2!P2_y --> {d2 => interrupt(id_inv, 0, {d3 => false}, (ch1? --> {(d, v) => init[P1_x:= v]}))}))
             """),

            # Case wait || wait
            ({},
             "wait(id_inv, P1_x, {d => init})",
             "wait(id_inv, P2_y, {d => init})",
             "b(P1_x == P2_y) && wait(id_inv, P1_x, {d => init})"),

            # Case wait_in || wait
            ({"ch1"},
             "wait_in(id_inv, ch1, {(d, v) => init[P1_x := v]})",
             "wait(id_inv, P2_y, {d1 => wait_outv(id_inv, ch1, P2_z, {d2 => init})})",
             "wait(id_inv, P2_y, {d1 => init[P1_x := P2_z]})"),

            # Case wait || wait_in
            # 1. paired
            ({"ch1"},
             "wait(id_inv, P1_y, {d1 => wait_outv(id_inv, ch1, P1_z, {d2 => init})})",
             "wait_in(id_inv, ch1, {(d, v) => init[P2_x := v]})",
             "wait(id_inv, P1_y, {d1 => init[P2_x := P1_z]})"),

            # 2. unpaired
            ({""},
             "wait(id_inv, P1_y, {d1 => init})",
             "wait_in(id_inv, ch1, {(d, v) => init[P2_x := v]})",
             """
             interrupt(id_inv, P1_y, {d1 => interrupt(id_inv, 0, {d2 => false}, (ch1? --> {(d, v) => init[P2_x := v]}))},
                       (ch1? --> {(d, v) => (b(0 >= P1_y - d) && init)[P2_x := v]}))
             """),

            # Case wait_outv || wait
            ({"ch1"},
             "wait_outv(id_inv, ch1, P1_x, {d => init})",
             "wait(id_inv, P2_y, {d1 => wait_in(id_inv, ch1, {(d2, v) => init[P2_x := v]})})",
             "wait(id_inv, P2_y, {d1 => init[P2_x := P1_x]})"),

            # Case wait || wait_outv
            ({"ch1"},
             "wait(id_inv, P1_y, {d1 => wait_in(id_inv, ch1, {(d2, v) => init[P1_x := v]})})",
             "wait_outv(id_inv, ch1, P2_x, {d => init})",
             "wait(id_inv, P1_y, {d1 => init[P1_x := P2_x]})"),

            # Case wait || init
            ({},
             "wait(id_inv, P1_x, {d => init})",
             "init",
             "b(0 >= P1_x) && init"),

            # Case interrupt_inf || init
            # 1. one unpaired comm
            ({"ch1"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",
             "interrupt(id_inv, 0, {d2 => false}, (ch2? --> {(d1, v1) => init[P1_y := v1]}))"),

            # 2. no unpaired comms
            ({"ch1", "ch2"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",
             "false"),

            # Case interrupt || init
            # 1. one unpaired comm
            ({"ch1"},
             "interrupt(id_inv, P1_x, {d => init}, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",
             "interrupt(id_inv, 0, {d2 => (b(0 >= P1_x) && init)}, (ch2? --> {(d1, v1) => init[P1_y := v1]}))"),

            # 2. no unpaired comms
            ({"ch1", "ch2"},
             "interrupt(id_inv, P1_x, {d => init}, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",
             "b(0 >= P1_x) && init"),

            # 3. one unpaired comm, delay nonzero
            ({"ch1"},
             "interrupt(id_inv, 1, {d => init}, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",
             "interrupt(id_inv, 0, {d2 => false}, (ch2? --> {(d1, v1) => init[P1_y := v1]}))"),

            # 4. no unpaired comms, delay nonzero
            ({"ch1", "ch2"},
             "interrupt(id_inv, 1, {d => init}, (ch1? --> {(d, v) => init[P1_x := v]}, ch2? --> {(d1, v1) => init[P1_y := v1]}))",
             "init",             
             "false"),

            # Case interrupt_inf || interrupt_inf
            # 1. no matched comms, both not in channel set
            ({},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}))",
             "interrupt_inf(id_inv, (ch2!P2_x --> {d1 => init}))",
             """
             interrupt_inf(id_inv, (ch1? --> {(d, v) => interrupt(id_inv, 0, {d2 => false}, (ch2!P2_x --> {d1 => init}))[P1_x := v]},
                                    ch2!P2_x --> {d1 => interrupt(id_inv, 0, {d3 => false}, (ch1? --> {(d, v) => init[P1_x := v]}))}))
             """),

            # 2. no matched comms, some in channel set.
            ({"ch1"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}))",
             "interrupt_inf(id_inv, (ch2!P2_x --> {d1 => wait_outv(id_inv, ch1, P2_y, {d2 => init})}))",
             "wait_outv(id_inv, ch2, P2_x, {d1 => init[P1_x := P2_y]})"),

            # 3. some matched comms
            ({"ch1"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}))",
             "interrupt_inf(id_inv, (ch1!P2_x --> {d1 => init}))",
             "init[P1_x := P2_x]"),

            # 4. some matched comms and some unmatched.
            ({"ch1"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}, ch3? --> {(d, v) => init[P1_y := v]}))",
             "interrupt_inf(id_inv, (ch1!P2_x --> {d1 => init}, ch2!P2_y --> {d2 => init}))",
             """
             interrupt(id_inv, 0, {d5 => init[P1_x := P2_x]},
                       (ch3? --> {(d, v) => interrupt(id_inv, 0, {d3 => false}, (ch2!P2_y --> {d2 => init}))[P1_y := v]},
                        ch2!P2_y --> {d2 => interrupt(id_inv, 0, {d4 => false}, (ch3? --> {(d, v) => init[P1_y := v]}))}))
             """),

            # 5. match in any order.
            ({"ch1", "ch2"},
             "interrupt_inf(id_inv, (ch1? --> {(d, v) => init[P1_x := v]}, ch2!P1_x --> {d => init}))",
             "interrupt_inf(id_inv, (ch1!P2_x --> {d1 => init}, ch2? --> {(d1, v) => init[P2_x := v]}))",
             "init[P1_x := P2_x] || init[P2_x := P1_x]")
        ]

        for chset, A1, A2, expected_res in test_case:
            A1 = parse_assn(A1)
            A2 = parse_assn(A2)
            res = parallel.sync_assn(chset, A1, A2)
            # print(res)
            expected_res = parse_assn(expected_res)
            # print(repr(res))
            # print(repr(expected_res))
            self.assertEqual(res, expected_res, f"actual: {res}")

    def testSyncAssnBasicTriple(self):
        """The following tests synchronization on three assertions.
        
        Each test case has the form:
            (chs12, chs13, chs23, A1, A2, A3, res),
        where
        - `chs12` is the set of shared channels between P1 and P2.
        - `chs13` is the set of shared channels between P1 and P3.
        - `chs23` is the set of shared channels between P2 and P3.
        - `A1` is the assertion for P1.
        - `A2` is the assertion for P2.
        - `A3` is the assertion for P3.
        - `res` is the expected result of synchronization.

        """
        test_case = [
            ({"ch1"},
             {"ch2"},
             {},
             "wait_in(id_inv, ch1, {(d, v) => wait_in(id_inv, ch2, {(d1, v1) => init[P1_x := v, P1_y := v1]})})",
             "wait_outv(id_inv, ch1, P2_x, {d2 => init})",
             "wait_outv(id_inv, ch2, P3_y, {d3 => init})",
             "init[P1_x := P2_x, P1_y := P3_y]"),

            ({"ch1"},
             {"ch2"},
             {},
             "wait_in(id_inv, ch1, {(d, v) => wait_in(id_inv, ch2, {(d1, v1) => init[P1_x := v, P1_y := v1]})})",
             "wait(id_inv, 2, {d4 => wait_outv(id_inv, ch1, P2_x, {d2 => init})})",
             "wait(id_inv, 5, {d5 => wait_outv(id_inv, ch2, P3_y, {d3 => init})})",
             "false"),
        ]

        for chs12, chs13, chs23, A1, A2, A3, expected_res in test_case:
            A1 = parse_assn(A1)
            A2 = parse_assn(A2)
            A3 = parse_assn(A3)
            expected_res = parse_assn(expected_res)

            # A1, A2 first
            res1 = parallel.sync_assn(chs12, A1, A2)
            res = parallel.sync_assn(chs13.union(chs23), res1, A3)
            print(res)
            self.assertEqual(res, expected_res, f"actual: {res}")

            # A1, A3 first
            res1 = parallel.sync_assn(chs13, A1, A3)
            res = parallel.sync_assn(chs12.union(chs23), res1, A2)
            print(res)
            self.assertEqual(res, expected_res, f"actual: {res}")

            # A2, A3 first
            res1 = parallel.sync_assn(chs23, A2, A3)
            res = parallel.sync_assn(chs12.union(chs13), res1, A1)
            print(res)
            self.assertEqual(res, expected_res, f"actual: {res}")

    def testSyncAssnRec(self):
        test_case = [
            ({"ch1"},
             "rec R1. init || wait_in(id_inv, ch1, {(d, v) => R1[P1_x := P1_x + v]})",
             "rec R2. init || wait_outv(id_inv, ch1, P2_y, {d => R2})",
             "(rec R5. (init || R5[P1_x := P1_x + P2_y]))"),

            ({"ch1"},
             """
             (rec R1. (init || (wait_outv(id_inv[x := x + 1], ch1, 1, {d1 => R1[x := x + 1]}) ||
                                wait_outv(id_inv[x := x + 1], ch2, 1, {d2 => R1[x := x + 1]}))))
             """,
             "(rec R2. (init || wait_in(id_inv, ch1, {(d1, v1) => R2[y := y + v1, z := v1]})))",
             "init"),
        ]

        for chset, A1, A2, expected_res in test_case:
            A1 = parse_assn(A1)
            A2 = parse_assn(A2)
            res = parallel.sync_assn(chset, A1, A2)
            print(res)
            expected_res = parse_assn(expected_res)
            self.assertEqual(res, expected_res)

    def testSyncAssnRecTriple(self):
        A1 = parse_assn("""
            (rec R1. (init || (wait_outv(id_inv[x := x + 1], ch1, 1, {d1 => R1[x := x + 1]}) ||
                               wait_outv(id_inv[x := x + 1], ch2, 1, {d2 => R1[x := x + 1]}))))
        """)

        A2 = parse_assn("(rec R2. (init || wait_in(id_inv, ch1, {(d1, v1) => R2[y := y + v1, z := v1]})))")

        A3 = parse_assn("(rec R3. (init || wait_in(id_inv, ch2, {(d1, v1) => R3[v := v + v1, w := v1]})))")

        bound_vars = []
        A1.get_bound_vars(bound_vars)
        A2.get_bound_vars(bound_vars)
        A3.get_bound_vars(bound_vars)

        A4 = parallel.sync_assn({"ch1"}, A1, A2, bound_vars=bound_vars)
        A5 = parallel.sync_assn({"ch2"}, A4, A3, bound_vars=bound_vars)
        print(A5)

    def testSyncAssnRecTriple2(self):
        A1 = parse_assn("(rec R1. (init || wait(id_inv[x := x + t], T - x, {d1 => R1[x := 0][x := x + d1]})))")
        A2 = parse_assn("(rec R2. (init || wait_in(id_inv, ch, {(d2, v1) => R2[x := v1]})))")
        res = parallel.sync_assn({}, A1, A2)

    def testSyncAssn(self):
        test_case = [
            # (({"pn": "A", "P": "ch1?x;ch2!x;"},
            #   {"chset": {"ch1"}, "init": "Bx==1"},
            #   {"pn": "B", "P": "ch1!x;"}),
            #  {"chset": {"ch2"}, "init": "Bx==1"},
            #  {"pn": "C", "P": "ch2?x;"}),

            # ({"pn": "A","P": "ch1?x;"},
            #  {"chset": {"ch1"}},
            #  {"pn": "B", "P": "ch1!3;"}),

            # ({"pn": "A", "P": "ch1?x; ch2?y;"},
            #  {"chset": {"ch1"}},
            #  {"pn": "B", "P": "ch1!3;"}),

            # ({"pn":"A","P":"ch1?x; ch2!y;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            # ({"pn":"A","P":"ch1?x; ch2!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            # ({"pn":"A","P":"ch1!x; ch2?y;"}, {"chset":{"ch1", "ch2"}} , {"pn":"B","P":"ch1?z; ch2!(z+1);"}),
            # ({"pn":"A","P":"y:=0;{ch1!x; y:=y+1;}*"}, {"chset":{"ch1"}}, {"pn":"B","P":"y:=0;{ch1?x; y:=y+x;}*"}),
            # ({"pn":"A","P":"{ch1!x; y:=y+1;}*"}, {"chset":{"ch1"}, "init":"Ay==0&&By==0", "recinv":("AR1","BR1","By==Ay*Ax")}, {"pn":"B","P":"{ch1?x; y:=y+x;}*"}),
            # ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch1?y --> skip;)"}),
            # ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch2?y --> skip;)"}),
            # ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch2?y --> skip;)"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}, "init":"Ax==0"}, {"pn":"B","P":"wait (5); ch1!1;"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{}, "init":"Ax==Bx"}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}, "init":"Ax==Bx"}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{}}, {"pn":"B","P":"ch2?y;"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"ch2?y;"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?y;"}),
            # ({"pn":"A","P":"{x_dot=1 & x<8 +> ch1!x; } |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}, "init": "Ax==0"}, {"pn":"B","P":"wait (8); ch1?y;"}),
            # ({"pn":"A","P":"ch2?y;"}, {"chset":{}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            # ({"pn":"A","P":"ch2?y;"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            # ({"pn":"A","P":"ch1?y;"}, {"chset":{"ch1"}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            # ({"pn":"A","P":"x:=1;"}, {"chset":{"ch1"}}, {"pn":"B","P":"skip;"}),
            # ({"pn":"A","P":"{x_dot=1 , y_dot=2 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (1);ch1?x;"}),
            # ({"pn":"A","P":"wait (5);"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (2); wait (3);"}),
            # ({"pn":"A","P":"ch1?x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (y);ch1!3;"}),
            # ({"pn":"A","P":"ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (y);ch1?x;"}),
            # ({"pn":"A","P":"wait (y);ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?x;"}),
            # (({"pn":"A","P":"ch2?x; wait (1);ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?x;"}), {"chset":{"ch2"}},{"pn":"C","P":"ch2!v;wait (1);"}),
            # ({"pn":"A","P":"x:=7;{x_dot=1 & x<6}"}, {"chset":{"ch1"}}, {"pn":"B","P":"skip;"}),
            # ({"pn":"A","P":"{x_dot=1 & x<6}"}, {"chset":{"ch1"}, "init": "Ax==7"}, {"pn":"B","P":"skip;"}),
            # ({"pn":"A","P":"{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{ch1?y; wait (y); ch2!0;}*"}),
            # ({"pn":"A","P":"{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *"}, {"chset":{"ch1", "ch2"}, "init": "Ax==0", "recinv":("AR1","BR1","Ax>=0&&Ax<=2")}, {"pn":"B","P":"{ch1?y; wait (y); ch2!0;}*"}),
            # (({"pn":"A","P":"{{x_dot=1 & true} |> [] (ch3?x --> ch1!0;,ch2?x --> skip;)}*"},{"chset":{"ch1", "ch2"}},{"pn":"B","P":"{{x_dot=1 & true} |> [] (ch4?x --> ch2!0;,ch1?x --> skip;)}*"}),{"chset":{"ch3", "ch4"}},{"pn":"C","P":"{wait (5);{ch3!0;} ++ {ch4!0;}}*"}),
            # ({"pn":"A","P":"ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*"}, 
            #  {"chset":{"ch1", "ch2", "ch3"}, 
            #   "init": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
            #             ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
            #             (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
            #   "recinv": ("AR1","BR1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
            #              ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
            #              (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
            #              &&Av==Bv&&Ap==Bp""")},
            #  {"pn":"B","P":"""ch1?v;ch2?p;
            #  {pp:=p+v*T+(1/2)*da*T^2;vv:=v+da*T;
            #  if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
            #  else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
            #  else { vlm:=0; } 
            #  if (vv<=0||vv^2<=vlm) {a:=da;} 
            #  else {pp:=p+v*T; 
            #     if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
            #     else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
            #     else { vlm:=0; } 
            #     if (v<=0||v^2<=vlm) {a:=0;} 
            #     else {a:=-am;}} 
            # ch3!a;wait (T); ch1?v;ch2?p;}*"""}),
            (({"pn": "A", "P": "{ x:=x+1; {ch1!1; ++ ch2!1;} }*"},
              {"chset": {"ch1"}},
              {"pn": "B", "P": "{  ch1?w;u:=u+w; }*"}),
             {"chset": {"ch2"}},
             {"pn": "C", "P": "{  ch1?y;x:=x+y; }*"})
        ]
        for s in test_case:
            print(sync_mult(s))

    def testSyncPost(self):    
        C = [
        {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "RI":[("R1","y>0")]},
        {"PA":"d:=0;y:=0;{x_dot=y, y_dot=a*x+b*y, d_dot=1 & d<dd}", "Pre":"x>0&&dd>0&&a<0&&b<=0&&b^2+4*a>0", "Post":"x>=0", "RI":[]},
        {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "RI":[]},
        {"PA":({"pn":"A","P":"{ch1!x; y:=y+1;}*"}, {"chset":{"ch1"}}, {"pn":"B","P":"{ch1?x; y:=y+x;}*"}),
         "Pre":"Ay==1&&By==1&&Ax==1", "Post":"By==Ay*Ax", "RI":[("R1","By==Ay*Ax")]},
        {"PA":({"pn":"A","P":"ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*"}, 
               {"chset":{"ch1", "ch2", "ch3"}},
               {"pn":"B","P":"""ch1?v;ch2?p;
                                {pp:=p+v*T+(1/2)*da*T^2;vv:=v+da*T;
                                if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
                                else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
                                else { vlm:=0; } 
                                if (vv<=0||vv^2<=vlm) {a:=da;} 
                                else {pp:=p+v*T; 
                                    if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
                                    else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
                                    else { vlm:=0; } 
                                if (v<=0||v^2<=vlm) {a:=0;} 
                                else {a:=-am;}} 
                                ch3!a;wait (T); ch1?v;ch2?p;}*"""}), 
         "Pre": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                        ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                        (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
         "Post": """Ap<=Bop""", 
         "RI":[("R1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                         ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                         (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
                         &&Av==Bv&&Ap==Bp""")]},
        ]
        for c in C:
            P = sync_mult(c["PA"])
            print(P)
            print(sync_post(c["Pre"],P,c["Post"],c["RI"]))

    def testSyncPostTr(self):    
        C = [
        {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "RI":[("R1","y>0")]},
        {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "RI":[]},
        {"PA":({"pn":"A","P":"{ {x_dot=y & true} |> [] (ch1?y --> skip;) }*"}, {"chset":{"ch1"}}, {"pn":"B","P":"{wait (5); ch1!1;}*"}),
         "Pre":"Ax>0&&Ay>0", "Post":"Ax>0", "RI":[("R1","Ax>0&&Ay>0")]},
         {"PA":({"pn":"A","P":"ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*"}, 
               {"chset":{"ch1", "ch2", "ch3"}},
               {"pn":"B","P":"""ch1?v;ch2?p;
                                {pp:=p+v*T+(1/2)*da*T^2;vv:=v+da*T;
                                if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
                                else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
                                else { vlm:=0; } 
                                if (vv<=0||vv^2<=vlm) {a:=da;} 
                                else {pp:=p+v*T; 
                                    if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
                                    else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
                                    else { vlm:=0; } 
                                if (v<=0||v^2<=vlm) {a:=0;} 
                                else {a:=-am;}} 
                                ch3!a;wait (T); ch1?v;ch2?p;}*"""}), 
         "Pre": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                        ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                        (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
         "Post": """Ap<=Bop""", 
         "RI":[("R1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                         ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                         (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
                         &&Av==Bv&&Ap==Bp""")]},
                
        ]
        for c in C:
            P = sync_mult(c["PA"])
            print(P)
            print(sync_post_tr(c["Pre"],P,c["Post"],c["RI"]))


    def testSyncPostBoth(self):    
        C = [
        # {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "Postr":"x>0", "RI":[("R1","y>0")], "OI":[]},
        # {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "Postr":"x>0", "RI":[],  "OI":[]},
        # {"PA":({"pn":"A","P":"{ {x_dot=y & true} |> [] (ch1?y --> skip;) }*"}, {"chset":{"ch1"}}, {"pn":"B","P":"{wait (5); ch1!1;}*"}),
        #  "Pre":"Ax>0&&Ay>0", "Post":"Ax>0", "Postr":"Ax>0", "RI":[("R1","Ax>0&&Ay>0")], "OI":[]},
        # {"PA":({"pn":"A","P":"ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*"}, 
        #        {"chset":{"ch1", "ch2", "ch3"}},
        #        {"pn":"B","P":"""ch1?v;ch2?p;
        #                         {pp:=p+v*T+(1/2)*da*T^2;vv:=v+da*T;
        #                         if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
        #                         else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
        #                         else { vlm:=0; } 
        #                         if (vv<=0||vv^2<=vlm) {a:=da;} 
        #                         else {pp:=p+v*T; 
        #                             if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
        #                             else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
        #                             else { vlm:=0; } 
        #                         if (v<=0||v^2<=vlm) {a:=0;} 
        #                         else {a:=-am;}} 
        #                         ch3!a;wait (T); ch1?v;ch2?p;}*"""}), 
        #  "Pre": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
        #                 ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
        #                 (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
        #  "Post": """Ap<=Bop""", "Postr": """Ap<=Bop""",
        #  "RI":[("R1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
        #                  ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
        #                  (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
        #                  &&Av==Bv&&Ap==Bp""")], "OI":[]},
        # {"PA":"{x_dot = -x + x * y , y_dot = -y, T_dot = -1 & T > 1} invariant unsol {x,y} [x>=0 && y>=0];", "Pre":"x==0.5 && y==0.5", "Post":"x+y>=0", "Postr":"x+y>=0", "RI":[], 
        #  "OI":["{x_dot = -x + x * y , y_dot = -y, T_dot = -1 & T > 0} invariant [x >= 0] {dbx}[y >= 0] {dbx};"]},
        # {"PA":"{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];", "Pre":"x==0.5", "Post":"x>0", "Postr":"x>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        # {"PA":"x:=0.5;T:=1;{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];", "Pre":"true", "Post":"x>0", "Postr":"x>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        # {"PA":"{x:=0.5;++x:=0.5;}{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];", "Pre":"true", "Post":"x>0", "Postr":"x>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        # {"PA":"if (y>0) {x:=1;} else {x:=1;}{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];", "Pre":"true", "Post":"x>0", "Postr":"x>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        # {"PA":"if (y>0) {x:=1;} else {x:=2;}{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];", "Pre":"true", "Post":"x>0", "Postr":"x>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        {"PA":({"pn":"A","P":"ch1?x;{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];"}, {"chset":{"ch1"}}, 
               {"pn":"B","P":"ch1!4; wait (2); wait (3);"}),
         "Pre":"AT==5", "Post":"Ax>0", "Postr":"Ax>0", "RI":[], 
         "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
        ]
        for c in C:
            P = sync_mult(c["PA"])
            # print(P)
            print(sync_post_both(c["Pre"],P,c["Post"],c["Postr"],c["RI"], c["OI"]))


    def testexpr(self):
        test_case = [
            # "x<=y||x==1",
            "x==2->x>0",
            # "Ax>0||Bx<=0",
            # "d1==6-2*x&&d1<5-2*x",
            # "exists x1 . (x==x1+1 && x1>0)",
            "(if x>0 then x else -x)>=0",
            # "(if (Bop-Ap>=(Bvm^2)/(2*Bam)) then (Av<=Bvm) else (Av<=(2*Bam*(Bop-Ap))^1/2))",
            # "if (Av+Bda*BT<=(if (Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)>=(Bvm^2)/(2*Bam)) then (Bvm) else (if (Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)>0) then ((2*Bam*(Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)))^1/2) else (0)))) then (Aa==Bda) else (if (Av<=(if (Bop-(Ap+Av*BT)>=(Bvm^2)/(2*Bam)) then (Bvm) else (if (Bop-(Ap+Av*BT)>0) then ((2*Bam*(Bop-(Ap+Av*BT)))^1/2) else (0)))) then (Aa==0) else (Aa==-Bam))",
            # "BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&(if (Bop-Ap>=(Bvm^2)/(2*Bam)) then (Av<=Bvm) else (if (Bop-Ap>0) then (Av<=(2*Bam*(Bop-Ap))^1/2) else (Av<=0)))"
        ]
        for s in test_case:
            print(parse_expr_with_meta(s))
            # print(wl_reduce(parse_expr_with_meta(s),[]))
            # print(wl_prove(parse_expr_with_meta(s),[]))
            # print(wl_reduce_false(parse_expr_with_meta(s)))


if __name__ == "__main__":
    unittest.main()

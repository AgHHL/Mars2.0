"""Unit test for parallel assertions."""

import unittest

from hhlpar.assn_parser import parse_expr, parse_path_inv, parse_assn
from hhlpar.parallel import seq_hcsp_to_assn, add_pn_assn, sync_mult, sync_post, sync_post_tr, sync_post_both, verify_ode
from ss2hcsp.hcsp.parser import parse_hp_with_meta, parse_expr_with_meta, parse_php_with_meta, parse_hoare_triple_with_meta
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.language.expression import WLFunction, WLSymbol
from wolframclient.exception import WolframKernelException
from hhlpar.wolframengine_wrapper import solveODE, wl_prove, wl_reduce, wl_reduce_true, wl_reduce_false
from hhlpar.wolframengine_wrapper import wl_simplify, wl_polynomial_div, wl_is_polynomial, found_wolfram
from hhlpar.wolframengine_wrapper import session


class AssnTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testParsePathInv(self):
        test_case = [
            "id_inv",
            "s == s0",
            "s == s0[x := v]",
        ]

        for s in test_case:
            path_inv = parse_path_inv(s)
            print(path_inv)

    def testParseAssn(self):
        test_case = [
            "init",

            # Example 1
            "wait_in(id_inv, ch1, {(d, v) =>"
            "  wait_outv(s == s0[x := v], ch2, v + 1, {d2 => init[x := v]})})",

            # Example 2
            # { P } *  ==  rec Q. skip || P; Q
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
            print(assn)

    def testSeqHcspToAssn(self):
        test_case = [
            # # Example 1
            # "ch1?x; ch2!(x+1);",

            # # Example 2
            # "{ ch1?x; y := y + x; }*",

            # # Example 3
            # "ch1!x; { ch1?x; y := y + x; }* ch1?x;",

            # # Example 4
            # "{ x := 0; { ch1?x; y := y + x; }* }*",

            # # Example 5
            # "wait (x); { ch1?x; y := y + x; }*",

            # # Example 6
            # "{x_dot=1 , y_dot=2 & x < 6 && y < 8} |> [] (ch1!x --> ch!y;) wait (5);",

            # # Example 7
            # "{x_dot=1 , y_dot=x & true} |> [] (ch1!x --> skip;, ch2?x --> skip;)",

            # Example 8
            # "{x_dot=1 , y_dot=2 & x < 6 && y < 8}",

            # Example 9
            # "{x_dot=y , y_dot=1 & x<8} wait (5);",

            # Example 10
            # "{ch1?x; }*",

            # Example 11
            # "{ch1!(x+1); }*" 

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

            '''
            loopinv R1:x>0 end 
            odeass {x_dot = -y * x, t_dot = -1 & t > 0}
            pre [Ax >= 0]; 
            (A: x:=1;|{}|B: x:=2;) 
            post [Ax >= 1]; 
            postr [Bx >= 1];''',

        ]
        for s in test_case:
            # hp = parse_php_with_meta(s)
            hp = parse_hoare_triple_with_meta(s)
            # print(hp)
            # print(seq_hcsp_to_assn(hp))
            # verify_ode(hp)
            # print(add_pn_assn("A",seq_hcsp_to_assn(hp)))
            # print(hp.pre, hp.hp, hp.post)
            P = sync_mult(hp.hp)
            print(P)
            print(sync_post_both(hp.pre,P,hp.post,hp.postr,[],[]))


    def testSyncAssn(self):
        test_case = [
            (({"pn":"A","P":"ch1?x;ch2!x;"}, {"chset":{"ch1"},"init":"Bx==1"}, {"pn":"B","P":"ch1!x;"}), {"chset":{"ch2"},"init":"Bx==1"}, {"pn":"C","P":"ch2?x;"}),
            ({"pn":"A","P":"ch1?x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            ({"pn":"A","P":"ch1?x; ch2?y;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            ({"pn":"A","P":"ch1?x; ch2!y;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            ({"pn":"A","P":"ch1?x; ch2!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1!3;"}),
            ({"pn":"A","P":"ch1!x; ch2?y;"}, {"chset":{"ch1", "ch2"}} , {"pn":"B","P":"ch1?z; ch2!(z+1);"}),
            ({"pn":"A","P":"y:=0;{ch1!x; y:=y+1;}*"}, {"chset":{"ch1"}}, {"pn":"B","P":"y:=0;{ch1?x; y:=y+x;}*"}),
            ({"pn":"A","P":"{ch1!x; y:=y+1;}*"}, {"chset":{"ch1"}, "init":"Ay==0&&By==0", "recinv":("AR1","BR1","By==Ay*Ax")}, {"pn":"B","P":"{ch1?x; y:=y+x;}*"}),
            ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch1?y --> skip;)"}),
            ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch2?y --> skip;)"}),
            ({"pn":"A","P":"{x_dot=1 & true} |> [] (ch1!x --> skip;)"}, {"chset":{}}, {"pn":"B","P":"{x_dot=1 & true} |> [] (ch2?y --> skip;)"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}, "init":"Ax==0"}, {"pn":"B","P":"wait (5); ch1!1;"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{}, "init":"Ax==Bx"}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}, "init":"Ax==Bx"}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{}}, {"pn":"B","P":"ch2?y;"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"ch2?y;"}),
            ({"pn":"A","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?y;"}),
            ({"pn":"A","P":"{x_dot=1 & x<8 +> ch1!x; } |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}, "init": "Ax==0"}, {"pn":"B","P":"wait (8); ch1?y;"}),
            ({"pn":"A","P":"ch2?y;"}, {"chset":{}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            ({"pn":"A","P":"ch2?y;"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            ({"pn":"A","P":"ch1?y;"}, {"chset":{"ch1"}}, {"pn":"B","P":"{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"}),
            ({"pn":"A","P":"x:=1;"}, {"chset":{"ch1"}}, {"pn":"B","P":"skip;"}),
            ({"pn":"A","P":"{x_dot=1 , y_dot=2 & true} |> [] (ch1!x --> skip;)"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (1);ch1?x;"}),
            ({"pn":"A","P":"wait (5);"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (2); wait (3);"}),
            ({"pn":"A","P":"ch1?x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (y);ch1!3;"}),
            ({"pn":"A","P":"ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"wait (y);ch1?x;"}),
            ({"pn":"A","P":"wait (y);ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?x;"}),
            (({"pn":"A","P":"ch2?x; wait (1);ch1!x;"}, {"chset":{"ch1"}}, {"pn":"B","P":"ch1?x;"}), {"chset":{"ch2"}},{"pn":"C","P":"ch2!v;wait (1);"}),
            ({"pn":"A","P":"x:=7;{x_dot=1 & x<6}"}, {"chset":{"ch1"}}, {"pn":"B","P":"skip;"}),
            ({"pn":"A","P":"{x_dot=1 & x<6}"}, {"chset":{"ch1"}, "init": "Ax==7"}, {"pn":"B","P":"skip;"}),
            ({"pn":"A","P":"{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *"}, {"chset":{"ch1", "ch2"}}, {"pn":"B","P":"{ch1?y; wait (y); ch2!0;}*"}),
            ({"pn":"A","P":"{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *"}, {"chset":{"ch1", "ch2"}, "init": "Ax==0", "recinv":("AR1","BR1","Ax>=0&&Ax<=2")}, {"pn":"B","P":"{ch1?y; wait (y); ch2!0;}*"}),
            (({"pn":"A","P":"{{x_dot=1 & true} |> [] (ch3?x --> ch1!0;,ch2?x --> skip;)}*"},{"chset":{"ch1", "ch2"}},{"pn":"B","P":"{{x_dot=1 & true} |> [] (ch4?x --> ch2!0;,ch1?x --> skip;)}*"}),{"chset":{"ch3", "ch4"}},{"pn":"C","P":"{wait (5);{ch3!0;} ++ {ch4!0;}}*"}),
            ({"pn":"A","P":"ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*"}, 
             {"chset":{"ch1", "ch2", "ch3"}, 
              "init": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                        ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                        (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
              "recinv": ("AR1","BR1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                         ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                         (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
                         &&Av==Bv&&Ap==Bp""")},
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
            ch3!a;wait (T); ch1?v;ch2?p;}*"""})
        ]
        for s in test_case:
            print(sync_mult(s))

    def testSyncPost(self):    
        C = [
        # {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "RI":[("R1","y>0")]},
        # {"PA":"d:=0;y:=0;{x_dot=y, y_dot=a*x+b*y, d_dot=1 & d<dd}", "Pre":"x>0&&dd>0&&a<0&&b<=0&&b^2+4*a>0", "Post":"x>=0", "RI":[]},
        # {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "RI":[]},
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
        # {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "RI":[("R1","y>0")]},
        # {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "RI":[]},
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
        {"PA":"{ y:=y+1;}*x:=y;", "Pre":"y>0", "Post":"x>0", "Postr":"x>0", "RI":[("R1","y>0")], "OI":[]},
        {"PA":"{x_dot=x, d_dot=1 & d<dd}", "Pre":"x>0", "Post":"x>0", "Postr":"x>0", "RI":[],  "OI":[]},
        {"PA":({"pn":"A","P":"{ {x_dot=y & true} |> [] (ch1?y --> skip;) }*"}, {"chset":{"ch1"}}, {"pn":"B","P":"{wait (5); ch1!1;}*"}),
         "Pre":"Ax>0&&Ay>0", "Post":"Ax>0", "Postr":"Ax>0", "RI":[("R1","Ax>0&&Ay>0")], "OI":[]},
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
         "Post": """Ap<=Bop""", "Postr": """Ap<=Bop""",
         "RI":[("R1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                         ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                         (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
                         &&Av==Bv&&Ap==Bp""")], "OI":[]},
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
        # {"PA":({"pn":"A","P":"ch1?x;{x_dot = -y * x, T_dot = -1 & T > 0} invariant unsol {x} [x>0];"}, {"chset":{"ch1"}}, 
        #        {"pn":"B","P":"ch1!4; wait (2); wait (3);"}),
        #  "Pre":"AT==5", "Post":"Ax>0", "Postr":"Ax>0", "RI":[], 
        #  "OI":["{x_dot = -y * x, T_dot = -1 & T > 0} invariant ghost z (z_dot = y * z / 2)[x * z * z == 1];"]},
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

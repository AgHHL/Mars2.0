theory BigStepSimple
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>Communications\<close>
datatype comm =
  Send cname exp        ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Cond fform proc proc        ("IF _ THEN _ ELSE _ FI" [95,94] 93)
| Wait exp  \<comment> \<open>Waiting for a specified amount of time\<close>
| IChoice proc proc  \<comment> \<open>Nondeterminism\<close>
| EChoice "(comm \<times> proc) list"  \<comment> \<open>External choice\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE fform "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc =
  Single proc
| Parallel pproc "cname set" pproc

text \<open>Global states\<close>
datatype gstate =
  State state
| ParState gstate gstate

subsection \<open>Traces\<close>

datatype comm_type = In | Out | IO

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock real "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

fun WaitBlk :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> trace_block" where
  "WaitBlk d p rdy = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"

lemma WaitBlk_simps [simp]:
  "WaitBlk d p rdy = WaitBlock d (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
  by auto

declare WaitBlk.simps [simp del]

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (auto)+

lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma restrict_cong_to_eq2:
  fixes x :: real
  shows "restrict p1 {0..} = restrict p2 {0..} \<Longrightarrow> 0 \<le> x \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext:
  fixes t1 t2 :: real
    and hist1 hist2 :: "real \<Rightarrow> gstate"
  shows "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  apply (auto simp add: restrict_def)
  done
  

lemma WaitBlk_ext_real:
  fixes t1 :: real
    and t2 :: real
  shows "t1 = t2 \<Longrightarrow> (\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
         WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  by (auto simp add: restrict_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  by (auto)+

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
proof -
  have a: "t1 = t2" "rdy1 = rdy2"
    using assms WaitBlk_cong 
    by blast+
  show ?thesis
    using restrict_cong_to_eq assms 
    by auto
qed

lemma WaitBlk_split1:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "t1 < t"
  shows "WaitBlk t1 p1 rdy = WaitBlk t1 p2 rdy"
  apply auto apply (rule ext) subgoal for x
      using assms[unfolded ] 
      using restrict_cong_to_eq[of p1 t p2 x] 
      apply auto
    done
  done

lemma WaitBlk_split2:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "t1 < t"
  shows "WaitBlk (t - t1) (\<lambda>\<tau>::real. p1 (\<tau> + t1)) rdy =
         WaitBlk (t - t1) (\<lambda>\<tau>::real. p2 (\<tau> + t1)) rdy"
  apply auto apply (rule ext) subgoal for x
      using assms[unfolded ]
      using restrict_cong_to_eq[of p1 t p2 "x + t1"] by auto
    done

lemmas WaitBlk_split = WaitBlk_split1 WaitBlk_split2
declare WaitBlk_simps [simp del]

type_synonym trace = "trace_block list"

type_synonym tassn = "trace \<Rightarrow> bool"


subsection \<open>Big-step semantics\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((ch[!]e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((ch[?]var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (s(var := e s))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| condB1: "b s1 \<Longrightarrow> big_step p1 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| condB2: "\<not> b s1 \<Longrightarrow> big_step p2 s1 tr s2 \<Longrightarrow> big_step (IF b THEN p1 ELSE p2 FI) s1 tr s2"
| waitB1: "e s > 0 \<Longrightarrow> big_step (Wait e) s [WaitBlk (e s) (\<lambda>_. State s) ({}, {})] s"
| waitB2: "\<not> e s > 0 \<Longrightarrow> big_step (Wait e) s [] s"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| EChoiceSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (OutBlock ch (e s1) # tr2) s2"
| EChoiceSendB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s1 tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              OutBlock ch (e s1) # tr2) s2"
| EChoiceReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (InBlock ch v # tr2) s2"
| EChoiceReceiveB2: "(d::real) > 0 \<Longrightarrow> i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s1(var := v)) tr2 s2 \<Longrightarrow>
    big_step (EChoice cs) s1 (WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice cs) #
                              InBlock ch v # tr2) s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy] s2"

lemma big_step_cong:
  "big_step c s1 tr s2 \<Longrightarrow> tr = tr' \<Longrightarrow> s2 = s2' \<Longrightarrow> big_step c s1 tr' s2'"
  by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
inductive_cases condE: "big_step (Cond b p1 p2) s1 tr s2"
inductive_cases waitE: "big_step (Wait d) s1 tr s2"
inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"



fun RepN :: "nat \<Rightarrow> proc \<Rightarrow> proc" where
  "RepN 0 c = Skip"
| "RepN (Suc n) c = c; RepN n c"

lemma big_step_rep:
  "big_step (Rep c) s1 tr1 s2 \<longleftrightarrow> (\<exists>n. big_step (RepN n c) s1 tr1 s2)"
proof -
  have "big_step p s1 tr1 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<exists>n. big_step (RepN n c) s1 tr1 s2" for p s1 tr1 s2
    apply (induction rule: big_step.induct, auto)
     apply (rule exI[where x=0])
    apply simp apply (rule skipB)
    subgoal for s1 tr1 s2 tr2 s3 n
      apply (rule exI[where x="Suc n"])
      apply simp apply (rule seqB) by auto
    done
  moreover have "\<And>s1 tr1 s2. big_step (RepN n c) s1 tr1 s2 \<Longrightarrow> big_step (Rep c) s1 tr1 s2" for n
    apply (induction n)
     apply simp apply (elim skipE) apply (auto intro: RepetitionB1)[1]
    apply simp apply (elim seqE) apply (auto intro: RepetitionB2) 
    done
  ultimately show ?thesis
    by blast
    qed


lemma big_step_assoc:"big_step ((a;b);c) s1 tr1 s2 \<longleftrightarrow> big_step (a;(b;c)) s1 tr1 s2"
  apply(auto elim!: seqE)
   apply (simp add: seqB)+
  by (smt (verit, ccfv_threshold) append.assoc seqB)


lemma RepNf:"big_step (c; RepN n c) s1 tr1 s2 \<longleftrightarrow> big_step (RepN n c; c) s1 tr1 s2"
proof(induction n arbitrary : s1 tr1 s2)
  case 0
  then show ?case 
    apply auto
    apply (metis append.left_neutral append.right_neutral seqB seqE skipB skipE)+
    done
next
  case (Suc n)
  show ?case 
    apply(auto elim!: seqE)
    using Suc
    using big_step_assoc seqB apply blast
    by (simp add: Suc seqB)
qed

lemma RepetitionB3:"big_step  (Rep p) s1 tr1 s2 \<Longrightarrow> big_step p s2 tr2 s3 \<Longrightarrow> tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
  unfolding big_step_rep
  apply auto
  subgoal for n
    apply(induction n arbitrary: s1 tr1 s2 tr2 s3 tr)
    subgoal for s1 tr1 s2 tr2 s3 tr
      apply simp
      apply(auto elim!: skipE)
      apply(rule exI[where x=1])
      apply auto
      apply(rule big_step_cong)   
        apply rule
         apply simp
        apply rule
      by auto
    subgoal for n s1 tr1 s2 tr2 s3 tr
      apply simp
      apply(auto elim!: seqE)
      subgoal premises pre for tri1 si tri2
      proof-
        obtain nn where c:"big_step (RepN nn p) si (tri2 @ tr2) s3"
          using pre(1)[of s2 tr2 s3 _ tri2 si]
          using pre(2,3,4,5,6)
          by auto
        show ?thesis
          apply(rule exI[where x="nn+1"])
          apply simp
          apply rule
          using pre(2,3,4,5,6) c
          by auto
      qed
      done
    done
  done


subsection \<open>Validity\<close>

text \<open>Assertion is a predicate on states and traces\<close>

type_synonym assn = "state \<Rightarrow> trace \<Rightarrow> bool"

definition IValid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> ([(1_)]/ (_)/ [(1_)])" 50) where
  "\<Turnstile> [P] c [Q] \<longleftrightarrow> (\<forall>s2 tr2. Q s2 tr2 \<longrightarrow> (\<exists> s1 tr1 tr. P s1 tr1 \<and> big_step c s1 tr s2 \<and> tr2=tr1@tr))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_refl [simp]:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "(P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>A R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A R)"
  unfolding entails_def by auto

lemma Valid_ex_pre:
  "(\<exists> v. \<Turnstile> [P v] c [Q]) \<Longrightarrow> \<Turnstile> [\<lambda>s t. \<exists>v. P v s t] c [Q]"
  unfolding IValid_def 
  by blast

lemma Valid_ex_post:
  "(\<And> v. \<Turnstile> [P] c [Q v]) \<Longrightarrow> \<Turnstile> [P] c [\<lambda>s t. \<exists>v. Q v s t]"
  unfolding IValid_def by auto

theorem Valid_strengthen_pre:
  "P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<Turnstile> [P] c [Q] \<Longrightarrow> \<Turnstile> [P'] c [Q]"
  unfolding IValid_def entails_def by blast

theorem Valid_weaken_post:
  "Q' \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<Turnstile> [P] c [Q] \<Longrightarrow> \<Turnstile> [P] c [Q']"
  unfolding IValid_def entails_def by blast

theorem Valid_disj:
  " \<Turnstile> [P1] c [Q1]\<Longrightarrow> \<Turnstile> [P2] c [Q2] \<Longrightarrow> \<Turnstile> [\<lambda> s tr. P1 s tr \<or> P2 s tr] c [\<lambda> s tr. Q1 s tr \<or> Q2 s tr]"
  unfolding IValid_def entails_def by blast

theorem Valid_skip:
  "\<Turnstile> [P] Skip [P]"
  unfolding IValid_def
  apply auto
  subgoal for s2 tr2
    apply (rule exI[where x= s2])
    apply (rule exI[where x= tr2])
    apply auto
    apply rule
    done
  done

theorem Valid_assign:
  "\<Turnstile> [Q] var ::= e [\<lambda> s tr. \<exists>x. s var = e (s(var := x)) \<and> Q (s(var := x)) tr]"
  unfolding IValid_def
  apply auto
  subgoal for s2 tr2 x
    apply (rule exI[where x="s2(var := x)"])
    apply (rule exI[where x= tr2])
    apply auto
    apply (rule big_step_cong)
      apply rule
     apply auto
    done
  done

theorem Valid_send:
  "\<Turnstile> [Q] Cm (ch[!]e) [\<lambda> s tr. \<exists> tr'. Q s tr' 
                        \<and> (tr = tr'@ [OutBlock ch (e s)] 
                           \<or> (\<exists> d>0. tr = tr'@ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)]))]"
  unfolding IValid_def
  apply clarify
  subgoal for s2 tr2 tr'
    apply(rule exI[where x= s2])
    apply(rule exI[where x= tr'])
    apply auto
     apply rule+
    by auto
  done


theorem Valid_receive:
  "\<Turnstile> [Q]
       Cm (ch[?]var) [\<lambda>s tr. \<exists> x tr'. Q (s(var := x)) tr' 
                       \<and> (tr = tr'@ [InBlock ch (s var)]
                          \<or> (\<exists> d>0. tr = tr'@ [WaitBlk d (\<lambda>_. State (s(var := x))) ({}, {ch}), InBlock ch (s var)]))]"
  unfolding IValid_def
  apply clarify
  subgoal for s2 tr2 x tr'
    apply(rule exI[where x="s2(var := x)"])
    apply(rule exI[where x= tr'])
    apply auto
    subgoal
      apply (rule big_step_cong)
        apply (rule receiveB1)
       apply auto
      done
    subgoal
      apply (rule big_step_cong)
        apply (rule receiveB2)
        apply auto
      done
    done
  done


theorem Valid_seq:
  "\<Turnstile> [P] c1 [Q] \<Longrightarrow> \<Turnstile> [Q] c2 [R] \<Longrightarrow> \<Turnstile> [P] c1; c2 [R]"
  unfolding IValid_def
  by (metis append_assoc seqB)

theorem Valid_cond:
  "\<Turnstile> [\<lambda> s tr. b s \<and> P s tr] c1 [Q1] \<Longrightarrow> 
   \<Turnstile> [\<lambda> s tr. \<not> b s \<and> P s tr] c2 [Q2] \<Longrightarrow>
   \<Turnstile> [P] IF b THEN c1 ELSE c2 FI [\<lambda> s tr. Q1 s tr \<or> Q2 s tr]"
  unfolding IValid_def   
  by (metis condB1 condB2)

theorem Valid_wait:
  "\<Turnstile> [P] Wait e [\<lambda> s tr. if e s\<le>0 then P s tr else \<exists> tr'. P s tr' \<and> tr = tr' @ [WaitBlk (e s) (\<lambda>_. State s) ({}, {})]]"
  unfolding IValid_def
  apply auto
   apply (meson eucl_less_le_not_le self_append_conv waitB2)
  by (metis not_le_imp_less waitB1)

theorem Valid_rep:
  assumes "\<And> n. \<Turnstile> [P (n::nat)] c [P (n+1)]"
  shows "\<Turnstile> [P 0] Rep c [\<lambda> s tr . \<exists> n. P n s tr]"
  unfolding IValid_def
  apply auto
  subgoal for s2 tr2 n
    apply(induct n arbitrary: s2 tr2)
    subgoal for s2 tr2
      apply (rule exI[where x=s2])
      apply (rule exI[where x=tr2])
      apply simp
      by (rule RepetitionB1)
    subgoal premises pre for n s2 tr2
    proof-
      have "(\<exists>s1 tr1. P n s1 tr1 \<and> (\<exists>tr. big_step c s1 tr s2 \<and> tr2 = tr1 @ tr))"
        using assms[of n] unfolding IValid_def
        using pre
      by auto
    then obtain s1 tr1 tr' where c1:"P n s1 tr1 \<and> big_step c s1 tr' s2 \<and> tr2 = tr1 @ tr'"
      by auto
    then obtain s0 tr0 tr'' where c2:"P 0 s0 tr0 \<and> big_step (Rep c) s0 tr'' s1 \<and> tr1 = tr0 @ tr''"
      using pre(1)[of s1 tr1]
      by auto
    show ?thesis
      apply(rule exI[where x=s0])
      apply(rule exI[where x=tr0])
      using c2 c1
      apply simp
      apply(rule RepetitionB3)
      by auto
  qed
  done
  done


theorem Valid_rep1:
  "\<Turnstile> [P] Rep c [P]"
  unfolding IValid_def
  apply auto
  subgoal for s2 tr2 
    apply (rule exI[where x=s2])
    apply (rule exI[where x=tr2])
    apply auto
    by(rule RepetitionB1)
  done

theorem Valid_rep2:
  assumes "\<Turnstile> [P] Rep c;c [Q]"
  shows"\<Turnstile> [P] Rep c [Q]"
  unfolding IValid_def
  apply auto
  subgoal premises pre for s2 tr2 
  proof-
    obtain s1 tr1 tr where c:"P s1 tr1 \<and> big_step (Rep c; c) s1 tr s2 \<and> tr2 = tr1 @ tr"
      using pre assms unfolding IValid_def by blast
    show ?thesis
      apply(rule exI[where x="s1"])
      apply(rule exI[where x="tr1"])
      using c 
      apply auto
      apply(auto elim!: seqE)
      apply(rule RepetitionB3)
        apply simp+
      done
  qed
  done

theorem Valid_rep3:
  assumes "\<Turnstile> [P] c;Rep c [Q]"
  shows"\<Turnstile> [P] Rep c [Q]"
  unfolding IValid_def
  apply auto
  subgoal premises pre for s2 tr2 
  proof-
    obtain s1 tr1 tr where c:"P s1 tr1 \<and> big_step (c;Rep c) s1 tr s2 \<and> tr2 = tr1 @ tr"
      using pre assms unfolding IValid_def by blast
    show ?thesis
      apply(rule exI[where x="s1"])
      apply(rule exI[where x="tr1"])
      using c 
      apply auto
      apply(auto elim!: seqE)
      apply(rule RepetitionB2)
        apply simp+
      done
  qed
  done


      
theorem Valid_ichoice:
  assumes "\<Turnstile> [P] c1 [Q1]"
    and "\<Turnstile> [P] c2 [Q2]"
  shows "\<Turnstile> [P] IChoice c1 c2 [\<lambda> s tr. Q1 s tr \<or> Q2 s tr]"
  using assms unfolding IValid_def 
  by (metis IChoiceB1 IChoiceB2)

theorem Valid_ichoice1:
  assumes "\<Turnstile> [P] c1 [Q]"
  shows "\<Turnstile> [P] IChoice c1 c2 [Q]"
  using assms unfolding IValid_def 
  by (metis IChoiceB1)

theorem Valid_ichoice2:
  assumes "\<Turnstile> [P] c2 [Q]"
  shows "\<Turnstile> [P] IChoice c1 c2 [Q]"
  using assms unfolding IValid_def 
  by (metis IChoiceB2)


theorem Valid_echoice1:
  assumes "i<length es"
    and "es ! i = (ch[!]e, c)"
    and "\<Turnstile> [\<lambda> s tr. \<exists> tr'. P s tr' 
                        \<and> (tr = tr'@ [OutBlock ch (e s)] 
                           \<or> (\<exists> d>0. tr = tr'@ [WaitBlk d (\<lambda>_. State s) (rdy_of_echoice es), OutBlock ch (e s)]))] c [Q]"
  shows "\<Turnstile>[P] EChoice es [Q]"
  unfolding IValid_def
  apply clarify
  subgoal premises pre for s2 tr2
  proof-
    obtain s1 tr1 tr tr' where c:"P s1 tr' \<and>
                  (tr1 = tr' @ [OutBlock ch (e s1)] \<or> (\<exists>d>0. tr1 = tr' @ [WaitBlk d (\<lambda>_. State s1) (rdy_of_echoice es), OutBlock ch (e s1)])) \<and>
           big_step c s1 tr s2 \<and> tr2 = tr1 @ tr"
      using assms pre unfolding IValid_def by meson
    show ?thesis
      apply(rule exI[where x=s1])
      apply(rule exI[where x=tr'])
      using c assms
      apply auto
       apply(rule EChoiceSendB1)
         apply simp+
      apply(rule EChoiceSendB2)
         apply simp+
      done
  qed
  done


theorem Valid_echoice2:
  assumes "i<length es"
    and "es ! i = (ch[?]var, c)"
    and "\<Turnstile> [\<lambda>s tr. \<exists> x tr'. P (s(var := x)) tr' 
                       \<and> (tr = tr'@ [InBlock ch (s var)]
                          \<or> (\<exists> d>0. tr = tr'@ [WaitBlk d (\<lambda>_. State (s(var := x))) (rdy_of_echoice es), InBlock ch (s var)]))] c [Q]"
  shows "\<Turnstile>[P] EChoice es [Q]"
  unfolding IValid_def
  apply clarify
  subgoal premises pre for s2 tr2
  proof-
    obtain s1 tr1 tr x tr' where c:"P (s1(var := x)) tr' \<and>
               (tr1 = tr' @ [InBlock ch (s1 var)] \<or>
                (\<exists>d>0. tr1 = tr' @ [WaitBlk d (\<lambda>_. State (s1(var := x))) (rdy_of_echoice es), InBlock ch (s1 var)])) \<and>
           big_step c s1 tr s2 \<and> tr2 = tr1 @ tr"
      using assms pre unfolding IValid_def by meson
    show ?thesis
      apply(rule exI[where x="s1(var := x)"])
      apply(rule exI[where x=tr'])
      using c assms
      apply auto
       apply(rule EChoiceReceiveB1)
         apply simp+
      subgoal for d
        thm EChoiceReceiveB2
      apply(rule big_step_cong)
      apply(rule EChoiceReceiveB2[of d i es ch var c "s1(var := x)" "s1 var"])
         apply simp+
        done
      done
  qed
  done






end

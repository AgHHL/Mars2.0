theory BigStepContinuous
  imports BigStepSimple
begin


subsection \<open>Hoare rules for ODE\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_ode:
  "\<Turnstile>[P]
     (Cont ode b)
     [\<lambda>s tr. (\<not>b s \<and> P s tr) \<or>
            (\<exists>d p. 0 < d \<and> ODEsol ode p d \<and> p d = s \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and>
                (\<exists>tr'. P (p 0) tr' \<and> tr = (tr' @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])))]"
  unfolding IValid_def
  apply clarify
  subgoal for s2 tr2
    apply auto
    subgoal 
      apply(rule exI[where x= s2])
      apply(rule exI[where x= tr2])
      apply auto
      apply rule
      by auto
    subgoal for d p tr'
      apply(rule exI[where x= "p 0"])
      apply(rule exI[where x= tr'])
      apply auto
      apply rule
      by auto
    done
  done




subsection \<open>Hoare rules for interrupt\<close>

text \<open>Weakest precondition form\<close>
theorem Valid_interrupt1:
  assumes "i < length cs"
    and "cs ! i = (ch[!]e, c)"
    and "\<Turnstile>[\<lambda>s tr. (\<exists> tr'. P s tr' \<and> tr=tr' @ [OutBlock ch (e s)]) \<or> (\<exists>d p. d>0 \<and> ODEsol ode p d \<and> p d = s \<and>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> (\<exists> tr'. P (p 0) tr' \<and> tr = tr'@ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                       OutBlock ch (e (p d))]))] c [Q]"
  shows "\<Turnstile> [P] Interrupt ode b cs [Q]"
  using assms(3)
  unfolding IValid_def
  apply auto
  subgoal premises pre for s2 tr2
  proof-
    obtain s1 tr1 where c:"((\<exists>tr'. P s1 tr' \<and> tr1 = tr' @ [OutBlock ch (e s1)]) \<or>
            (\<exists>d>0. \<exists>p. ODEsol ode p d \<and>
                       p d = s1 \<and>
                       (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and>
                       (\<exists>tr'. P (p 0) tr' \<and> tr1 = tr' @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (p d))]))) \<and>
           (\<exists>tr. big_step c s1 tr s2 \<and> tr2 = tr1 @ tr)"
      using pre by fastforce
    then show ?thesis 
      apply auto
      subgoal for tr tr'
        apply(rule exI[where x="s1"])
        apply(rule exI[where x="tr'"])
        apply auto
        apply(rule InterruptSendB1)
        using assms
          apply simp+
        done
      subgoal for tr d p tr'
        apply(rule exI[where x="p 0"])
        apply(rule exI[where x="tr'"])
        apply auto
        apply(rule InterruptSendB2)
        using assms
               apply simp+
        done
      done
  qed
  done



theorem Valid_interrupt2:
  assumes "i < length cs"
    and "cs ! i = (ch[?]var, c)"
    and "\<Turnstile>[\<lambda>s tr. (\<exists> x tr'. P (s(var:=x)) tr' \<and> tr=tr' @ [InBlock ch (s var)]) \<or> (\<exists>d p x. d>0 \<and> ODEsol ode p d \<and> p d = s(var:=x) \<and>
                        (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> (\<exists> tr'. P (p 0) tr' \<and> tr = tr'@ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs),
                                       InBlock ch (s var)]))] c [Q]"
  shows "\<Turnstile> [P] Interrupt ode b cs [Q]"
  using assms(3)
  unfolding IValid_def
  apply auto
  subgoal premises pre for s2 tr2
  proof-
    obtain s1 tr1 where c:"((\<exists>x tr'. P (s1(var := x)) tr' \<and> tr1 = tr' @ [InBlock ch (s1 var)]) \<or>
               (\<exists>d>0. \<exists>p. ODEsol ode p d \<and>
                          (\<exists>x. p d = s1(var := x)) \<and>
                          (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and>
                          (\<exists>tr'. P (p 0) tr' \<and> tr1 = tr' @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs), InBlock ch (s1 var)]))) \<and>
              (\<exists>tr. big_step c s1 tr s2 \<and> tr2 = tr1 @ tr)"
      using pre by fastforce
    then show ?thesis 
      apply auto
      subgoal for tr x tr'
        apply(rule exI[where x="s1(var := x)"])
        apply(rule exI[where x="tr'"])
        apply auto
        apply(rule InterruptReceiveB1)
        using assms
          apply simp+
        done
      subgoal for tr d p x tr'
        apply(rule exI[where x="p 0"])
        apply(rule exI[where x="tr'"])
        apply auto
        apply(rule InterruptReceiveB2)
        using assms
               apply simp+
        done
      done
  qed
  done





theorem Valid_interrupt3:
  "\<Turnstile>[P]
     Interrupt ode b cs
     [\<lambda>s tr. (\<not>b s \<and> P s tr) \<or>
            (\<exists>d p. 0 < d \<and> ODEsol ode p d \<and> p d = s \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and>
                (\<exists>tr'. P (p 0) tr' \<and> tr = (tr' @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)])))]"
  unfolding IValid_def
  apply clarify
  subgoal for s2 tr2
    apply auto
    subgoal 
      apply(rule exI[where x= s2])
      apply(rule exI[where x= tr2])
      apply auto
      apply rule
      by auto
    subgoal for d p tr'
      apply(rule exI[where x= "p 0"])
      apply(rule exI[where x= tr'])
      apply auto
      apply rule
      by auto
    done
  done




end

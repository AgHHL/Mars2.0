theory BigStepInterruptParallel3
  imports BigStepInterruptParallel2 
begin





lemma sync_gassn_interrupt_sol_interrupt_sol2:
  assumes "\<not>compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1 \<and> pn2 \<in> pns2 \<and> pns1 \<inter> pns2 = {}"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_sol_cg I2 pn2 e2 G2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pp (\<lambda>_ .0) 
         (\<lambda>_ . IFG  (\<lambda>s0. e1 (the (s0 pn1)) > 0) 
               THEN (IFG (\<lambda> s0. e2 (the (s0 pn2)) > 0)
                     THEN com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2)
                     ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (G2 0))
                     FI)
               ELSE (IFG (\<lambda> s0. e2 (the (s0 pn2)) > 0)
                     THEN (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_sol_cg I2 pn2 e2 G2 specs2))
                     ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (G2 0)
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_sol_cg I2 pn2 e2 G2 specs2))
                     FI)
               FI)
          ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
           (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply(subgoal_tac"e2 (the (s0 pn2)) = e2 (the (s12 pn2))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval2[of pn2]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
      text \<open>case 1 - 1\<close>
      subgoal for tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply simp
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply(rule )
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 1 - 3\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 1 - 5\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 6\<close>
      subgoal for tr1' a1 b1 p1
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 2 - 1\<close>
      subgoal for tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 2 - 2\<close>
      subgoal
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule )
        by auto
      text \<open>case 2 - 3\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 2 - 4\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of j])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 2 - 5\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 2 - 6\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of j])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v tr1'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI1)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
            by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 3 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            unfolding cond_gassn2_def
            apply auto
            subgoal
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            done
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 3 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 4 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 4 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of i])
        subgoal by auto
             apply simp
        by auto
      text \<open>case 4 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 4 - 4\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 4 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 4 - 6\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 5 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 5 - 2\<close>
      subgoal for i ch1 P v tr1'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI1)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 5 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            unfolding cond_gassn2_def
            apply auto
            subgoal
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            done
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 5 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 5 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 5 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 6 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 6 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of i])
        subgoal by auto
             apply simp
        by auto
      text \<open>case 6 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 6 - 4\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 6 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 6 - 6\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      done
    done
  done




lemma sync_gassn_interrupt_sol_interrupt_solInf1:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_solInf_cg (delay_inv d I2) (map (spec_wait_of d) specs2)))
         ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
           apply (auto elim!: interrupt_solInf_cg.cases)[6]
      text \<open>case 1 - 1\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            subgoal by auto
               apply simp
            by auto
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases "d>e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d=e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
                  apply simp
              by auto
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d<e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                  apply auto
              apply(rule interrupt_sol_cg.intros(1))
              subgoal by auto
               apply simp
                apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      by auto
    text \<open>case 1 - 3\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            subgoal by auto
               apply simp
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases "d>e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d=e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
                  apply simp
              by auto
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d<e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                  apply auto
              apply(rule interrupt_sol_cg.intros(1))
              subgoal by auto
               apply simp
                apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      by auto
    text \<open>case 2 - 1\<close>
    subgoal for j ch2 Q v tr2'
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(1)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 2\<close>
    subgoal for j ch2 Q d v tr2' a b p
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(2)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 3\<close>
    subgoal for j
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(3)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 4\<close>
    subgoal for j
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(4)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 3 - 1\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
          by auto               
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(1)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(3)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 3 - 2\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(2)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 3 - 3\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
            apply auto
          using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)             
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(3)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(3)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 3 - 4\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(4)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 1\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(4)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 2\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) by auto
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 4 - 3\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(4)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 4\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) 
          using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 5 - 1\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
          using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)              
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(1)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(5)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 5 - 2\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(2)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 5 - 3\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
            by auto                       
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(3)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(5)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 5 - 4\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(4)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 6 - 1\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(6)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 6 - 2\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE) 
          using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 4 - 3\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(6)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 4\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) 
          by auto
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    done
  done
  done


thm sync_gassn_interrupt_sol_interrupt_sol2
thm sync_gassn_interrupt_sol_interrupt_solInf1
thm sync_gassn_interrupt_solInf_interrupt_solInf1

lemma sync_gassn_interrupt_sol_interrupt_solInf2:
  assumes "\<not>compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pp (\<lambda>_ .0) 
         (\<lambda>_ . IFG  (\<lambda>s0. e1 (the (s0 pn1)) > 0) 
               THEN com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2)
               ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_solInf_cg I2 specs2))
               FI)
          ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
           (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
        apply (elim interrupt_sol_cg.cases) apply auto
           apply (auto elim!: interrupt_solInf_cg.cases)[6]
      text \<open>case 1 - 1\<close> 
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      text \<open>case 1 - 3\<close> 
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms) 
      text \<open>case 2 - 1\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(1)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 2\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(2)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 3\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(3)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 4\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(4)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
            apply auto
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          unfolding cond_gassn2_def
          apply auto
          subgoal
            apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          subgoal
            apply(rule disj_gassn_disjI1)
            apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        text \<open>case 4 - 1\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
        text \<open>case 4 - 2\<close>
        subgoal
          apply(elim combine_blocks_waitE1)
          by(auto simp add:assms)
        text \<open>case 4 - 3\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
      text \<open>case 4 - 4\<close>
      subgoal
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      text \<open>case 5 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          apply auto
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          unfolding cond_gassn2_def
          apply auto
          subgoal
            apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          subgoal
            apply(rule disj_gassn_disjI1)
            apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 5 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
      text \<open>case 5 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 5 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        text \<open>case 6 - 1\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
        text \<open>case 6 - 2\<close>
        subgoal
          apply(elim combine_blocks_waitE1)
          by(auto simp add:assms)
        text \<open>case 6 - 3\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
      text \<open>case 6 - 4\<close>
      subgoal
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      done
    done
  done




lemma sync_gassn_interrupt_sol_interrupt_sol1_test1:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1 \<and> pn2 \<in> pns2 \<and> pns1 \<inter> pns2 = {}"
     and  "e1 (the (s0 pn1)) \<le> 0 \<and> e2 (the (s0 pn2)) \<le> 0"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_sol_cg I2 pn2 e2 G2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_sol_cg (delay_inv d I2) pn2 (\<lambda>s. e2 s - d) (\<lambda> t. G2 (t+d)) (map (spec_wait_of d) specs2))
         \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg (delay_inv d I1) pn1 (\<lambda>s. e1 s - d) (\<lambda> t. G1 (t+d)) (map (spec_wait_of d) specs1)) (G2 d))
         ((map (if1 chs pns1 pns2 I2 pn2 e2 (\<lambda> d. false_gassn) specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 (\<lambda> d. false_gassn) specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply(subgoal_tac"e2 (the (s0 pn2)) = e2 (the (s12 pn2))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval2[of pn2]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
      using assms(3)
                          apply auto
      subgoal
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)   
        apply(rule)
              apply auto
        apply(rule ) by auto
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)   
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(3)[of i]) 
          apply simp+
        done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)   
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(5)[of i]) 
          apply simp+
        done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)   
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(3)[of i]) 
          apply simp+
        done
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              done
            done
          done
        subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)   
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(5)[of i]) 
          apply simp+
        done
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
            apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          done
        done
      done

lemma sync_gassn_interrupt_sol_interrupt_sol1_test2:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1 \<and> pn2 \<in> pns2 \<and> pns1 \<inter> pns2 = {}"
     and  "e1 (the (s0 pn1)) \<le> 0 \<and> e2 (the (s0 pn2)) > 0"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_sol_cg I2 pn2 e2 G2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_sol_cg (delay_inv d I2) pn2 (\<lambda>s. e2 s - d) (\<lambda> t. G2 (t+d)) (map (spec_wait_of d) specs2)))
         ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 (\<lambda> d. false_gassn) specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply(subgoal_tac"e2 (the (s0 pn2)) = e2 (the (s12 pn2))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval2[of pn2]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
      using assms(3)
                          apply auto
      subgoal
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(3)[of i]) 
          apply simp+
        done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of i]) 
          apply simp+
        done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(5)[of i]) 
          apply simp+
        done
      subgoal for i
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule)
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of i]) 
          apply simp+
        done
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            done
          done
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              done
            done
          done
        subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
        subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
      subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
       subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
          done
        done
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
          subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
            apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
          done
        done
      done


end
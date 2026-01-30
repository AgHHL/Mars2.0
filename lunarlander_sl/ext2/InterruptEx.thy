theory InterruptEx
  imports BigStepInterruptParallel3
begin

definition A :: pname where "A = ''a''"
definition B :: pname where "B = ''b''"
definition C :: pname where "C = ''c''"
definition X :: char where "X = CHR ''x''"
definition Y :: char where "Y = CHR ''y''"
definition Z :: char where "Z = CHR ''z''"
definition ch1t2 :: cname where "ch1t2 = ''ch1t2''"
definition ch2t1 :: cname where "ch2t1 = ''ch2t1''"
definition ch1 :: cname where "ch1 = ''ch1''"
definition ch2 :: cname where "ch2 = ''ch2''"

(*
lemma test_interrupt_unique:
  assumes "spec_of c1 Q1" "spec_of c2 Q2" "spec_of c Q"
  shows "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                      [(dh1[?]Y, c1),(dh2[?]Y, c2)] c)
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 dh1 (\<lambda>d v . Q1 {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}}),
                             InSpec2 dh2 (\<lambda>d v . Q2 {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
proof -
  have 1: "paramODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) 
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t))"
    unfolding paramODEsolInf_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
      apply auto
      apply (rule exI[where x="1"])
      apply auto
      apply (rule has_vector_derivative_projI)
      apply (auto simp add: state2vec_def)
      apply (rule has_vector_derivative_eq_rhs)
       apply (auto intro!: derivative_intros)[1]
      by simp
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  let ?specs = "[InSpec dh1 Y Q1,InSpec dh2 Y Q2]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_inf_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply (auto intro!: rel_list.intros) 
       apply (rule spec_of_es.intros)
       apply (rule assms)
      apply (rule spec_of_es.intros)
    apply(rule assms)
     apply (rule assms)
    subgoal for s0
      apply (simp only: updr_rpart_simp1)
      apply (rule interrupt_solInf_mono)
      apply (auto intro!: rel_list.intros spec2_entails.intros)
        subgoal for d v s0 apply (simp only: substr_assn2_def updr_rpart_simp2 subst_assn2_def)
          by (rule entails_triv)
        subgoal for d v s0 apply (simp only: substr_assn2_def updr_rpart_simp2 subst_assn2_def)
          by (rule entails_triv)
        done
      done
qed

definition interrupt1 :: "'a proc" where
"interrupt1 = (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(ch1[?]Y, Cm (ch1t2[!](\<lambda>_.0))),(ch2t1[?]Y, Skip)] Skip)"

lemma spec_interrupt1:
  shows "spec_of interrupt1
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch1 (\<lambda>d v . (wait_out_cv single_id_inv ch1t2 (\<lambda>_ . 0) (\<lambda>d. init)) {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}}),
                             InSpec2 ch2t1 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
  unfolding interrupt1_def
  apply(rule test_interrupt_unique)
  apply(rule spec_of_send)
  apply(rule spec_of_skip)
  apply(rule spec_of_skip)
  done


definition interrupt2 :: "'a proc" where
"interrupt2 = (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(ch2[?]Y, Cm (ch2t1[!](\<lambda>_.0))),(ch1t2[?]Y, Skip)] Skip)"

lemma spec_interrupt2:
  shows "spec_of interrupt2
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch2 (\<lambda>d v . (wait_out_cv single_id_inv ch2t1 (\<lambda>_ . 0) (\<lambda>d. init)) {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}}),
                             InSpec2 ch1t2 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
  unfolding interrupt2_def
  apply(rule test_interrupt_unique)
  apply(rule spec_of_send)
  apply(rule spec_of_skip)
  apply(rule spec_of_skip)
  done

lemma sync:
  "sync_gassn {ch1t2, ch2t1} {A} {B}
    (single_assn A ((interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch1 (\<lambda>d v . (wait_out_cv single_id_inv ch1t2 (\<lambda>_ . 0) (\<lambda>d. init)) {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}}),
                             InSpec2 ch2t1 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])))
    (single_assn B (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch2 (\<lambda>d v . (wait_out_cv single_id_inv ch2t1 (\<lambda>_ . 0) (\<lambda>d. init)) {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}}),
                             InSpec2 ch1t2 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])) s0 
    \<Longrightarrow>\<^sub>G PP"
  apply (auto simp add: single_assn_simps)
  apply (rule entails_g_trans)
   apply (rule sync_gassn_interrupt_solInf_interrupt_solInf1)
  subgoal unfolding rdy_of_comm_specg2_def
    by auto
  apply (auto simp add:ch1_def ch2_def ch1t2_def ch2t1_def)
*)



lemma test_interrupt_unique:
  assumes "spec_of c1 Q1" "spec_of c Q"
  shows "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
                      [(dh1[?]Y, c1)] c)
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 dh1 (\<lambda>d v . Q1 {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
proof -
  have 1: "paramODEsolInf (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) 
                       (\<lambda>s0 t. (rpart s0)(X := val s0 X + t))"
    unfolding paramODEsolInf_def apply clarify
    subgoal for s
      apply (rule conjI)
      subgoal apply (cases s)
        by (auto simp add: rpart.simps val.simps)
      unfolding ODEsolInf_def solves_ode_def has_vderiv_on_def
      apply auto
      apply (rule exI[where x="1"])
      apply auto
      apply (rule has_vector_derivative_projI)
      apply (auto simp add: state2vec_def)
      apply (rule has_vector_derivative_eq_rhs)
       apply (auto intro!: derivative_intros)[1]
      by simp
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>t v. ODE2Vec (ODE ((\<lambda>_ _. 0)(X := \<lambda>_. 1))) (vec2state v))"
  proof -
    have eq: "(\<chi> a. (if a = X then \<lambda>_. 1 else (\<lambda>_. 0)) (($) v)) = (\<chi> a. if a = X then 1 else 0)" for v::vec
      by auto
    show ?thesis
      unfolding fun_upd_def vec2state_def
      apply (auto simp add: state2vec_def eq)
      by (rule local_lipschitz_constI)
  qed
  let ?specs = "[InSpec dh1 Y Q1]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_inf_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply (auto intro!: rel_list.intros) 
       apply (rule spec_of_es.intros)
       apply (rule assms)
      apply (rule assms)
    subgoal for s0
      apply (simp only: updr_rpart_simp1)
      apply (rule interrupt_solInf_mono)
      apply (auto intro!: rel_list.intros spec2_entails.intros)
        subgoal for d v s0 apply (simp only: substr_assn2_def updr_rpart_simp2 subst_assn2_def)
          by (rule entails_triv)
        done
      done
qed

definition interrupt1 :: "'a proc" where
"interrupt1 = (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(ch1[?]Y, Skip)] Skip)"

lemma spec_interrupt1:
  shows "spec_of interrupt1
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch1 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
  unfolding interrupt1_def
  apply(rule test_interrupt_unique)
  apply(rule spec_of_skip)
  apply(rule spec_of_skip)
  done


definition interrupt2 :: "'a proc" where
"interrupt2 = (Interrupt (ODE ((\<lambda>_ _. 0)(X := (\<lambda>_. 1)))) (\<lambda>_. True)
               [(ch2[?]Y,Skip)] Skip)"

lemma spec_interrupt2:
  shows "spec_of interrupt2
           (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch2 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])"
  unfolding interrupt2_def
  apply(rule test_interrupt_unique)
  apply(rule spec_of_skip)
  apply(rule spec_of_skip)
  done

inductive specg2_entails :: "'a comm_specg2 \<Rightarrow> 'a comm_specg2 \<Rightarrow> bool" where
  "(\<And>d v s0. P1 d v s0 \<Longrightarrow>\<^sub>G P2 d v s0) \<Longrightarrow> specg2_entails (InSpecg2 ch P1) (InSpecg2 ch P2)"
| "(\<And>d v s0. Q1 d v s0 \<Longrightarrow>\<^sub>G Q2 d v s0) \<Longrightarrow> specg2_entails (OutSpecg2 ch Q1) (OutSpecg2 ch Q2)"

inductive_cases specg2_entails_inE: "specg2_entails (InSpecg2 ch P1) spec2"
inductive_cases specg2_entails_outE: "specg2_entails (OutSpecg2 ch Q1) spec2"

lemma rdy_of_specg2_entails:
  assumes "rel_list specg2_entails specs specs2"
  shows "rdy_of_comm_specg2 specs = rdy_of_comm_specg2 specs2"
  unfolding rdy_of_comm_specg2_def
  apply (rule rdy_info_of_list_cong)
  apply (rule rel_list_mono[OF _ assms])
  apply (elim specg2_entails.cases) by auto

lemma interrupt_solInfg_mono:
  assumes "rel_list specg2_entails specs specs2"
  shows "interrupt_solInf_cg I specs s0 \<Longrightarrow>\<^sub>G interrupt_solInf_cg I specs2 s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (induct rule: interrupt_solInf_cg.cases) apply auto
    subgoal for i ch Q v tr'
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim specg2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_cg.intros(1)[of i _ _ Q2])
        using assms(1) unfolding entails_g_def by auto
      done
    subgoal for i ch Q d' v tr' a b
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim specg2_entails_inE)
      subgoal for Q2
        apply (rule interrupt_solInf_cg.intros(2)[of i _ _ Q2])
        using assms(1) unfolding entails_g_def apply auto
        apply (rule rdy_of_specg2_entails) by auto
      done
    subgoal for i ch e Q tr'
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim specg2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_cg.intros(3)[of i _ _ Q2])
        using assms(1) unfolding entails_g_def by auto
      done
    subgoal for i ch E Q d tr' a b
      using rel_listD2[OF assms, of i] rel_listD1[OF assms] apply simp
      apply (elim specg2_entails_outE)
      subgoal for Q2
        apply (rule interrupt_solInf_cg.intros(4)[of i _ _ Q2])
        using assms(1) unfolding entails_g_def apply auto
        apply (rule rdy_of_specg2_entails) by auto
      done
    done
  done

lemma sync_gassn_emp_in:
  "ch \<notin> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (init_single pns1) (wait_in_cg I ch Q) s0 \<Longrightarrow>\<^sub>G
   wait_in_cg I ch (\<lambda>d v. sync_gassn chs pns1 pns2 (init_single pns1) (Q d v))s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for tr1'
        apply (elim init_single.cases) apply auto
        apply (elim sync_elims) apply auto
        subgoal for tr'
          apply (rule wait_in_cg.intros)
           apply (rule sync_gassn.intros) apply auto
           apply (rule init_single.intros) by auto
        done
      subgoal for d tr'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync_gassn_in_emp:
  "ch \<notin> chs \<Longrightarrow>
   sync_gassn chs pns1 pns2 (wait_in_cg I ch Q)  (init_single pns2) s0 \<Longrightarrow>\<^sub>G
   wait_in_cg I ch (\<lambda>d v. sync_gassn chs pns1 pns2 (Q d v) (init_single pns2))s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim wait_in_cg.cases) apply auto
      subgoal for tr1'
        apply (elim init_single.cases) apply auto
        apply (elim sync_elims) apply auto
        subgoal for tr'
          apply (rule wait_in_cg.intros)
           apply (rule sync_gassn.intros) apply auto
           apply (rule init_single.intros) by auto
        done
      subgoal for d tr'
        apply (elim init_single.cases) apply auto
        by (elim sync_elims)
      done
    done
  done

lemma sync:
  "sync_gassn {} {A} {B}
    (single_assn A (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch1 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})]))
    (single_assn B (interrupt_solInf_c (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)) 
                            [InSpec2 ch2 (\<lambda>d v . init {{Y := (\<lambda>s. v)}} {{X := (\<lambda>s. val s X + d)}})])) s0 
    \<Longrightarrow>\<^sub>G 
    interrupt_solInf_cg
     (merge_inv (single_inv A (\<lambda>s0 t s. s = upd s0 X (val s0 X + t))) (single_inv B (\<lambda>s0 t s. s = upd s0 X (val s0 X + t))))
     [InSpecg2 ''ch1'' (\<lambda> d v. (wait_in_cg (delay_inv d (single_inv ''b'' (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)))) ''ch2''
         (\<lambda>dd vv. init_single{''b'',''a''} 
                      {{Y := (\<lambda>_. vv)}}\<^sub>g at ''b'' {{X := (\<lambda>s. val s X + (d+dd))}}\<^sub>g at ''b'') 
                      {{Y := (\<lambda>_. v)}}\<^sub>g at ''a'' {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''a'')),
      InSpecg2 ''ch2'' (\<lambda> d v. (wait_in_cg (delay_inv d (single_inv ''a'' (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)))) ''ch1''
         (\<lambda>dd vv. init_single{''b'',''a''} 
                      {{Y := (\<lambda>_. vv)}}\<^sub>g at ''a'' {{X := (\<lambda>s. val s X + (d+dd))}}\<^sub>g at ''a'') 
                      {{Y := (\<lambda>_. v)}}\<^sub>g at ''b'' {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''b''))] s0"
  apply (auto simp add: single_assn_simps)
  apply (rule entails_g_trans)
   apply (rule sync_gassn_interrupt_solInf_interrupt_solInf1)
  subgoal unfolding rdy_of_comm_specg2_def
    by auto
  apply (auto simp add:ch1_def ch2_def)
  apply (rule interrupt_solInfg_mono)
   apply (auto intro!: rel_list.intros) 
  subgoal
    apply(rule specg2_entails.intros(1))
    apply (subst interrupt_solInf_cg_in)
    apply (rule entails_g_trans)
     apply(rule sync_gassn_subst_left)
     apply auto
    apply (rule entails_g_trans)
    apply(rule updg_mono)
     apply(rule sync_gassn_subst_left)
     apply auto
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule sync_gassn_emp_in)
    apply auto
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
    apply(rule wait_in_cg_mono)
     apply(rule sync_gassn_subst_right)
    apply(auto simp add:A_def B_def)
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule wait_in_cg_mono)
     apply(rule updg_mono)+
     apply(rule sync_gassn_subst_right)
      apply(auto simp add:A_def B_def)
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule wait_in_cg_mono)
     apply(rule updg_mono)+
     apply(rule sync_gassn_emp)
     apply simp
    by(rule entails_g_triv)
  subgoal
    apply(rule specg2_entails.intros(1))
    apply (subst interrupt_solInf_cg_in)
    apply (rule entails_g_trans)
     apply(rule sync_gassn_subst_right)
     apply(auto simp add:A_def B_def)
    apply (rule entails_g_trans)
    apply(rule updg_mono)
     apply(rule sync_gassn_subst_right)
     apply auto
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule sync_gassn_in_emp)
    apply auto
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
    apply(rule wait_in_cg_mono)
     apply(rule sync_gassn_subst_left)
    apply(auto simp add:A_def B_def)
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule wait_in_cg_mono)
     apply(rule updg_mono)+
     apply(rule sync_gassn_subst_left)
      apply(auto simp add:A_def B_def)
    apply (rule entails_g_trans)
     apply(rule updg_mono)+
     apply(rule wait_in_cg_mono)
     apply(rule updg_mono)+
     apply(rule sync_gassn_emp)
     apply simp
    by(rule entails_g_triv)
  done

lemma full_spec:
  "spec_of_global
    (Parallel (Single A interrupt1)
              {}
              (Single B interrupt2))
    (interrupt_solInf_cg
     (merge_inv (single_inv A (\<lambda>s0 t s. s = upd s0 X (val s0 X + t))) (single_inv B (\<lambda>s0 t s. s = upd s0 X (val s0 X + t))))
     [InSpecg2 ''ch1'' (\<lambda> d v. (wait_in_cg (delay_inv d (single_inv ''b'' (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)))) ''ch2''
         (\<lambda>dd vv. init_single{''b'',''a''} 
                      {{Y := (\<lambda>_. vv)}}\<^sub>g at ''b'' {{X := (\<lambda>s. val s X + (d+dd))}}\<^sub>g at ''b'') 
                      {{Y := (\<lambda>_. v)}}\<^sub>g at ''a'' {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''a'')),
      InSpecg2 ''ch2'' (\<lambda> d v. (wait_in_cg (delay_inv d (single_inv ''a'' (\<lambda>s0 t s. s = upd s0 X (val s0 X + t)))) ''ch1''
         (\<lambda>dd vv. init_single{''b'',''a''} 
                      {{Y := (\<lambda>_. vv)}}\<^sub>g at ''a'' {{X := (\<lambda>s. val s X + (d+dd))}}\<^sub>g at ''a'') 
                      {{Y := (\<lambda>_. v)}}\<^sub>g at ''b'' {{X := (\<lambda>s. val s X + d)}}\<^sub>g at ''b''))])"
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single[OF spec_interrupt1])
     apply (rule spec_of_single[OF spec_interrupt2])
    apply auto
  apply(rule sync)
  done


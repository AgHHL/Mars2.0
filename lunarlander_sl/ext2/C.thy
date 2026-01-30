theory C
  imports BigStepContParallel
begin



locale C =
  fixes Stop_point :: real    \<comment> \<open>64000\<close>
  fixes V_limit :: real       \<comment> \<open>100\<close>
  fixes Next_V_limit :: real  \<comment> \<open>40\<close>
  fixes Period :: real        \<comment> \<open>0.125\<close>
  fixes A_minus :: real       \<comment> \<open>1\<close>
  fixes A_plus :: real        \<comment> \<open>1\<close>
  assumes Period[simp]: "Period > 0"
  assumes V_limit: "V_limit > 0"
  assumes A_minus: "A_minus > 0"
  assumes A_plus: "A_plus > 0"
begin

definition "Pull_curve_max_d = V_limit * V_limit / (2 * A_minus)"
definition "Pull_curve_coeff = sqrt (2 * A_minus)"

lemma Pull_curve_coeff_ge_zero [simp]:
  "Pull_curve_coeff > 0"
  unfolding Pull_curve_coeff_def using A_minus by auto

lemma Pull_curve_max_d_ge_zero [simp]:
  "Pull_curve_max_d > 0"
  unfolding Pull_curve_max_d_def using V_limit A_minus by auto

text \<open>Variables\<close>

definition A :: char where "A = CHR ''a''"
definition V :: char where "V = CHR ''b''"
definition S :: char where "S = CHR ''c''"
definition T :: char where "T = CHR ''k''"
definition Ca :: char where "Ca = CHR ''o''"

definition M :: pname where "M = ''m''"
definition N :: pname where "N = ''n''"




lemma train_vars_distinct [simp]: "A \<noteq> V" "A \<noteq> S" "A \<noteq> T" 
                                  "V \<noteq> A" "V \<noteq> S" "V \<noteq> T" 
                                  "S \<noteq> A" "S \<noteq> V" "S \<noteq> T"
                                  "T \<noteq> A" "T \<noteq> V" "T \<noteq> S"
  unfolding A_def V_def S_def T_def by auto

definition Plant :: "'a proc" where
  "Plant =
      Rep (
      Interrupt 
      (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),
                      V := (\<lambda>s. s A))))(\<lambda> s. True)
      [(''P2C''[!](\<lambda>s. (rpart s) V),
            Cm (''P2C''[!](\<lambda>s. (rpart s) S));
            Cm (''C2P''[?]A))] Skip)"


lemma plant_ode:
  assumes "spec_of c1 Q1" "spec_of c2 Q2"
  shows
  "spec_of (Interrupt (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),V := (\<lambda>s. s A)))) (\<lambda>_. True) [(''P2C''[!](\<lambda>s. (rpart s) V), c2)] c1)
           (wait_out_c (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * t)) S (val s0 S + val s0 V * t + val s0 A * t * t /2))
               ''P2C'' (\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = val s0 V + val s0 A * d)] 
                            \<and>\<^sub>a Q2 {{V := (\<lambda>s. val s V + val s A * d)}} {{S := (\<lambda>s. val s S + val s V * d + val s A * d * d/2)}}))"
proof -
  have 1: "paramODEsolInf (ODE ((\<lambda>_ _. 0)(S := (\<lambda>s. s V),V := (\<lambda>s. s A))))
                          (\<lambda>s0 t. (rpart s0)(V := val s0 V + val s0 A * t,S := val s0 S + val s0 V * t + val s0 A * t * t /2))"
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
      subgoal
      apply (rule has_vector_derivative_eq_rhs)
       apply (fast intro!: derivative_intros)[1]
        by simp
      subgoal
      apply (rule has_vector_derivative_eq_rhs)
         apply (fast intro!: derivative_intros)[1]
        apply (cases s)
        by (simp add: rpart.simps val.simps)
      done
    done
  have 2: "local_lipschitz {- 1<..} UNIV (\<lambda>(t::real) v. ODE2Vec (ODE ((\<lambda>_ _. 0)(S := \<lambda>s. s V, V := \<lambda>s. s A))) (vec2state v))"
  proof -
    have bl:"bounded_linear (\<lambda>(v::vec) . \<chi> x. if x = V then (v$A) else if x = S then (v$V) else 0)"
      apply (rule bounded_linearI')
      using vec_lambda_unique by fastforce+
    show ?thesis
      unfolding state2vec_def vec2state_def fun_upd_def
      apply (rule c1_implies_local_lipschitz[where f'="(\<lambda>(t,v). Blinfun(\<lambda>(v::vec) . \<chi> x. if x = V then (v$A) else if x = S then (v$V) else 0))"])
         apply (auto simp add: bounded_linear_Blinfun_apply[OF bl])
      subgoal premises pre for t x
        unfolding has_derivative_def apply (auto simp add: bl)
        apply (rule vec_tendstoI)
        by (auto simp add: state2vec_def)
        done
  qed
  let ?specs = "[OutSpec ''P2C'' (\<lambda>s. (rpart s) V) Q2]"
  show ?thesis
    apply (rule spec_of_post)
     apply (rule spec_of_interrupt_inf_unique[where specs="?specs"])
        apply (rule 1) apply (rule 2)
      apply (auto intro!: rel_list.intros) apply (rule spec_of_es.intros)
      apply (rule assms) apply (rule assms)
    apply (subst interrupt_solInf_c_out)
    subgoal for s0
      apply (simp only: updr_rpart_simp2)
      apply (rule wait_out_c_mono)
      apply (cases s0)
      apply (auto simp add: substr_assn2_def subst_assn2_def updr.simps rpart.simps val.simps upd.simps pure_assn_def conj_assn_def)
      by (simp add: entails_triv fun_upd_twist)
    done
qed


fun plant_rep :: "nat \<Rightarrow> 'a assn2" where
  "plant_rep 0 = init"
| "plant_rep (Suc n) =
   (wait_out_c (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * t)) S (val s0 S + val s0 V * t + val s0 A * t * t / 2)) ''P2C''
    (\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = val s0 V + val s0 A * d)] \<and>\<^sub>a
           (wait_out_cv single_id_inv ''P2C'' (\<lambda>s. rpart s S)
                  (\<lambda>d. wait_in_c single_id_inv ''C2P'' (\<lambda>d v. plant_rep n {{A := (\<lambda>_. v)}}))) 
           {{V := (\<lambda>s. val s V + val s A * d)}} {{S := (\<lambda>s. val s S + val s V * d + val s A * d * d / 2)}}))"


lemma plant_spec':"spec_of Plant (\<exists>\<^sub>an. plant_rep n)"
  unfolding Plant_def 
  apply (rule spec_of_rep)
  subgoal for n
    apply (induction n)
     apply simp apply (rule spec_of_skip)
    subgoal premises pre for n
      apply (simp only: RepN.simps)
      apply (subst spec_of_interrupt_distrib)
      apply simp
      apply(rule plant_ode)
       apply (subst spec_of_skip_left)
       apply(rule pre)
      apply (subst spec_of_seq_assoc)
      apply(rule Valid_send_sp)
      apply(rule Valid_receive_sp)
      apply(rule pre)
      done
    done
  done

fun plant_rep' :: "nat \<Rightarrow> 'a assn2" where
  "plant_rep' 0 = init"
| "plant_rep' (Suc n) =
   (wait_out_c (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * t)) S (val s0 S + val s0 V * t + val s0 A * t * t / 2)) ''P2C''
    (\<lambda>d v. !\<^sub>a[(\<lambda>s0. v = val s0 V + val s0 A * d)] \<and>\<^sub>a
           (wait_out_cv (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * d)) S (val s0 S + val s0 V * d + val s0 A * d * d / 2)) 
                              ''P2C'' (\<lambda>s. val s S + val s V * d + val s A * d * d / 2)
                  (\<lambda>_. wait_in_c (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * d)) S (val s0 S + val s0 V * d + val s0 A * d * d / 2)) 
                          ''C2P'' (\<lambda>_ v. plant_rep' n {{A := (\<lambda>_. v)}}{{V := (\<lambda>s. val s V + val s A * d)}} {{S := (\<lambda>s. val s S + val s V * d + val s A * d * d / 2)}})))))"

lemma plant_entails:
  "plant_rep n s0 \<Longrightarrow>\<^sub>A plant_rep' n s0"
proof (induction n arbitrary: s0)
  case 0
  then show ?case
    by (auto intro: entails_triv)
next
  case (Suc n)
  show ?case
    apply simp
    apply (rule wait_out_c_mono)
    apply (rule conj_pure_mono)
    apply (rule entails_trans)
     apply (rule upd_mono)
     apply (rule wait_out_cv_upd)
    apply auto
    apply (rule entails_trans)
     apply (rule wait_out_cv_upd)
    apply (auto simp add:upd_upd_simp')
    apply (rule wait_out_cv_mono)
    apply (rule entails_trans)
     apply (rule upd_mono)
     apply (rule wait_in_c_upd)
    apply (rule entails_trans)
     apply (rule wait_in_c_upd)
    apply (auto simp add:upd_upd_simp')
    apply (rule wait_in_c_mono)
    apply (rule upd_mono)+
    by(rule Suc)
qed

lemma plant_spec:"spec_of Plant (\<exists>\<^sub>an. plant_rep' n)"
apply (rule spec_of_post)
   apply (rule plant_spec') apply clarify
  apply (rule exists_assn_mono)
  by (rule plant_entails)



definition fs :: "real \<Rightarrow> real" where
   "fs s =
      (let D = Stop_point - s in
        if D \<ge> Pull_curve_max_d then
          V_limit
        else if D \<ge> 0 then
          Pull_curve_coeff * sqrt(D)
        else 0)"

definition com_a :: "real \<Rightarrow> real \<Rightarrow> real" where
  "com_a s v =
      (let s1' = s + v * Period + A_plus * Period\<^sup>2 / 2 in
       let target_v1 = fs s1' in
         if v + A_plus * Period \<le> target_v1 then
           A_plus
         else let s2' = s + v * Period in
              let target_v2 = fs s2' in
                if v \<le> target_v2 then 0
                else -A_minus)"
lemma control_vars_distinct [simp]: "Ca \<noteq> V" "Ca \<noteq> S" 
                                  "V \<noteq> Ca" "V \<noteq> S" 
                                  "S \<noteq> Ca" "S \<noteq> V" 
 unfolding Ca_def V_def S_def by auto

definition Control :: "'a proc" where
  "Control =
    Rep(
      Wait (\<lambda> s. Period);
      Cm (''P2C''[?]V);
      Cm (''P2C''[?]S);
      Ca ::= (\<lambda>s. com_a ((rpart s) S) ((rpart s) V));
      Cm (''C2P''[!](\<lambda>s. (rpart s) Ca)))"

fun control_rep :: "nat \<Rightarrow> 'a assn2" where
  "control_rep 0 = init"
| "control_rep (Suc n) = wait_c single_id_inv (\<lambda> s. Period) 
                   (\<lambda>_. wait_in_c single_id_inv ''P2C''
                      (\<lambda>d v1. wait_in_c single_id_inv ''P2C''
                        (\<lambda>d v2. wait_out_cv single_id_inv ''C2P'' (\<lambda>s. rpart s Ca)
                          (\<lambda>d. control_rep n) {{Ca := (\<lambda>s. com_a (rpart s S) (rpart s V))}} {{S := (\<lambda>_. v2)}}) {{V := (\<lambda>_. v1)}}))"


lemma control_spec':"spec_of Control (\<exists>\<^sub>an. control_rep n)"
  unfolding Control_def 
  apply (rule spec_of_rep)
  subgoal for n
    apply (induction n)
     apply simp apply (rule spec_of_skip)
    subgoal premises pre for n
      apply (simp only: RepN.simps control_rep.simps)
      apply (subst spec_of_seq_assoc)
      apply(rule Valid_wait_sp)
      apply (subst spec_of_seq_assoc)
      apply(rule Valid_receive_sp)
      apply (subst spec_of_seq_assoc)
      apply(rule Valid_receive_sp)
      apply (subst spec_of_seq_assoc)
      apply(rule Valid_assign_sp) 
      apply(rule Valid_send_sp)
      apply(rule pre)
      done
    done
  done


fun control_rep' :: "nat \<Rightarrow> 'a assn2" where
  "control_rep' 0 = init"
| "control_rep' (Suc n) = wait_c single_id_inv (\<lambda> s. Period) 
                   (\<lambda>_. wait_in_c single_id_inv ''P2C''
                      (\<lambda>d v1. wait_in_c (\<lambda>s0 t s. s = upd s0 V v1) ''P2C''
                        (\<lambda>d v2. wait_out_cv (\<lambda>s0 t s. s = upd (upd (upd s0 V v1) S v2) Ca (com_a v2 v1))''C2P'' (\<lambda>s. com_a v2 v1)
                          (\<lambda>d. control_rep' n {{Ca := (\<lambda>s. com_a (rpart s S) (rpart s V))}} {{S := (\<lambda>_. v2)}}{{V := (\<lambda>_. v1)}}))))"


lemma control_entails:
  "control_rep n s0 \<Longrightarrow>\<^sub>A control_rep' n s0"
proof (induction n arbitrary: s0)
  case 0
  then show ?case
    by (auto intro: entails_triv)
next
  case (Suc n)
  show ?case
    apply simp
    apply (rule wait_c_mono)
    apply (rule wait_in_c_mono)
    apply (rule entails_trans)
     apply (rule upd_mono)
     apply (rule wait_in_c_mono)
     apply auto
     apply (rule upd_mono)
    apply(rule wait_out_cv_upd)
    apply (rule entails_trans)
     apply(rule wait_in_c_upd)
    apply (rule wait_in_c_mono)
    apply (rule entails_trans)
    apply (rule upd_mono)
     apply(rule wait_out_cv_upd)
    apply (rule entails_trans)
     apply(rule wait_out_cv_upd)
    apply simp
    apply(rule wait_out_cv_mono)
    apply (rule upd_mono)+
    by(rule Suc)
qed

lemma control_spec:"spec_of Control (\<exists>\<^sub>an. control_rep' n)"
apply (rule spec_of_post)
   apply (rule control_spec') apply clarify
  apply (rule exists_assn_mono)
  by (rule control_entails)


lemma gg:
  "sync_gassn {''P2C'', ''C2P''} {M} {N}
    (single_assn M (plant_rep' (Suc n1)))
    (single_assn N (control_rep' (Suc n2))) s0 \<Longrightarrow>\<^sub>G 
              wait_cg (merge_inv
               (single_inv M (\<lambda>s0 t s. s = upd (upd s0 V (val s0 V + val s0 A * t)) 
                                 S (val s0 S + val s0 V * t + val s0 A * t * t / 2)))
               (id_inv {N})) N (\<lambda>s. Period)  
               (\<lambda>d. sync_gassn {''P2C'', ''C2P''} {M} {N} (single_assn M (plant_rep' n1)) (single_assn N(control_rep' n2)) 
                    {{Ca := (\<lambda>a. com_a (rpart a S)(rpart a V))}}\<^sub>g at N
                    {{S := (\<lambda>a. val (the (s0 M)) S + val (the (s0 M)) V * d + val (the (s0 M)) A * d * d /2)}}\<^sub>g at N
                    {{V := (\<lambda>a. val (the (s0 M)) V + val (the (s0 M)) A * d)}}\<^sub>g at N
                    {{A := (\<lambda>a. com_a (val (the (s0 M)) S + val (the (s0 M)) V * d + val (the (s0 M)) A * d * d / 2) (val (the (s0 M)) V + val (the (s0 M)) A * d))}}\<^sub>g at M 
                    {{V := (\<lambda>a. val a V + val a A * d)}}\<^sub>g at M 
                    {{S := (\<lambda>s. val s S + val s V * d + val s A * d * d / 2)}}\<^sub>g at M) s0"
  apply (auto simp add: single_assn_simps)
  apply (rule entails_g_trans)
   apply(rule sync_gassn_out_wait_pair)
     apply(auto simp add:M_def N_def)
  apply (rule wait_cg_mono)
  apply (rule entails_g_trans)
   apply (rule sync_gassn_out_in)
    apply auto[2]
  subgoal for d
  apply (rule entails_g_trans)
    apply(rule exists_gassn_elim)
  apply(rule sync_gassn_conj_pure_left')
  apply (rule entails_g_trans)
   apply (rule sync_gassn_outv_in')
  apply auto
  apply (rule entails_g_trans)
   apply (rule sync_gassn_in_outv')
     apply auto
  apply (rule entails_g_trans)
   apply (rule sync_gassn_subst_left) apply auto
  apply (rule entails_g_trans)
   apply (rule updg_mono)
   apply (rule sync_gassn_subst_left) apply auto
  apply (rule entails_g_trans)
   apply (rule updg_mono)+
   apply (rule sync_gassn_subst_left) apply auto
  apply (rule entails_g_trans)
   apply (rule updg_mono)+
   apply (rule sync_gassn_subst_right) apply auto
  apply (rule entails_g_trans)
   apply (rule updg_mono)+
   apply (rule sync_gassn_subst_right) apply auto
  apply (rule entails_g_trans)
   apply (rule updg_mono)+
      apply (rule sync_gassn_subst_right) apply auto
    apply(rule entails_g_triv)
    apply(rule entails_g_triv)
    done
  done


lemma full_spec:
  "spec_of_global
    (Parallel (Single M Plant)
              {''P2C'', ''C2P''}
              (Single N Control))
    (\<exists>\<^sub>gn1 n2. sync_gassn {''P2C'', ''C2P''} {M} {N}
                (single_assn M (plant_rep' n1))
                (single_assn N (control_rep' n2)))"
  apply (rule spec_of_global_post)
   apply (rule spec_of_parallel)
      apply (rule spec_of_single[OF plant_spec])
     apply (rule spec_of_single[OF control_spec])
    apply auto   
  apply (auto simp add: single_assn_exists sync_gassn_exists_left)
  apply (auto simp add: sync_gassn_exists_right)
  by (rule entails_g_triv)





fun loop_invariant :: "real \<times> real \<Rightarrow> bool" where
  "loop_invariant (s, v) \<longleftrightarrow> v \<le> fs s \<and> s \<le> Stop_point"

definition loop_invariant_a :: "real \<Rightarrow> real \<Rightarrow> real => bool" where
  "loop_invariant_a s v a = (loop_invariant (s, v) \<and> a = com_a s v)"

lemma fs_at_least_zero:
  "fs s \<ge> 0"
  unfolding fs_def Let_def apply auto
  using V_limit apply auto
  using  Pull_curve_coeff_ge_zero
  by (simp add: dual_order.strict_implies_order)

lemma fs_at_most_limit:
  "fs s \<le> V_limit"
  unfolding fs_def Let_def
  apply auto
  subgoal premises pre
  proof-
    have "Stop_point - s < V_limit * V_limit / (2 * A_minus)"
        using pre unfolding Pull_curve_max_d_def Pull_curve_coeff_def by auto
      then have 31: "(Stop_point - s) * (2 * A_minus) < V_limit * V_limit"
        using A_minus
        by (metis lattice_ab_group_add_class.zero_less_double_add_iff_zero_less_single_add mult_2 pos_less_divide_eq)
      have 32: "sqrt (2 * A_minus) * sqrt (Stop_point - s) = sqrt ((Stop_point - s) * (2 * A_minus))"
        using A_minus pre by (simp add: real_sqrt_mult)
      have 33: "V_limit = sqrt (V_limit * V_limit)"
        using V_limit by auto
      show ?thesis 
        unfolding Pull_curve_max_d_def Pull_curve_coeff_def 32
        apply (subst 33) using 31 
        using real_sqrt_less_iff 
        using less_eq_real_def by blast
    qed
    subgoal using V_limit by auto
    done


lemma fs_prop1:
  assumes "v \<le> fs(s)"
    and "v \<ge> 0"
    and "s \<le> Stop_point"
  shows "v^2 \<le> 2 * A_minus * (Stop_point - s)"
proof-
  have 1: "v^2 \<le> 2 * A_minus * (Stop_point - s)" if "Stop_point - s \<ge> Pull_curve_max_d"
  proof-
    have 11: "v\<le>V_limit"
      using assms(1) that unfolding fs_def Let_def by auto
    then have 12: "v^2\<le>V_limit^2"
      using assms(2) V_limit by simp
    have 13:" V_limit^2 \<le>2 * A_minus * (Stop_point - s)" 
      using that A_minus unfolding Pull_curve_max_d_def
      by (auto simp add: power2_eq_square field_simps)
    then show ?thesis using 12 by auto
  qed
  have 2:"v^2 \<le> 2 * A_minus * (Stop_point - s)" if "Stop_point - s < Pull_curve_max_d"
  proof-
    have 21:"v \<le> Pull_curve_coeff * sqrt(Stop_point - s)"
      using assms that unfolding fs_def by auto
    then show ?thesis using assms A_minus unfolding Pull_curve_coeff_def 
      by (metis power2_eq_square real_sqrt_le_iff real_sqrt_mult real_sqrt_pow2)
  qed
  show ?thesis using 1 2 assms 
    by linarith
qed


fun loop_once :: "real \<times> real \<Rightarrow> real \<times> real" where
  "loop_once (s, v) = 
    (let a = com_a s v in
     let v' = v + a * Period in
     let s' = s + v * Period + a * Period * Period / 2 in
      (s', v'))"


declare loop_once.simps[simp del]


lemma loop_once_invariant:
  assumes "v \<le> fs s \<and> s \<le> Stop_point"
    and "(s', v') = loop_once (s, v)"
  shows "v' \<le> fs s' \<and> s' \<le> Stop_point"
proof -
  have case1:"v' \<le> fs s' \<and> s' \<le> Stop_point" if cond1:"v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)"
  proof-
    have 1:"com_a s v = A_plus" 
      using that unfolding com_a_def by auto
    have 2:"(s', v') = (s + v * Period + A_plus * Period\<^sup>2 / 2,v + A_plus * Period )" 
      using assms 1  that loop_once.simps by (auto simp add: power2_eq_square)
    have 3:"v' \<le> fs s'" 
      using that 2
      unfolding fs_def Let_def by auto
    have 4:"s' \<le> Stop_point" 
    proof (cases "v' > 0")
      case True
      then show ?thesis 
        using 3 2 that apply(simp add: fs_def Let_def) apply auto 
        by (smt Pull_curve_max_d_ge_zero)
    next
      case False
      then show ?thesis 
      proof-
        have "v + A_plus * Period \<le> 0"
          using False 2 by auto
        then have "(v + A_plus * Period)*Period \<le> 0"
          by (meson Period eucl_less_le_not_le mult_le_0_iff)
        then have "v * Period + A_plus * Period\<^sup>2 \<le>0"
          by(auto simp add:power2_eq_square algebra_simps)
        then have "v * Period + A_plus * Period\<^sup>2 - A_plus * Period*Period/2 \<le>0"
          apply(subgoal_tac "A_plus * Period*Period/2 > 0")
           prefer 2 using A_plus apply simp
          by linarith
        then have "v * Period + A_plus * Period\<^sup>2/2 \<le>0"
          by(auto simp add: power2_eq_square)
        then have "s + v * Period + A_plus * Period\<^sup>2/2 \<le> Stop_point"
          using assms by auto
        then show ?thesis using 2 apply auto done
      qed
    qed
     show ?thesis using 3 4 by auto
  qed
  have case2:"v' \<le> fs s' \<and>  s' \<le> Stop_point" if cond2:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)" 
    "v \<le> fs (s + v * Period)" 
  proof-
    have 1: "com_a s v = 0" using that unfolding com_a_def by auto
    have 2: "(s',v') = (s + v * Period, v)" using assms 1 loop_once.simps by auto
    have 3:"v' \<le> fs s'" 
      using 2 that
      unfolding fs_def Let_def by auto
    have 4:"s' \<le> Stop_point" 
    proof-
      have "v \<le> 0" if "s' > Stop_point"
        using 2 3 unfolding fs_def Let_def 
        using Pull_curve_max_d_ge_zero assms(1) that by auto
      then have"s\<ge>s'" if "s' > Stop_point" using 2 that
        by (smt Period old.prod.inject zero_less_mult_pos2)
      then show ?thesis using assms 
        using leI 2   by auto
    qed
    then show ?thesis using 3 4  by auto
  qed
  have case3:"v' \<le> fs s'  \<and> s' \<le> Stop_point" if cond3:
    "\<not> v + A_plus * Period \<le> fs (s + v * Period + A_plus * Period\<^sup>2 / 2)"
    "\<not> v \<le> fs (s + v * Period)" 
  proof-
    have 1: "com_a s v = -A_minus" using that unfolding com_a_def by auto
    have 2:"(s',v') = (s + v * Period - A_minus * Period\<^sup>2 / 2, v - A_minus  * Period)"
        using assms 1  cond3 loop_once.simps by (auto simp add: power2_eq_square)
    have 31:"s' \<le> Stop_point" if "v\<ge>0"
        using 2 apply auto
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
              using fs_prop1 assms that by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le> 
                      2 * A_minus * (Stop_point - s) - 2 * A_minus * v * Period + A_minus^2 * Period^2"
            by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le>
                      2 * A_minus * (Stop_point - s - v * Period + 1/2 * A_minus * Period^2)"
            by (auto simp add: algebra_simps power2_eq_square)
          then have "(v - A_minus * Period)^2 \<le> 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))"
            by (auto simp add: algebra_simps power2_eq_square)
          then have " 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)) \<ge> 0"
            by (smt zero_le_power2)
          then have "(Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)) \<ge> 0"
            by (metis A_minus less_eq_real_def linordered_ab_group_add_class.double_add_le_zero_iff_single_add_le_zero mult_less_cancel_right not_one_le_zero not_real_square_gt_zero one_add_one zero_le_mult_iff zero_less_mult_iff)
          then show ?thesis by auto
            qed
            done
          have 32:"s' \<le> Stop_point" if "v<0"
            using 2 apply auto
            apply (subgoal_tac"s \<le> Stop_point")
             prefer 2 using assms apply auto
            apply (subgoal_tac"v * Period \<le> 0")
            prefer 2 using that Period 
             apply (smt cond3(2) fs_at_least_zero)
            apply (subgoal_tac" A_minus * Period\<^sup>2 / 2 \<ge> 0")
             prefer 2
            subgoal
              using A_minus by(auto simp add:power2_eq_square)
            by linarith
       have 41:"v' \<le> fs s'" if "v\<ge>0"
        using 2
        unfolding fs_def Let_def apply auto
        subgoal using assms(1) fs_at_most_limit A_minus Period 
          by (smt mult_diff_mult mult_less_iff1)
        subgoal premises pre
        proof-
          have "v^2 \<le> 2 * A_minus * (Stop_point - s)"
            using fs_prop1 assms that by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le> 
                      2 * A_minus * (Stop_point - s) - 2 * A_minus * v * Period + A_minus^2 * Period^2"
            by auto
          then have "v^2 - 2 * A_minus * v * Period + A_minus^2 * Period^2 \<le>
                      2 * A_minus * (Stop_point - s - v * Period + 1/2 * A_minus * Period^2)"
            by (auto simp add: algebra_simps power2_eq_square)
          then have "(v - A_minus * Period)^2 \<le> 2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))"
            by (auto simp add: algebra_simps power2_eq_square)
          then have a:"sqrt((v - A_minus * Period)^2) \<le> sqrt(2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)))"
            using real_sqrt_le_iff by blast
          have b:"(v - A_minus * Period) <= sqrt((v - A_minus * Period)^2)" 
            by auto
          have c:"sqrt(2 * A_minus * (Stop_point - (s + v * Period - 1/2 * A_minus * Period^2))) = sqrt(2 * A_minus) * sqrt((Stop_point - (s + v * Period - 1/2 * A_minus * Period^2)))"
            by (simp add: real_sqrt_mult)
          show ?thesis using a b c unfolding Pull_curve_coeff_def by auto
        qed
        subgoal using assms fs_at_most_limit A_minus Period 
          using Pull_curve_max_d_ge_zero by linarith
        subgoal using 31 that by auto
        done
      have 42:"v' \<le> fs s'" if "v<0"
        using 2
        unfolding fs_def Let_def apply auto
        subgoal using assms(1) fs_at_most_limit A_minus Period 
          by (smt mult_diff_mult mult_less_iff1)
        subgoal 
          apply(subgoal_tac "s + v * Period - A_minus * Period\<^sup>2 / 2  \<le> s")
           prefer 2 subgoal
           apply (subgoal_tac"s \<le> Stop_point")
             prefer 2 using assms apply auto
            apply (subgoal_tac"v * Period \<le> 0")
            prefer 2 using that Period 
             apply (smt cond3(2) fs_at_least_zero)
            apply (subgoal_tac" A_minus * Period\<^sup>2 / 2 \<ge> 0")
             prefer 2
            subgoal
              using A_minus by(auto simp add:power2_eq_square)
            apply linarith
            done
            apply(subgoal_tac" \<not> Pull_curve_max_d \<le> Stop_point - s")
             prefer 2
             apply simp
            apply(subgoal_tac"v \<le> Pull_curve_coeff * sqrt (Stop_point - s)")
            prefer 2
            subgoal using assms unfolding fs_def Let_def by auto
            apply(subgoal_tac"v - A_minus * Period \<le> v")
            prefer 2 subgoal using A_minus 
              by (smt cond3(2) fs_at_least_zero that)
            apply(subgoal_tac"Pull_curve_coeff * sqrt (Stop_point - s)\<le>Pull_curve_coeff * sqrt (Stop_point - (s + v * Period - A_minus * Period\<^sup>2 / 2))")
             apply linarith
            by simp
          subgoal using assms fs_at_most_limit A_minus Period 
            using Pull_curve_max_d_ge_zero by linarith
          subgoal using that A_minus 
            using "32" by auto
          done
       show ?thesis using 31 32 41 42 
         using leI by blast
    qed
  show ?thesis
    using case1 case2 case3
    by linarith
qed



lemma loop_once_invariant':
  assumes "loop_invariant (s,v)"
    and "(s', v') = loop_once (s, v)"
  shows "loop_invariant (s',v')"
  using loop_once_invariant assms
  using loop_invariant.simps by blast

lemma loop_once_invariant_a:
  assumes "loop_invariant_a s v a"
    and "s' = s + v * Period + a * Period * Period / 2"
    and "v' = v + a * Period"
    and "a' = com_a s' v'"
  shows "loop_invariant_a s' v' a'"
  apply(subgoal_tac"(s', v') = loop_once (s, v)")
  subgoal
    using assms unfolding loop_invariant_a_def
    using loop_once_invariant'[of s v s' v']
    by auto
  apply(auto simp add: loop_once.simps)
  using assms apply auto
  by (metis loop_invariant_a_def)

lemma updg_assn2_prop:
  assumes "P (updg s0 pn var (e (the (s0 pn)))) s tr \<Longrightarrow> Q"
  shows  "(P {{var := e}}\<^sub>g at pn) s0 s tr \<Longrightarrow> Q"
  using assms unfolding updg_assn2_def by auto

lemma entails_g_prop:
  assumes "P \<Longrightarrow>\<^sub>G Q"
  shows "P s tr \<Longrightarrow> Q s tr"
  using assms unfolding entails_g_def by auto

lemma sync_prop:
  assumes "loop_invariant_a (val (the (s0 M)) S) (val (the (s0 M)) V) (val (the (s0 M)) A)"
  shows "sync_gassn {''P2C'', ''C2P''} {M} {N}
    (single_assn M (plant_rep' n1))
    (single_assn N (control_rep' n2)) s0 
    \<Longrightarrow>\<^sub>G (\<lambda> s tr. loop_invariant_a (val (the (s M)) S) (val (the (s M)) V) (val (the (s M)) A))"
  using assms
proof (induction n1 n2 arbitrary: s0 rule: diff_induct)
  case (1 x)
  show ?case 
  proof (cases x)
    case 0
    then show ?thesis 
      apply (auto simp add: single_assn_simps)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_emp) apply auto
      unfolding entails_g_def
      apply clarify
      apply(elim init_single.cases)
      using 1 by auto
  next
    case (Suc nat)
    then show ?thesis 
      apply (auto simp add: single_assn_simps)
      apply (rule sync_gassn_out_emp_unpair)
      by auto
  qed
next
  case (2 y)
  then show ?case 
    apply (auto simp add: single_assn_simps)
    apply(rule sync_gassn_emp_wait)
    unfolding M_def N_def by auto
next
  case (3 x y)
  show ?case 
    apply (rule entails_g_trans)
     apply(rule gg)
    unfolding entails_g_def
    apply clarify
    apply(elim wait_cg.cases)
    subgoal for s tr e gs0 pn d P gs tra I p rdy
      apply auto
      apply(rule updg_assn2_prop[of _ _ M S])
       prefer 2
       apply simp
      apply(rule updg_assn2_prop[of _ _ M V])
       prefer 2
      apply simp
      apply(rule updg_assn2_prop[of _ _ M A])
       prefer 2
       apply simp
      apply(rule updg_assn2_prop[of _ _ N V])
       prefer 2
       apply simp
      apply(rule updg_assn2_prop[of _ _ N S])
       prefer 2
       apply simp
      apply(rule updg_assn2_prop[of _ _ N Ca])
       prefer 2
       apply simp
      apply(rule entails_g_prop[of "sync_gassn {''P2C'', ''C2P''} {M} {N} (single_assn M (plant_rep' x)) (single_assn N (control_rep' y))
     (updg
       (updg
         (updg
           (updg
             (updg (updg gs0 M S (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)) M
               V (val (the (updg gs0 M S
                             (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2) M))
                   V +
                  val (the (updg gs0 M S
                             (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2) M))
                   A *
                  Period))
             M A
             (com_a (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
               (val (the (gs0 M)) V + val (the (gs0 M)) A * Period)))
           N V (val (the (gs0 M)) V + val (the (gs0 M)) A * Period))
         N S (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2))
       N Ca
       (com_a
         (rpart
           (the (updg
                  (updg
                    (updg
                      (updg
                        (updg gs0 M S
                          (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2))
                        M V
                        (val (the (updg gs0 M S
                                    (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                                    M))
                          V +
                         val (the (updg gs0 M S
                                    (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                                    M))
                          A *
                         Period))
                      M A
                      (com_a (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                        (val (the (gs0 M)) V + val (the (gs0 M)) A * Period)))
                    N V (val (the (gs0 M)) V + val (the (gs0 M)) A * Period))
                  N S (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2) N))
           S)
         (rpart
           (the (updg
                  (updg
                    (updg
                      (updg
                        (updg gs0 M S
                          (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2))
                        M V
                        (val (the (updg gs0 M S
                                    (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                                    M))
                          V +
                         val (the (updg gs0 M S
                                    (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                                    M))
                          A *
                         Period))
                      M A
                      (com_a (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2)
                        (val (the (gs0 M)) V + val (the (gs0 M)) A * Period)))
                    N V (val (the (gs0 M)) V + val (the (gs0 M)) A * Period))
                  N S (val (the (gs0 M)) S + val (the (gs0 M)) V * Period + val (the (gs0 M)) A * Period * Period / 2) N))
           V)))" _ gs tra])
       prefer 2
       apply simp
      apply(rule 3(1))
      apply (auto simp add:M_def N_def)
      using 3(2)
      using loop_once_invariant_a[of "(val (the (s0 M)) S)" "(val (the (s0 M)) V)" "(val (the (s0 M)) A)"]
      by (auto simp add:M_def N_def)
    subgoal for s tr e gs0 pn P gs tra I
      by auto
    done
qed

thm full_spec

lemma full_spec':
  "spec_of_global_gen (\<lambda> s. loop_invariant_a (val (the (s M)) S) (val (the (s M)) V) (val (the (s M)) A))
    (Parallel (Single M Plant)
              {''P2C'', ''C2P''}
              (Single N Control))
    (\<lambda>s0 s tr. loop_invariant_a (val (the (s M)) S) (val (the (s M)) V) (val (the (s M)) A))"
  unfolding spec_of_global_gen_def apply auto
  apply (rule weaken_post_global)
   apply (rule spec_of_globalE[OF full_spec]) apply simp
  apply (rule exists_gassn_elim)
  apply (rule exists_gassn_elim)
  apply (rule sync_prop)
  by auto

end
end
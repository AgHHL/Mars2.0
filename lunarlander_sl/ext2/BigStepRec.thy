theory BigStepRec
  imports BigStepParallel
begin


thm lfp_unfold

definition entails2 :: "'a assn2 \<Rightarrow> 'a assn2 \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>a" 30) where
  "(P \<Longrightarrow>\<^sub>a Q) \<longleftrightarrow> (\<forall>s0 s tr. P s0 s tr \<longrightarrow> Q s0 s tr)"

lemma assn2_order_self[simp]:"x \<Longrightarrow>\<^sub>a x "
  unfolding entails2_def 
  by auto 

lemma assn2_order_tran[simp]:"x \<Longrightarrow>\<^sub>a y \<Longrightarrow> y \<Longrightarrow>\<^sub>a z \<Longrightarrow> x \<Longrightarrow>\<^sub>a z"
  unfolding entails2_def 
  by auto 

lemma assn2_order_eq[simp]:"x \<Longrightarrow>\<^sub>a y \<Longrightarrow> y \<Longrightarrow>\<^sub>a x \<Longrightarrow> x = y"
  unfolding entails2_def 
  apply(rule)+
  by auto      

definition assn2_inf :: "'a assn2 set \<Rightarrow> 'a assn2" where 
"(assn2_inf P) s0 s tr = (\<forall> p \<in> P . p s0 s tr)"

lemma assn2_inf_1: "p \<in> P \<Longrightarrow> (assn2_inf P) \<Longrightarrow>\<^sub>a p"
  unfolding assn2_inf_def entails2_def
  by auto

lemma assn2_inf_2: " (\<And> p. p \<in> P \<Longrightarrow> q \<Longrightarrow>\<^sub>a p) \<Longrightarrow> q \<Longrightarrow>\<^sub>a (assn2_inf P)"
  unfolding assn2_inf_def entails2_def
  by auto

definition assn2_mono :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> bool" where 
"(assn2_mono f) = (\<forall> p q. p \<Longrightarrow>\<^sub>a q \<longrightarrow> f p \<Longrightarrow>\<^sub>a f q)"

lemma assn2_mono_prop:"assn2_mono f \<Longrightarrow> p \<Longrightarrow>\<^sub>a q \<Longrightarrow> f p \<Longrightarrow>\<^sub>a f q"
  unfolding assn2_mono_def
  by auto

lemma entails_to_entails2:
  assumes "\<And> s0. p s0 \<Longrightarrow>\<^sub>A q s0"
  shows "p \<Longrightarrow>\<^sub>a q"
  using assms
  unfolding entails_def entails2_def
  by auto

lemma entails2_to_entails:
  assumes "p \<Longrightarrow>\<^sub>a q"
  shows "p s0 \<Longrightarrow>\<^sub>A q s0" 
  using assms
  unfolding entails_def entails2_def
  by auto

lemma entails2_left_disj:
  assumes "p1 \<Longrightarrow>\<^sub>a q" and "p2 \<Longrightarrow>\<^sub>a q"
  shows "p1 \<or>\<^sub>a p2 \<Longrightarrow>\<^sub>a q" 
  using assms
  unfolding entails2_def disj_assn_def
  by auto

lemma entails2_right_disj1:
  assumes "p \<Longrightarrow>\<^sub>a q1"
  shows "p \<Longrightarrow>\<^sub>a q1 \<or>\<^sub>a q2" 
  using assms
  unfolding entails2_def disj_assn_def
  by auto

lemma entails2_right_disj2:
  assumes "p \<Longrightarrow>\<^sub>a q2"
  shows "p \<Longrightarrow>\<^sub>a q1 \<or>\<^sub>a q2" 
  using assms
  unfolding entails2_def disj_assn_def
  by auto

lemma entails2_exists:
  assumes "\<exists>n. P  \<Longrightarrow>\<^sub>a Q n "
  shows "P \<Longrightarrow>\<^sub>a (\<exists>\<^sub>an. Q n)"
  using assms unfolding exists_assn_def entails2_def by auto

lemma entails2_exists':
  assumes "\<forall> n. P n \<Longrightarrow>\<^sub>a Q"
  shows "(\<exists>\<^sub>an. P n) \<Longrightarrow>\<^sub>a Q"
  using assms unfolding exists_assn_def entails2_def by auto
      
definition assn2_lfp :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2"
  where "assn2_lfp f = assn2_inf {u. f u \<Longrightarrow>\<^sub>a u}"

lemma assn2_lfp_lowerbound: "f H \<Longrightarrow>\<^sub>a H \<Longrightarrow> assn2_lfp f \<Longrightarrow>\<^sub>a H"
  unfolding assn2_lfp_def by (rule assn2_inf_1) simp

lemma assn2_lfp_greatest: "(\<And>u. f u \<Longrightarrow>\<^sub>a u \<Longrightarrow> H \<Longrightarrow>\<^sub>a u) \<Longrightarrow> H \<Longrightarrow>\<^sub>a assn2_lfp f"
  unfolding assn2_lfp_def by (rule assn2_inf_2) simp

lemma assn2_lfp_fixpoint:
  assumes "assn2_mono f"     
  shows "f (assn2_lfp f) = assn2_lfp f"
  unfolding assn2_lfp_def
proof (rule assn2_order_eq)
  let ?H = "{u. f u \<Longrightarrow>\<^sub>a u}"
  let ?a = "assn2_inf ?H"
  show "f ?a \<Longrightarrow>\<^sub>a ?a"
  proof (rule assn2_inf_2)
    fix x
    assume "x \<in> ?H"
    then have "?a \<Longrightarrow>\<^sub>a x" by (rule assn2_inf_1)
    with \<open>assn2_mono f\<close> have 1:"f ?a \<Longrightarrow>\<^sub>a f x" unfolding assn2_mono_def by auto
    also from \<open>x \<in> ?H\<close> have 2:"f x \<Longrightarrow>\<^sub>a x" unfolding assn2_mono_def by auto
    show "f ?a \<Longrightarrow>\<^sub>a x" using 1 2 assn2_order_tran by auto
  qed
  show "?a \<Longrightarrow>\<^sub>a f ?a"
  proof (rule assn2_inf_1)
    from \<open>assn2_mono f\<close> and \<open>f ?a \<Longrightarrow>\<^sub>a ?a\<close> have "f (f ?a) \<Longrightarrow>\<^sub>a f ?a" unfolding assn2_mono_def by auto
    then show "f ?a \<in> ?H" by auto
  qed
qed

lemma assn2_lfp_unfold: "assn2_mono f \<Longrightarrow> assn2_lfp f = f (assn2_lfp f)"
  by (rule assn2_lfp_fixpoint [symmetric])


fun rep_f :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> nat \<Rightarrow> 'a assn2" where
  "rep_f f 0 = init"
| "rep_f f (Suc n) = f (rep_f f n)"

fun rec_f :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> ('a assn2 \<Rightarrow> 'a assn2)" where
  "rec_f f p = (init \<or>\<^sub>a (f p))"

fun rep_fp :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2 \<Rightarrow> nat \<Rightarrow> 'a assn2" where
  "rep_fp f p 0 = p"
| "rep_fp f p (Suc n) = f (rep_fp f p n)"

fun rec_fp :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> 'a assn2 \<Rightarrow> ('a assn2 \<Rightarrow> 'a assn2)" where
  "rec_fp f p q = (p \<or>\<^sub>a (f q))"

lemma assn2_mono_rec:
  assumes "assn2_mono f"
  shows "assn2_mono (rec_f f)"
  unfolding assn2_mono_def
  apply auto
  apply(rule entails2_left_disj)
     apply(rule entails2_right_disj1)
     apply simp
  apply(rule entails2_right_disj2)
  using assms
  unfolding assn2_mono_def
  by auto

lemma assn2_mono_recp:
  assumes "assn2_mono f"
  shows "assn2_mono (rec_fp f p)"
  unfolding assn2_mono_def
  apply auto
  apply(rule entails2_left_disj)
     apply(rule entails2_right_disj1)
     apply simp
  apply(rule entails2_right_disj2)
  using assms
  unfolding assn2_mono_def
  by auto

lemma spec_of_rep':
  assumes "\<And> c Q. spec_of c Q \<Longrightarrow> spec_of (b;c) (f Q)"
  shows "spec_of (Rep b) (\<exists>\<^sub>an. rep_f f n)"
  apply(rule spec_of_rep)
  subgoal for n
    apply (induction n)
    subgoal
      apply auto
      apply(rule spec_of_skip)
      done
    apply auto
    subgoal for n
      using assms[of "RepN n b" "rep_f f n"]
      by auto
    done
  done

lemma entails_exists_left:
  assumes "\<And>x. P x  \<Longrightarrow>\<^sub>a Q"
  shows "(\<exists>\<^sub>ax. P x) \<Longrightarrow>\<^sub>a Q"
  using assms unfolding entails2_def exists_assn_def by blast

lemma rep_to_rec:
  assumes "assn2_mono f"
  shows "(\<exists>\<^sub>an. rep_f f n) \<Longrightarrow>\<^sub>a  assn2_lfp (rec_f f)"
  apply(rule entails_exists_left)
  subgoal for n
    apply (induction n)
    subgoal apply (subst assn2_lfp_unfold)
      subgoal apply(rule assn2_mono_rec) using assms by auto
      apply auto
      apply(rule entails2_right_disj1)
      by auto
    subgoal premises pre for n
      apply (subst assn2_lfp_unfold)
      subgoal apply(rule assn2_mono_rec) using assms by auto
      apply auto
      apply(rule entails2_right_disj2)
      apply(rule assn2_mono_prop[of f])
      subgoal using assms by auto
      using pre by blast
    done
  done

lemma repp_to_recp:
  assumes "assn2_mono f"
  shows "(\<exists>\<^sub>an. rep_fp f p n) \<Longrightarrow>\<^sub>a  assn2_lfp (rec_fp f p)"
  apply(rule entails_exists_left)
  subgoal for n
    apply (induction n)
    subgoal apply (subst assn2_lfp_unfold)
      subgoal apply(rule assn2_mono_recp) using assms by auto
      apply auto
      apply(rule entails2_right_disj1)
      by auto
    subgoal premises pre for n
      apply (subst assn2_lfp_unfold)
      subgoal apply(rule assn2_mono_recp) using assms by auto
      apply auto
      apply(rule entails2_right_disj2)
      apply(rule assn2_mono_prop[of f])
      subgoal using assms by auto
      using pre by blast
    done
  done

definition fun_exists :: "('a assn2 \<Rightarrow> 'a assn2) \<Rightarrow> bool" where
  "fun_exists f = (\<forall> Q . f (\<exists>\<^sub>an. Q (n::nat)) = (\<exists>\<^sub>an. f (Q n)))"

lemma fun_exists_prop:
  "fun_exists f \<Longrightarrow> (f (\<exists>\<^sub>an. Q (n::nat)) = (\<exists>\<^sub>an. f (Q n)))"
  unfolding fun_exists_def
  by auto


thm wait_in_c_exists


lemma rec_to_rep:
  assumes "fun_exists f"
  shows "assn2_lfp (rec_f f) \<Longrightarrow>\<^sub>a (\<exists>\<^sub>an. rep_f f n)"
  apply(rule assn2_lfp_lowerbound)
  apply simp
  apply(rule entails2_left_disj)
  subgoal 
    apply(rule entails2_exists)
    apply(rule exI[where x=0])
    by auto
  using assms
  apply(simp add:fun_exists_prop)
  unfolding exists_assn_def entails2_def
  apply auto
  subgoal for s0 s tr n
    apply(rule exI[where x="Suc n"])
    by auto
  done

lemma recp_to_repp:
  assumes "fun_exists f"
  shows "assn2_lfp (rec_fp f p) \<Longrightarrow>\<^sub>a (\<exists>\<^sub>an. rep_fp f p n)"
  apply(rule assn2_lfp_lowerbound)
  apply simp
  apply(rule entails2_left_disj)
  subgoal 
    apply(rule entails2_exists)
    apply(rule exI[where x=0])
    by auto
  using assms
  apply(simp add:fun_exists_prop)
  unfolding exists_assn_def entails2_def
  apply auto
  subgoal for s0 s tr n
    apply(rule exI[where x="Suc n"])
    by auto
  done

lemma rec_eq_rep:
  assumes "assn2_mono f"
    and "fun_exists f"
  shows "assn2_lfp (rec_f f) = (\<exists>\<^sub>an. rep_f f n)"
  apply(rule assn2_order_eq)
  using rec_to_rep rep_to_rec assms by auto

lemma rep_eq_rec:
  assumes "assn2_mono f"
    and "fun_exists f"
  shows "(\<exists>\<^sub>an. rep_f f n) = assn2_lfp (rec_f f)"
  apply(rule rec_eq_rep[symmetric])
  using assms by auto

lemma spec_of_rep'':
  assumes "\<And> c Q. spec_of c Q \<Longrightarrow> spec_of (b;c) (f Q)"
   and  "assn2_mono f"
 shows "spec_of (Rep b) (assn2_lfp (rec_f f))"  
  apply(rule spec_of_post)
   apply(rule spec_of_rep'[where f=f])
   apply auto
  subgoal using assms by auto
  using rep_to_rec[of f] assms unfolding entails_def entails2_def
  by auto


lemma rep_subst:
  assumes "\<And> p. g (f p) = f' (g p)" 
    and "fun_exists g"
    and "assn2_mono f'"
  shows "g (\<exists>\<^sub>an. rep_fp f i n) \<Longrightarrow>\<^sub>a (\<exists>\<^sub>an. rep_fp f' (g i) n)"
  apply (subst fun_exists_prop)
  using assms(2)
   apply simp
  apply(rule entails2_exists')
  apply auto
  subgoal for n
    apply(rule entails2_exists)
    apply(rule exI[where x=n])
    apply(induction n)
     apply auto
    using assms
    apply auto
    unfolding assn2_mono_def
    by auto
  done
  
    
  

lemma rep_loop_once:
  assumes "assn2_mono f"
    and "fun_exists f"
  shows "(\<exists>\<^sub>an. rep_f f n) = (init \<or>\<^sub>a f (\<exists>\<^sub>an. rep_f f n))"
  apply(subst fun_exists_prop[where f=f])
  unfolding exists_assn_def disj_assn_def
  apply(auto simp add: assms)
  apply(rule ext)+
  apply auto
  subgoal for s0 s tr n
    apply(cases n)
    subgoal by auto
    subgoal by auto
    done
  subgoal apply(rule exI[where x=0]) by auto
  subgoal for s0 s tr n
    apply(rule exI[where x="Suc n"]) 
    by auto
  done


lemma rec_loop_once:
  assumes "assn2_mono f"
    and "fun_exists f"
  shows "(assn2_lfp (rec_f f)) = (init \<or>\<^sub>a f (assn2_lfp (rec_f f)))"
  using assms rep_loop_once rec_eq_rep
  by metis

lemma false_disj_gassn:
  "(P \<or>\<^sub>g false_gassn) s0 \<Longrightarrow>\<^sub>G P s0"
  unfolding entails_g_def disj_gassn_def false_gassn_def by auto

lemma false_disj_gassn':
  "(false_gassn \<or>\<^sub>g P) s0 \<Longrightarrow>\<^sub>G P s0"
  unfolding entails_g_def disj_gassn_def false_gassn_def by auto

lemma entails_g_triv':
  "P s0 \<Longrightarrow>\<^sub>G P s0"
  unfolding entails_g_def by auto


lemma tt:
  assumes "\<And> pn p. single_assn pn (f1 p) = F1 (single_assn pn p)"
     and "\<And> pn p. single_assn pn (f2 p) = F2 (single_assn pn p)"
      and "assn2_mono f1"
      and "fun_exists f1"
      and "assn2_mono f2"
      and "fun_exists f2"
      and "\<And> p s0. sync_gassn chs {pn1} {pn2} (init_single {pn1}) (F2 p) s0 \<Longrightarrow>\<^sub>G false_gassn s0"
      and "\<And> p s0. sync_gassn chs {pn1} {pn2} (F1 p) (init_single {pn2}) s0 \<Longrightarrow>\<^sub>G false_gassn s0"
      and "\<And> p1 p2 s0. sync_gassn chs {pn1} {pn2} (F1 p1) (F2 p2) s0 \<Longrightarrow>\<^sub>G F (sync_gassn chs {pn1} {pn2} p1 p2) s0"
    shows "sync_gassn chs {pn1} {pn2} (single_assn pn1 (assn2_lfp (rec_f f1))) (single_assn pn2 (assn2_lfp (rec_f f2))) s0 \<Longrightarrow>\<^sub>G 
             (init_single {pn1, pn2} \<or>\<^sub>g F (sync_gassn chs {pn1} {pn2} (single_assn pn1 (assn2_lfp (rec_f f1)))
         (single_assn pn2 (assn2_lfp (rec_f f2))))) s0 "
  apply(subst rec_loop_once[of f1])
    apply(auto simp add: assms)
  apply(subst single_assn_disj)
  apply(rule sync_gassn_disj2_s)
    apply(subst rec_loop_once[of f2])
      apply(auto simp add: assms)
    apply(subst single_assn_disj)
    apply (rule entails_g_trans)
    apply(rule sync_gassn_disj2'_s)
      apply(subst single_assn_init)+
      apply(rule sync_gassn_emp[of "{pn1,pn2}"])
    subgoal by auto
     apply(subst single_assn_init)
       apply(subst assms(2))
       apply(rule assms(7))
      apply(subst false_disj_gassn)
    subgoal by auto
     apply(subst rec_loop_once[of f2])
       apply(auto simp add: assms)
     apply(subst single_assn_disj)
     apply (rule entails_g_trans)
      apply(rule sync_gassn_disj2'_s)
       apply(subst single_assn_init)
       apply(rule assms(8))
      apply(subst assms(2))
      apply(subst assms(9))
     subgoal by auto
     apply(rule false_disj_gassn')
     done
    

    
definition entails_g2 :: "'a gassn2 \<Rightarrow> 'a gassn2 \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>g" 30) where
  "(P \<Longrightarrow>\<^sub>g Q) \<longleftrightarrow> (\<forall>s0 s tr. P s0 s tr \<longrightarrow> Q s0 s tr)"

lemma gassn2_order_self[simp]:"x \<Longrightarrow>\<^sub>g x "
  unfolding entails_g2_def 
  by auto 

lemma gassn2_order_tran[simp]:"x \<Longrightarrow>\<^sub>g y \<Longrightarrow> y \<Longrightarrow>\<^sub>g z \<Longrightarrow> x \<Longrightarrow>\<^sub>g z"
  unfolding entails_g2_def 
  by auto 

lemma gassn2_order_eq[simp]:"x \<Longrightarrow>\<^sub>g y \<Longrightarrow> y \<Longrightarrow>\<^sub>g x \<Longrightarrow> x = y"
  unfolding entails_g2_def 
  apply(rule)+
  by auto      

definition gassn2_inf :: "'a gassn2 set \<Rightarrow> 'a gassn2" where 
"(gassn2_inf P) s0 s tr = (\<forall> p \<in> P . p s0 s tr)"

lemma gassn2_inf_1: "p \<in> P \<Longrightarrow> (gassn2_inf P) \<Longrightarrow>\<^sub>g p"
  unfolding gassn2_inf_def entails_g2_def
  by auto

lemma gassn2_inf_2: " (\<And> p. p \<in> P \<Longrightarrow> q \<Longrightarrow>\<^sub>g p) \<Longrightarrow> q \<Longrightarrow>\<^sub>g (gassn2_inf P)"
  unfolding gassn2_inf_def entails_g2_def
  by auto

definition gassn2_mono :: "('a gassn2 \<Rightarrow> 'a gassn2) \<Rightarrow> bool" where 
"(gassn2_mono f) = (\<forall> p q. p \<Longrightarrow>\<^sub>g q \<longrightarrow> f p \<Longrightarrow>\<^sub>g f q)"

lemma gassn2_mono_prop:"gassn2_mono f \<Longrightarrow> p \<Longrightarrow>\<^sub>g q \<Longrightarrow> f p \<Longrightarrow>\<^sub>g f q"
  unfolding gassn2_mono_def
  by auto

lemma entailsg_to_entailsg2:
  assumes "\<And> s0. p s0 \<Longrightarrow>\<^sub>G q s0"
  shows "p \<Longrightarrow>\<^sub>g q"
  using assms
  unfolding entails_g_def entails_g2_def
  by auto

lemma entailsg2_to_entailsg:
  assumes "p \<Longrightarrow>\<^sub>g q"
  shows "p s0 \<Longrightarrow>\<^sub>G q s0" 
  using assms
  unfolding entails_g_def entails_g2_def
  by auto

lemma entailsg2_left_disj:
  assumes "p1 \<Longrightarrow>\<^sub>g q" and "p2 \<Longrightarrow>\<^sub>g q"
  shows "p1 \<or>\<^sub>g p2 \<Longrightarrow>\<^sub>g q" 
  using assms
  unfolding entails_g2_def disj_gassn_def
  by auto

lemma entailsg2_right_disj1:
  assumes "p \<Longrightarrow>\<^sub>g q1"
  shows "p \<Longrightarrow>\<^sub>g q1 \<or>\<^sub>g q2" 
  using assms
  unfolding entails_g2_def disj_gassn_def
  by auto

lemma entailsg2_right_disj2:
  assumes "p \<Longrightarrow>\<^sub>g q2"
  shows "p \<Longrightarrow>\<^sub>g q1 \<or>\<^sub>g q2" 
  using assms
  unfolding entails_g2_def disj_gassn_def
  by auto

lemma entailsg2_exists:
  assumes "\<exists>n. P  \<Longrightarrow>\<^sub>g Q n "
  shows "P \<Longrightarrow>\<^sub>g (\<exists>\<^sub>gn. Q n)"
  using assms unfolding exists_gassn_def entails_g2_def by auto

lemma entailsg2_false:
  assumes "P  \<Longrightarrow>\<^sub>g false_gassn "
  shows "P = false_gassn"
  apply (rule ext)+
  using assms unfolding false_gassn_def entails_g2_def 
  by auto

lemma entailsg2_false':
  assumes "P = false_gassn "
  shows "P \<Longrightarrow>\<^sub>g false_gassn"
  unfolding exists_gassn_def
  using assms unfolding false_gassn_def entails_g2_def 
  by auto

definition gassn2_lfp :: "('a gassn2 \<Rightarrow> 'a gassn2) \<Rightarrow> 'a gassn2"
  where "gassn2_lfp f = gassn2_inf {u. f u \<Longrightarrow>\<^sub>g u}"

lemma gassn2_lfp_lowerbound: "f H \<Longrightarrow>\<^sub>g H \<Longrightarrow> gassn2_lfp f \<Longrightarrow>\<^sub>g H"
  unfolding gassn2_lfp_def by (rule gassn2_inf_1) simp

lemma gassn2_lfp_greatest: "(\<And>u. f u \<Longrightarrow>\<^sub>g u \<Longrightarrow> H \<Longrightarrow>\<^sub>g u) \<Longrightarrow> H \<Longrightarrow>\<^sub>g gassn2_lfp f"
  unfolding gassn2_lfp_def by (rule gassn2_inf_2) simp

lemma gassn2_lfp_fixpoint:
  assumes "gassn2_mono f"
  shows "f (gassn2_lfp f) = gassn2_lfp f"
  unfolding gassn2_lfp_def
proof (rule gassn2_order_eq)
  let ?H = "{u. f u \<Longrightarrow>\<^sub>g u}"
  let ?a = "gassn2_inf ?H"
  show "f ?a \<Longrightarrow>\<^sub>g ?a"
  proof (rule gassn2_inf_2)
    fix x
    assume "x \<in> ?H"
    then have "?a \<Longrightarrow>\<^sub>g x" by (rule gassn2_inf_1)
    with \<open>gassn2_mono f\<close> have 1:"f ?a \<Longrightarrow>\<^sub>g f x" unfolding gassn2_mono_def by auto
    also from \<open>x \<in> ?H\<close> have 2:"f x \<Longrightarrow>\<^sub>g x" unfolding gassn2_mono_def by auto
    show "f ?a \<Longrightarrow>\<^sub>g x" using 1 2 gassn2_order_tran by auto
  qed
  show "?a \<Longrightarrow>\<^sub>g f ?a"
  proof (rule gassn2_inf_1)
    from \<open>gassn2_mono f\<close> and \<open>f ?a \<Longrightarrow>\<^sub>g ?a\<close> have "f (f ?a) \<Longrightarrow>\<^sub>g f ?a" unfolding gassn2_mono_def by auto
    then show "f ?a \<in> ?H" by auto
  qed
qed

lemma gassn2_lfp_unfold: "gassn2_mono f \<Longrightarrow> gassn2_lfp f = f (gassn2_lfp f)"
  by (rule gassn2_lfp_fixpoint [symmetric])


fun grep_f :: "pname set \<Rightarrow> ('a gassn2 \<Rightarrow> 'a gassn2) \<Rightarrow> nat \<Rightarrow> 'a gassn2" where
  "grep_f pn f 0 = init_single pn"
| "grep_f pn f (Suc n) = f (grep_f pn f n)"

fun grec_f :: "pname set \<Rightarrow> ('a gassn2 \<Rightarrow> 'a gassn2) \<Rightarrow> ('a gassn2 \<Rightarrow> 'a gassn2)" where
  "grec_f pn f p = (init_single pn \<or>\<^sub>g (f p))"

lemma gassn2_mono_rec:
  assumes "gassn2_mono f"
  shows "gassn2_mono (grec_f pn f)"
  unfolding gassn2_mono_def
  apply auto
  apply(rule entailsg2_left_disj)
     apply(rule entailsg2_right_disj1)
     apply simp
  apply(rule entailsg2_right_disj2)
  using assms
  unfolding gassn2_mono_def
  by auto

lemma entailsg_exists_left:
  assumes "\<And>x. P x  \<Longrightarrow>\<^sub>g Q"
  shows "(\<exists>\<^sub>gx. P x) \<Longrightarrow>\<^sub>g Q"
  using assms unfolding entails_g2_def exists_gassn_def by blast

lemma grep_to_grec:
  assumes "gassn2_mono f"
  shows "(\<exists>\<^sub>gn. grep_f pn f n) \<Longrightarrow>\<^sub>g gassn2_lfp (grec_f pn f)"
  apply(rule entailsg_exists_left)
  subgoal for n
    apply (induction n)
    subgoal apply (subst gassn2_lfp_unfold)
      subgoal apply(rule gassn2_mono_rec) using assms by auto
      apply auto
      apply(rule entailsg2_right_disj1)
      by auto
    subgoal premises pre for n
      apply (subst gassn2_lfp_unfold)
      subgoal apply(rule gassn2_mono_rec) using assms by auto
      apply auto
      apply(rule entailsg2_right_disj2)
      apply(rule gassn2_mono_prop[of f])
      subgoal using assms by auto
      using pre by blast
    done
  done

definition gfun_exists :: "('a gassn2 \<Rightarrow> 'a gassn2) \<Rightarrow> bool" where
  "gfun_exists f = (\<forall> Q . f (\<exists>\<^sub>gn. Q (n::nat)) = (\<exists>\<^sub>gn. f (Q n)))"

lemma gfun_exists_prop:
  "gfun_exists f \<Longrightarrow> (f (\<exists>\<^sub>gn. Q (n::nat)) = (\<exists>\<^sub>gn. f (Q n)))"
  unfolding gfun_exists_def
  by auto


lemma grec_to_grep:
  assumes "gfun_exists f"
  shows "gassn2_lfp (grec_f pn f) \<Longrightarrow>\<^sub>g (\<exists>\<^sub>gn. grep_f pn f n)"
  apply(rule gassn2_lfp_lowerbound)
  apply simp
  apply(rule entailsg2_left_disj)
  subgoal 
    apply(rule entailsg2_exists)
    apply(rule exI[where x=0])
    by auto
  using assms
  apply(simp add:gfun_exists_prop)
  unfolding exists_gassn_def entails_g2_def
  apply auto
  subgoal for s0 s tr n
    apply(rule exI[where x="Suc n"])
    by auto
  done

lemma grec_eq_grep:
  assumes "gassn2_mono f"
    and "gfun_exists f"
  shows "gassn2_lfp (grec_f pn f) = (\<exists>\<^sub>gn. grep_f pn f n)"
  apply(rule gassn2_order_eq)
  using grec_to_grep grep_to_grec assms by auto

lemma grep_eq_grec:
  assumes "gassn2_mono f"
    and "gfun_exists f"
  shows "(\<exists>\<^sub>gn. grep_f pn f n) = gassn2_lfp (grec_f pn f)"
  apply(rule grec_eq_grep[symmetric])
  using assms by auto

lemma rep_to_grep':
  assumes "\<And> p. single_assn pn (f p) = F (single_assn pn p)"
  shows "(grep_f {pn} F n) = single_assn pn (rep_f f n)"
   proof(induction n)
     case 0
     then show ?case 
       by(simp add:single_assn_simps)
   next
     case (Suc n)
     then show ?case 
       apply simp
       using assms by auto
   qed

lemma rep_to_grep:
  assumes "\<And> p. single_assn pn (f p) = F (single_assn pn p)"
  shows "(\<exists>\<^sub>gn. grep_f {pn} F n) = single_assn pn (\<exists>\<^sub>an. rep_f f n)"
  apply(subst single_assn_exists)
  unfolding exists_gassn_def
  apply(rule ext)+
  apply auto
  subgoal for s0 s tr n
    apply(rule exI[where x=n])
    using rep_to_grep' assms 
    by metis
  subgoal for s0 s tr n
    apply(rule exI[where x=n])
    using rep_to_grep' assms 
    by metis
  done

lemma sync_rep_rep1:
  assumes "\<And> p. sync_gassn chs pn1 pn2 (F1 p) (init_single pn2) \<Longrightarrow>\<^sub>g false_gassn "
      and "\<And> p1 p2. sync_gassn chs pn1 pn2 (F1 p1) (F2 p2) \<Longrightarrow>\<^sub>g F (sync_gassn chs pn1 pn2 p1 p2)"
      and "F false_gassn \<Longrightarrow>\<^sub>g false_gassn"
      and "n1 > n2"
    shows "sync_gassn chs pn1 pn2 (grep_f pn1 F1 n1) (grep_f pn2 F2 n2) = false_gassn "
  using assms(4)
      proof(induction n1 arbitrary: n2)
        case 0
        then show ?case 
          using assms by auto
      next
        case (Suc n1)
        then show ?case 
          apply(cases n2)
          subgoal 
            apply simp 
            apply(rule entailsg2_false)
            apply(rule assms(1))
            done
          subgoal for n2'
            apply auto
            apply(rule entailsg2_false)
            apply(rule gassn2_order_tran)
             apply(rule assms(2))
            apply auto
            using assms by auto
          done
      qed

lemma sync_rep_rep2:
  assumes "\<And> p. sync_gassn chs pn1 pn2 (init_single pn1) (F2 p) \<Longrightarrow>\<^sub>g false_gassn "
      and "\<And> p1 p2. sync_gassn chs pn1 pn2 (F1 p1) (F2 p2) \<Longrightarrow>\<^sub>g F (sync_gassn chs pn1 pn2 p1 p2)"
      and "F false_gassn \<Longrightarrow>\<^sub>g false_gassn"
      and "n1 < n2"
    shows "sync_gassn chs pn1 pn2 (grep_f pn1 F1 n1) (grep_f pn2 F2 n2) = false_gassn "
  using assms(4)
      proof(induction n2 arbitrary: n1)
        case 0
        then show ?case 
          using assms by auto
      next
        case (Suc n2)
        then show ?case 
          apply(cases n1)
          subgoal 
            apply simp 
            apply(rule entailsg2_false)
            apply(rule assms(1))
            done
          subgoal for n1'
            apply auto
            apply(rule entailsg2_false)
            apply(rule gassn2_order_tran)
             apply(rule assms(2))
            apply auto
            using assms by auto
          done
      qed

lemma sync_rep_rep3:
  assumes "\<And> p1 p2. sync_gassn chs pn1 pn2 (F1 p1) (F2 p2) \<Longrightarrow>\<^sub>g F (sync_gassn chs pn1 pn2 p1 p2)"
      and "gassn2_mono F"
    shows "sync_gassn chs pn1 pn2 (grep_f pn1 F1 n) (grep_f pn2 F2 n) \<Longrightarrow>\<^sub>g grep_f (pn1 \<union> pn2) F n"
  proof(induction n)
    case 0
    then show ?case 
      apply auto
      apply (rule entailsg_to_entailsg2)
      apply (rule entails_g_trans)
       apply (rule sync_gassn_emp)
       prefer 2
       apply (rule entails_g_triv')
      by auto
  next
    case (Suc n)
    then show ?case 
      apply auto
      apply (rule gassn2_order_tran)
       apply(rule assms(1))
      apply(rule gassn2_mono_prop[of F])
      using assms by auto
  qed

lemma sync_rep_rep:
  assumes "\<And> p. sync_gassn chs pn1 pn2 (init_single pn1) (F2 p) \<Longrightarrow>\<^sub>g false_gassn "
      and "\<And> p. sync_gassn chs pn1 pn2 (F1 p) (init_single pn2) \<Longrightarrow>\<^sub>g false_gassn "
      and "\<And> p1 p2. sync_gassn chs pn1 pn2 (F1 p1) (F2 p2) \<Longrightarrow>\<^sub>g F (sync_gassn chs pn1 pn2 p1 p2)"
      and "F false_gassn = false_gassn"
      and "gassn2_mono F"
    shows "sync_gassn chs pn1 pn2 (\<exists>\<^sub>gn. grep_f pn1 F1 n) (\<exists>\<^sub>gn. grep_f pn2 F2 n) \<Longrightarrow>\<^sub>g (\<exists>\<^sub>gn. grep_f (pn1\<union>pn2) F n) "
  apply(subst sync_gassn_exists_left)
  apply(subst sync_gassn_exists_right)
  unfolding exists_gassn_def entails_g2_def
  apply auto
  subgoal for s0 s tr n1 n2
    apply(cases "n1<n2")
    subgoal 
      using sync_rep_rep2[of chs pn1 pn2 F2 F1 F n1 n2] assms 
      apply auto
      unfolding false_gassn_def by auto
    apply(cases "n1>n2")
    subgoal 
      using sync_rep_rep1[of chs pn1 pn2 F1 F2 F n2 n1] assms 
      apply auto
      unfolding false_gassn_def by auto
    apply auto
    apply(rule exI[where x=n1])
    apply auto
    apply(rule entails_g_elim)
     prefer 2
    apply(rule entailsg2_to_entailsg)
    apply(rule sync_rep_rep3[of chs pn1 pn2 F1 F2 F n2])
    using assms by auto
  done

        
  


     

end

theory BigStepProp
  imports BigStepRec BigStepInterruptParallel3
begin



definition pp :: "('a estate \<Rightarrow> bool) \<Rightarrow> 'a assn" ("![_]" [71] 70) where
  "(![b]) = (\<lambda>s tr. b s)"

lemma post_init:
  assumes "\<forall> s. P s \<longrightarrow> Q s"
  shows "P s0 \<Longrightarrow> init s0 \<Longrightarrow>\<^sub>A ![Q]"
  unfolding init_def pp_def entails_def
  using assms
  by auto


lemma post_wait:
  assumes "P s0 \<and> e s0 > 0\<Longrightarrow> R (e s0) s0 \<Longrightarrow>\<^sub>A ![Q]"
   and "P s0 \<and> e s0 \<le> 0 \<Longrightarrow> R 0 s0 \<Longrightarrow>\<^sub>A ![Q]"
 shows "P s0 \<Longrightarrow> wait_c I e R s0 \<Longrightarrow>\<^sub>A ![Q]"
  using assms
  unfolding entails_def pp_def
  apply auto
  apply(elim wait_c.cases)
  by auto

lemma post_subst:
  assumes "\<And> s0.  (\<lambda> s. \<exists> s'. P s' \<and> s = (upd s' var (e s'))) s0 \<Longrightarrow> R s0 \<Longrightarrow>\<^sub>A ![Q]"
  shows "P s0 \<Longrightarrow> (R {{var := e}}) s0 \<Longrightarrow>\<^sub>A ![Q]"
  using assms
  unfolding subst_assn2_def entails_def pp_def
  by auto

lemma post_or:
 assumes "P s0 \<Longrightarrow> R1 s0 \<Longrightarrow>\<^sub>A ![Q]"
   and "P s0 \<Longrightarrow> R2 s0 \<Longrightarrow>\<^sub>A ![Q]"
 shows "P s0 \<Longrightarrow> (R1 \<or>\<^sub>a R2) s0 \<Longrightarrow>\<^sub>A ![Q]"
  using assms
  unfolding entails_def pp_def disj_assn_def
  by auto


lemma post_pure:
 assumes "P s0 \<and> b s0 \<Longrightarrow> R s0 \<Longrightarrow>\<^sub>A ![Q]"
 shows "P s0 \<Longrightarrow> (!\<^sub>a[b] \<and>\<^sub>a R) s0 \<Longrightarrow>\<^sub>A ![Q]"
  using assms
  unfolding entails_def pp_def conj_assn_def pure_assn_def
  by auto



lemma post_rep:
  assumes "\<forall> s. P s \<longrightarrow> Q s"
    and "\<forall> s. Q s \<longrightarrow> G s"
    and "\<And> n s0. (\<forall> s0. Q s0 \<longrightarrow> rep_f f n s0 \<Longrightarrow>\<^sub>A ![Q]) \<Longrightarrow> Q s0 \<Longrightarrow> f(rep_f f n) s0 \<Longrightarrow>\<^sub>A ![Q]"
  shows "P s0 \<Longrightarrow> (\<exists>\<^sub>an. rep_f f n) s0 \<Longrightarrow>\<^sub>A ![G]"
  apply (rule entails_trans[of _ "![Q]"])
   prefer 2
  subgoal unfolding exists_assn_def entails_def pp_def 
    using assms by auto
  unfolding entails_def exists_assn_def pp_def
  apply auto
  subgoal premises pre for s tr n
  proof-
    have 1:"Q s0 \<Longrightarrow> rep_f f n s0 \<Longrightarrow>\<^sub>A ![Q]" for n
    proof(induction n arbitrary:s0)
      case 0
      then show ?case 
        apply simp
        unfolding init_def entails_def pp_def by auto
    next
      case (Suc n)
      show ?case 
        apply simp
        apply (rule assms(3))
        apply auto
         apply(rule Suc)
        apply auto
        apply(rule Suc)
        done
    qed
    have 2:"P s0 \<Longrightarrow> rep_f f n s0 s tr \<Longrightarrow> Q s" for n s tr
      using 1[of n] assms(1,2)
      unfolding entails_def pp_def by auto
    show ?thesis
      using 2 pre by auto
  qed
  done

lemma post_rep':
  assumes "\<forall> s. P s \<longrightarrow> Q s"
    and "\<forall> s. Q s \<longrightarrow> G s"
    and "\<And> R s0. (\<forall> s0 . Q s0 \<longrightarrow> R s0 \<Longrightarrow>\<^sub>A ![Q]) \<Longrightarrow> Q s0 \<Longrightarrow> f(R) s0 \<Longrightarrow>\<^sub>A ![Q]"
  shows "P s0 \<Longrightarrow> (\<exists>\<^sub>an. rep_f f n) s0 \<Longrightarrow>\<^sub>A ![G]"
  apply (rule entails_trans[of _ "![Q]"])
   prefer 2
  subgoal unfolding exists_assn_def entails_def pp_def 
    using assms by auto
  unfolding entails_def exists_assn_def pp_def
  apply auto
  subgoal premises pre for s tr n
  proof-
    have 1:"Q s0 \<Longrightarrow> rep_f f n s0 \<Longrightarrow>\<^sub>A ![Q]" for n
    proof(induction n arbitrary:s0)
      case 0
      then show ?case 
        apply simp
        unfolding init_def entails_def pp_def by auto
    next
      case (Suc n)
      show ?case 
        apply simp
        apply (rule assms(3))
        apply auto
         apply(rule Suc)
        apply auto
        apply(rule Suc)
        done
    qed
    have 2:"P s0 \<Longrightarrow> rep_f f n s0 s tr \<Longrightarrow> Q s" for n s tr
      using 1[of n] assms(1,2)
      unfolding entails_def pp_def by auto
    show ?thesis
      using 2 pre by auto
  qed
  done
                                                
inductive trInv :: "('a estate \<Rightarrow> bool) \<Rightarrow> 'a trace \<Rightarrow> bool" where
  "trInv b []"
| "trInv b tr \<Longrightarrow> trInv b ((InBlock ch v)#tr)"
| "trInv b tr \<Longrightarrow> trInv b ((OutBlock ch v)#tr)"
| "trInv b tr \<Longrightarrow> \<forall> \<tau>\<in>{0..d}. b (p \<tau>) \<Longrightarrow> trInv b ((WaitBlk d p rdy)#tr)"


definition trpp :: "('a estate \<Rightarrow> bool) \<Rightarrow> 'a assn" ("?![_]" [71] 70) where
  "(?![b]) = (\<lambda>s tr. trInv b tr)"

lemma post_tr_init:
  "init s0 \<Longrightarrow>\<^sub>A ?![b]"
  unfolding init_def entails_def trpp_def
  apply auto
  apply(rule trInv.intros(1))
  done

lemma post_tr_wait:
  assumes "P s0 \<and> e s0 > 0\<Longrightarrow> R (e s0) s0 \<Longrightarrow>\<^sub>A ?![Q]"
   and "P s0 \<and> e s0 > 0 \<Longrightarrow> \<forall> t \<in> {0..e s0}.(\<forall> s.  I s0 t s \<longrightarrow> Q s)"
   and "P s0 \<and> e s0 \<le> 0 \<Longrightarrow> R 0 s0 \<Longrightarrow>\<^sub>A ?![Q]"
 shows "P s0 \<Longrightarrow> wait_c I e R s0 \<Longrightarrow>\<^sub>A ?![Q]"
  using assms
  unfolding entails_def trpp_def 
  apply auto
  apply(elim wait_c.cases)
   apply auto
  apply(rule trInv.intros(4))
   by auto
  
lemma post_tr_subst:
  assumes "\<And> s0.  (\<lambda> s. \<exists> s'. P s' \<and> s = (upd s' var (e s'))) s0 \<Longrightarrow> R s0 \<Longrightarrow>\<^sub>A ?![Q]"
  shows "P s0 \<Longrightarrow> (R {{var := e}}) s0 \<Longrightarrow>\<^sub>A ?![Q]"
  using assms
  unfolding subst_assn2_def entails_def pp_def
  by auto

lemma post_tr_or:
 assumes "P s0 \<Longrightarrow> R1 s0 \<Longrightarrow>\<^sub>A ?![Q]"
   and "P s0 \<Longrightarrow> R2 s0 \<Longrightarrow>\<^sub>A ?![Q]"
 shows "P s0 \<Longrightarrow> (R1 \<or>\<^sub>a R2) s0 \<Longrightarrow>\<^sub>A ?![Q]"
  using assms
  unfolding entails_def pp_def disj_assn_def
  by auto


lemma post_tr_pure:
 assumes "P s0 \<and> b s0 \<Longrightarrow> R s0 \<Longrightarrow>\<^sub>A ?![Q]"
 shows "P s0 \<Longrightarrow> (!\<^sub>a[b] \<and>\<^sub>a R) s0 \<Longrightarrow>\<^sub>A ?![Q]"
  using assms
  unfolding entails_def pp_def conj_assn_def pure_assn_def
  by auto


lemma post_tr_rep':
  assumes "\<forall> s. P s \<longrightarrow> Q s"
    and "\<And> R s0. (\<forall> s0 . Q s0 \<longrightarrow> R s0 \<Longrightarrow>\<^sub>A ?![G]) \<Longrightarrow> Q s0 \<Longrightarrow> f(R) s0 \<Longrightarrow>\<^sub>A ?![G]"
  shows "P s0 \<Longrightarrow> (\<exists>\<^sub>an. rep_f f n) s0 \<Longrightarrow>\<^sub>A ?![G]"
  apply (rule entails_trans[of _ "?![G]"])
   prefer 2
  subgoal unfolding exists_assn_def entails_def trpp_def 
    using assms by auto
  unfolding entails_def exists_assn_def pp_def
  apply auto
  subgoal premises pre for s tr n
  proof-
    have 1:"Q s0 \<Longrightarrow> rep_f f n s0 \<Longrightarrow>\<^sub>A ?![G]" for n
    proof(induction n arbitrary:s0)
      case 0
      then show ?case 
        apply simp
        unfolding init_def entails_def trpp_def 
        apply auto
        by rule
    next
      case (Suc n)
      show ?case 
        apply simp
        apply (rule assms(2))
        apply auto
         apply(rule Suc)
        apply auto
        apply(rule Suc)
        done
    qed
    have 2:"P s0 \<Longrightarrow> rep_f f n s0 s tr \<Longrightarrow> trInv G tr" for n s tr
      using 1[of n] assms(1,2)
      unfolding entails_def trpp_def by auto
    show ?thesis
      using 2 pre unfolding trpp_def
      by auto
  qed
  done



end
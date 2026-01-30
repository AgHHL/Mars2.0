theory ContinuousSyntax
  imports DiscreteSyntax
begin

\<comment> \<open>a continuous can be a general calculation block or a integrator block
it also defined as a block while sample_time = 0.
note: In continuous blocks, offset list has other meanings which deciding the corresponding
outupd is a math operation, integrator or derivative
offset = 0: math operation(called calculation blocks)
offset = 1: integrator
In this file, we define the syntax for continuous blocks first, then define well-formed for a 
continuous diagram. Furthermore, we define functions for combination(for ODEs) and also for 
translating block to an ODE\<close>


section \<open>Syntax and classification functions for continuous block\<close>

type_synonym DisBlk = block
type_synonym ConBlk = block



\<comment> \<open>return the computational blocks in the continuous blocks\<close>
fun getCalBlks :: "ConBlk list \<Rightarrow> ConBlk list" where
  "getCalBlks [] = []" |
  "getCalBlks (b#bl) = (if (set (get_offsets b)) = {0} then b#getCalBlks bl
  else getCalBlks bl)"

lemma getCalBlks_offsets: "\<forall>x \<in> set (getCalBlks bl). set (get_offsets x) = {0}"
  apply clarify subgoal premises pre for x
    using pre
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis using Cons unfolding getCalBlks.simps by auto
    next
      case False
      then show ?thesis using Cons unfolding getCalBlks.simps by auto
    qed
  qed
  done

lemma getCalBlks_last: "getCalBlks (bl@[b]) = 
(if (set (get_offsets b)) = {0} then getCalBlks bl@[b] else getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  next
    case False
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  qed
qed

lemma getCalBlks_rev: "getCalBlks (rev bl) = 
rev (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case using getCalBlks_last by simp
qed

lemma getCalBlksSubset : "Outputs (getCalBlks bl) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksSubset2 : "set (getCalBlks bl) \<subseteq> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksSubset3 : "Inputs (getCalBlks bl) \<subseteq> Inputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case by auto
qed

lemma getCalBlksPerm : "bl1 <~~> bl2 \<Longrightarrow> 
(getCalBlks bl1) <~~> (getCalBlks bl2)"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 1: "b1 \<in> set bl2"
    using Cons(2) by (simp add: prem_seteq)
  have 2: "bl1 <~~> remove1 b1 bl2"
    using Cons(2) 1 by (metis perm_remove_perm remove_hd)
  have 3: "getCalBlks bl1 <~~> getCalBlks (remove1 b1 bl2)"
    using Cons 2 by simp
  then show ?case
  proof(cases "set (get_offsets b1) = {0}")
    case True
    have 4: "getCalBlks (remove1 b1 bl2) = remove1 b1 (getCalBlks bl2)"
    using True proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "a = b1")
        case True
        then show ?thesis unfolding getCalBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding getCalBlks.simps using Cons by simp
      qed
    qed
    have 5: "b1 \<in> set (getCalBlks bl2)"
      using 1 True
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case by auto
    qed
    then show ?thesis unfolding getCalBlks.simps using True 3 4 perm_remove2 by fastforce
  next
    case False
    have 5: "getCalBlks (remove1 b1 bl2) = getCalBlks bl2"
    using False proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons b2 bl2)
      then show ?case
      proof(cases "b1 = b2")
        case True
        then show ?thesis unfolding getCalBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding getCalBlks.simps using Cons by simp
      qed
    qed
    then show ?thesis unfolding getCalBlks.simps using Cons 3 False by presburger
  qed
qed

lemma getCalBlks_distinct: "distinct bl \<Longrightarrow> 
distinct (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding getCalBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons
      using getCalBlksSubset2 by auto
  next
    case False
    then show ?thesis unfolding getCalBlks.simps using Cons by auto
  qed
qed

lemma getCalBlks_remove: "b \<in> set bl \<Longrightarrow> 
getCalBlks (remove1 b bl) =  remove1 b (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons
      using getCalBlksSubset2 by auto
  next
    case False
    then show ?thesis unfolding getCalBlks.simps using Cons by (smt (verit, ccfv_SIG) 
          getCalBlks.simps(2) getCalBlks_offsets remove1.simps(2) remove1_idem set_ConsD)
  qed
qed

\<comment> \<open>End section\<close>

section \<open>well-formed definition for continuous diagram and some theorems for well-formed\<close>

\<comment> \<open>limitation for a continuous block;
1. length outputs = length offsets = length outupds;
2. Outputs uniqueness in a block
3. "set (get_offsets b) = {0}" for math operations and "set (get_offsets b) = {1}" for integrator
4. no loop for a computational block\<close>
definition "Available' b = ((length (get_offsets b)) = (length (get_outputs b))
    \<and> ((length (get_outputs b)) = (length (get_outupd b)))
    \<and> (\<forall>i j. i < j \<and> j < (length (get_outputs b)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs b) i) \<noteq> (nth (get_outputs b) j))  \<and> 
  ({0} = set (get_offsets b) \<or> {1} = set (get_offsets b) \<or> {} = set (get_offsets b)) 
  \<and> (get_sample_time b = 0) \<and>
  (1 \<notin> set (get_offsets b) \<longrightarrow> (set (get_outputs b) \<inter> set (get_inputs b) = {})))"

definition "wf2 bl = ((Unique bl) \<and> (Graph (set bl)) \<and> (\<forall>b \<in> set bl. 
Available' b))"

lemma wf2_lemma : "wf2 (b#bl) \<Longrightarrow> wf2 bl"
  unfolding wf2_def Unique_def Graph_def by (smt (verit, best) Suc_leI le_imp_less_Suc 
      length_Cons less_imp_le_nat nth_Cons_Suc set_subset_Cons subsetD)

lemma wf2_lemma2: "wf2 bl1 \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow> wf2 bl2"
  subgoal premises pre
proof -
  have 1: "Unique bl2"
    using pre Unique_Permutation unfolding wf2_def by auto
  have 2: "set bl1 = set bl2"
    using pre(2) by (meson perm_sym prem_seteq subsetI subset_antisym)
  show ?thesis using 1 2 unfolding wf2_def using wf2_def pre(1) by presburger
qed
  done

lemma wf2_remove: "b \<in> set bl \<Longrightarrow> wf2 bl \<Longrightarrow> wf2 (remove1 b bl)"
  subgoal premises pre
proof -
  have 1: "Unique (remove1 b bl)"
    using pre by (simp add: wf2_def Unique_remove)
  show ?thesis using 1 unfolding wf2_def using wf2_def pre(1)
    by (metis wf2_lemma wf2_lemma2 perm_remove pre(2))
qed
  done

lemma wf2_rev: "wf2 bl \<Longrightarrow> wf2 (rev bl)"
  subgoal premises pre
proof -
  have 1: "Unique (rev bl)"
    using pre by (simp add: wf2_def Unique_rev)
  show ?thesis using 1 pre unfolding wf2_def using wf2_def by simp
qed
  done



\<comment> \<open>besorted for continuous blocks(and only for computational blocks);
unlike the "besorted" for discrete blocks, offsets here is always 0(vs Unit Delay)\<close>
fun besorted2 :: "block list \<Rightarrow> bool" where
"besorted2 [] = True" |
"besorted2 (b # bl) = (besorted2 bl \<and> (\<forall> a. a \<in> set bl \<longrightarrow> 
            (set (get_outputs a) \<inter> set (get_inputs b) = {})))"

lemma besorted2_empty: "besorted2 (b#bl) \<Longrightarrow> set (get_inputs b) \<inter> Outputs bl = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case by (smt (verit, best) Outputs.simps(2) Un_iff besorted2.simps(2) 
        disjoint_iff list.set_intros(1) list.set_intros(2))
qed

lemma besorted2_is_besorted : "besorted2 bl \<Longrightarrow> besorted bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case unfolding besorted2.simps besorted.simps
    by (metis check_offset.elims(2))
qed

lemma besorted2_last : "besorted2 (bl@[a]) \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding besorted2.simps by simp
qed

lemma besorted2_Cons : "besorted2 (a#bl) \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding besorted2.simps by simp
qed

lemma besorted2_last2: "besorted2 (bl@[a]) \<Longrightarrow> set (get_outputs a) \<inter> Inputs bl = {}"
proof(induction bl)
  case Nil
  then show ?case by auto
next
  case (Cons b bl)
  then show ?case unfolding besorted2.simps by fastforce
qed

lemma besorted2_remove: "Unique bl \<Longrightarrow>besorted2 bl \<Longrightarrow> besorted2 (remove1 a bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis using Cons(3) by simp
  next
    case False
    have tmp1: "besorted2 (remove1 a bl)"
      using Cons unfolding Unique_def
      by (meson Cons.IH Cons.prems(1) Unique_lemma besorted2.simps(2))
    then show ?thesis using Cons(3) 
      by (metis besorted2.simps(2) notin_set_remove1 remove1.simps(2))
  qed
qed

lemma besorted2_remove2: "besorted2 (al@bl) \<Longrightarrow> besorted bl"
proof(induction al)
  case Nil
  then show ?case by (simp add: besorted2_is_besorted)
next
  case (Cons a al)
  then show ?case by simp
qed

lemma besorted2_remove3: "besorted2 (al@bl) \<Longrightarrow> besorted2 bl"
proof(induction al)
  case Nil
  then show ?case by (simp add: besorted2_is_besorted)
next
  case (Cons a al)
  then show ?case by simp
qed

lemma besorted2_find_0indegree_NotNone: "besorted2 al \<Longrightarrow> al = cl@bl \<Longrightarrow> bl \<noteq> [] \<Longrightarrow>
fst (find_0indegree_blocks al bl cl) = Some (hd bl) \<and> snd (find_0indegree_blocks al bl cl) = tl bl"
  subgoal premises pre 
proof(cases "bl = []")
  case True
  then show ?thesis using pre by auto
next
  case False
  have 1: "set (get_inputs (hd bl)) \<inter> Outputs (tl bl) = {}"
  proof -
    show ?thesis using pre(1,2) besorted2_empty Outputs_rev 
      by (metis False besorted2_remove3 list.exhaust_sel)
  qed
  have 2: "get_block_indegree (hd bl) al - Outputs cl = {}"
  proof(cases "0 \<in> set (get_offsets (hd bl)) \<or> get_sample_time (hd bl) = 0")
    case True
    then show ?thesis unfolding get_block_indegree_def apply simp using 1 pre(2) False by (smt 
          (verit, best) DiffE IntE Outputs.simps(2) Outputs_Cons UnE disjoint_iff_not_equal 
          list.collapse subsetI)
  next
    case False
    then show ?thesis unfolding get_block_indegree_def by auto
  qed
  then show ?thesis using find_0indegree_blocks.simps(2)[of al "hd bl" "tl bl" cl] 
    by (simp add: False)
qed
  done

lemma toposort_besorted: "besorted2 al \<Longrightarrow> al = cl@bl 
\<Longrightarrow> length (topological_sort al bl cl) = length al"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    by (metis (no_types, lifting) case_prodD length_induct mem_Collect_eq)
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    have 3: "topological_sort al bl cl = cl"
      unfolding topological_sort.simps[of al bl cl]  using True by simp
    then show ?thesis using 2(3) True by auto
  next
    case False
    have 3: "fst (find_0indegree_blocks al bl cl) = Some (hd bl) \<and>
        snd (find_0indegree_blocks al bl cl) = tl bl"
      using besorted2_find_0indegree_NotNone 2(2,3) False by auto
    have 4: "length (snd (find_0indegree_blocks al bl cl)) < length bl"
      using 2 unfolding loop_free_def sortDiag_def using topological_sort.simps[of al bl cl]
      using 3 length_find_0indegree by blast
    have 5: "topological_sort al bl cl = topological_sort al (tl bl) (cl@[hd bl])"
    proof -
      have tmp: "topological_sort al bl cl = (let x = find_0indegree_blocks al bl cl
        in topological_sort al (snd x) (cl @ [the (fst x)]))"
        using topological_sort.simps[of al bl cl] 3 by (smt (verit, del_insts) option.distinct(1))
      show ?thesis using tmp 3 by simp
    qed
    have 6: "al = cl@[hd bl]@(tl bl)"
      using 2(3) False by auto
    then show ?thesis using 2 4 5 by (metis "3" append.assoc case_prodI mem_Collect_eq)
  qed
qed

lemma besorted2_loopfree: "besorted2 bl \<Longrightarrow> loop_free bl"
  using toposort_besorted unfolding loop_free_def sortDiag_def by blast

lemma besorted2_lemma: "besorted2 (bl@[a]@[b]) \<Longrightarrow> set (get_outputs b) \<inter> set (get_inputs a) = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case by simp
qed

lemma besortedTobesorted2 : "besorted bl \<Longrightarrow> \<forall>b \<in> set bl. (set (get_offsets b) = {0})
  \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "besorted2 bl"
    using Cons(2) unfolding besorted.simps using Cons(1,3) by auto
  have 2: "\<forall>a. a \<in> set bl \<longrightarrow> set (get_outputs a) \<inter> set (get_inputs b) = {}"
    using Cons(2) unfolding besorted.simps using Cons(3)
    by (smt (verit) Int_commute boolean_algebra.conj_zero_right check_offset.elims(1) 
        disjoint_insert(2) insertI1 list.set(1) list.set_intros(1))
  then show ?case unfolding besorted2.simps using 1 by simp
qed

lemma besortedTrans : "besorted bl \<Longrightarrow> wf2 bl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {0} \<or> set (get_offsets b) = {}) \<Longrightarrow> besorted2 bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "besorted2 bl"
    using Cons(2) unfolding besorted.simps using Cons 
    by (meson list.set_intros(2) wf2_lemma)
  have 2: "\<forall>a. a \<in> set bl \<longrightarrow> set (get_outputs a) \<inter> set (get_inputs b) = {}"
    using Cons(2) unfolding besorted.simps using Cons(3,4) by (metis Available'_def Cons.prems(1) 
        Graph_def besorted2.simps(2) besortedTobesorted2 length_greater_0_conv set_empty2 wf2_def)
  then show ?case unfolding besorted2.simps using 1 by simp
qed

lemma sort_is_sorted2 : "cl = (getCalBlks bl) \<Longrightarrow> sortDiag (rev cl) = rev cl  
\<Longrightarrow> wf2 bl \<Longrightarrow> besorted2 (rev cl)"
  subgoal premises pre
proof -
  have 1: "set cl \<subseteq> set bl"
    using pre(1)
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps 
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
        unfolding getCalBlks.simps by auto
    next
      case False
      then show ?thesis using Cons(1)[of "getCalBlks bl"] Cons(2)
        unfolding getCalBlks.simps by auto
    qed
  qed
  have 2: "(\<forall>i j. i < j \<and> j < length bl \<and> 0 \<le> i \<longrightarrow> bl ! i \<noteq> bl ! j)"
    using 1 pre(3) unfolding wf2_def Unique_def by simp
  have 3: "Unique cl"
    using pre(1) 2 unfolding Unique_def
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps
    proof(cases "set (get_offsets b) = {0}")
      case True
      have tmp1: "\<forall>i j. i < j \<and> j < length (getCalBlks bl) \<and> 0 \<le> i 
        \<longrightarrow> getCalBlks bl ! i \<noteq> getCalBlks bl ! j"
        using Cons(1,3) by (metis Unique_def Unique_lemma)
      have tmp2: "\<exists>c. c \<in> set (getCalBlks bl) \<and> c = b \<Longrightarrow> 
  \<forall>i j. i < j \<and> j < length (b # bl) \<and> 0 \<le> i \<longrightarrow> (b # bl) ! i \<noteq> (b # bl) ! j \<Longrightarrow> False"
        apply clarify subgoal premises pre for c
      proof -
        have tmp2_1: "\<forall>c. c \<in> set (getCalBlks bl) \<longrightarrow> c \<in> set bl"
          apply clarify subgoal for c
        proof(induction bl)
          case Nil
          then show ?case by simp
        next
          case (Cons d dl)
          then show ?case unfolding getCalBlks.simps
            by (smt (verit, best) list.set_intros(1) list.set_intros(2) set_ConsD)
        qed
        done
      have tmp2_2 : "b \<in> set bl"
        using tmp2_1 pre(2) by simp 
      show ?thesis using tmp2_2 pre(1) by (metis Suc_leI bot_nat_0.extremum in_set_conv_nth 
            le_imp_less_Suc length_Cons nth_Cons_0 nth_Cons_Suc)
      qed
      done
    have tmp3: "\<forall>i. i < length (getCalBlks bl) \<and> 0 \<le> i \<longrightarrow> 
          (getCalBlks bl) ! i \<noteq> b"
      using tmp2 Cons(3) using nth_mem by blast
    then show ?thesis using Cons(2) True unfolding getCalBlks.simps apply simp
        using tmp1 using less_Suc_eq_0_disj by fastforce
    next
      case False
      then show ?thesis using Cons unfolding getCalBlks.simps
        by (metis Unique_def Unique_lemma)
    qed
  qed
  have 4: "Unique (rev cl)"
    using 3 Unique_rev by blast
  have 5: "Graph (set (rev cl))"
  proof -
    have tmp: "set (rev cl) \<subseteq> set bl"
      using 1 by simp
    show ?thesis using pre(3) tmp unfolding wf2_def Graph_def by (meson subsetD)
  qed
  have 6: "besorted (rev cl)"
    using 4 5 pre(2) sort_is_sorted by force
  have 7: "\<forall>b \<in> set (rev cl). (set (get_offsets b) = {0})"
    using pre(1)
  proof(induction bl arbitrary:cl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis using Cons unfolding getCalBlks.simps by simp
    next
      case False
      then show ?thesis using Cons(1)[of cl] Cons(2) 
        unfolding getCalBlks.simps by presburger
    qed
    
  qed
  show ?thesis using 6 7 besortedTobesorted2 by presburger
qed
  done

lemma sort_is_sorted3 : "loop_free cl \<Longrightarrow> sortDiag cl = dl \<Longrightarrow> \<forall>b \<in> set cl. (set (get_offsets b) = {0})
\<Longrightarrow> wf2 cl \<Longrightarrow> besorted2 dl"
  subgoal premises pre
proof -
  have 1: "besorted dl"
    using pre unfolding wf2_def using sort_is_sorted by meson
  show ?thesis using 1 besortedTobesorted2 pre(2) pre(3) sortDiag_subset by blast
qed
  done

text \<open>Delete those discrete blocks in a Simulink graph.\<close>
fun deleteDisBlks :: "block list \<Rightarrow> block list" where
  "deleteDisBlks [] = []" |  
  "deleteDisBlks (a#al) = (if (get_sample_time a > 0) then deleteDisBlks al
  else (a#(deleteDisBlks al)))"

\<comment> \<open>return the integrator blocks in the continuous blocks\<close>
fun findIntegBlks :: "block list \<Rightarrow> block list" where
  "findIntegBlks [] = []" |
  "findIntegBlks (b#bl) = (if (set (get_offsets b) = {1}) then 
b#(findIntegBlks bl) else findIntegBlks bl)"

lemma findIntegBlks_forall: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
  apply clarify subgoal for c
  proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case
    proof(cases "(set (get_offsets b)) = {1}")
    case True
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  next
    case False
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  qed
  qed
  done

lemma findIntegBlks_last: "findIntegBlks (bl@[b]) = 
(if (set (get_offsets b)) = {1} then findIntegBlks bl@[b] else findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding findIntegBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {1}")
    case True
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  next
    case False
    then show ?thesis unfolding findIntegBlks.simps using Cons by auto
  qed
qed

lemma findIntegBlks_rev: "findIntegBlks (rev bl) = 
rev (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding findIntegBlks.simps by auto
next
  case (Cons a bl)
  then show ?case using findIntegBlks_last by simp
qed

lemma findIntegBlksSubset : "Outputs (findIntegBlks bl) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findIntegBlks.simps by auto
qed


lemma findIntegBlksSubset2 : "set bl1 \<subseteq> set bl2 \<Longrightarrow>
Outputs (findIntegBlks bl1) \<subseteq> Outputs (findIntegBlks bl2)"
proof(induction bl1 arbitrary: bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 1: "set (get_offsets b) = {1} \<Longrightarrow> b \<in> set bl2 \<Longrightarrow> set (get_outputs b) \<subseteq> 
        Outputs (findIntegBlks bl2)"
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "b = a")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by auto
      next
        case False
        have tmp1: "set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl2)"
          using Cons False by simp
        then show ?thesis unfolding findIntegBlks.simps by auto
      qed
    qed
    then show ?thesis unfolding findIntegBlks.simps using Cons True by simp
  next
    case False
    then show ?thesis unfolding findIntegBlks.simps using Cons by simp
  qed
qed

lemma findIntegBlksSubset3 : "set (findIntegBlks bl) \<subseteq> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findIntegBlks.simps by auto
qed

lemma findIntegBlkswf : "wf2 bl \<Longrightarrow> wf2 (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "set (get_offsets a) = {0}")
    case True
    then show ?thesis unfolding getCalBlks.simps using Cons
      by (simp add: wf2_lemma)
  next
    case False
    have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
      using Cons(2) unfolding wf2_def Unique_def
      by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
    have tmp2: "\<forall>j. j < (length (findIntegBlks bl)) \<and> j \<ge> 0 
      \<longrightarrow> a \<noteq> (nth (findIntegBlks bl) j)"
      using tmp1 findIntegBlksSubset3
      by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
    have tmp3: "Unique (a # findIntegBlks bl)"
      using Cons Unique_add unfolding wf2_def tmp2 by (metis wf2_def wf2_lemma tmp2)
    have tmp4: "Graph (set (a # findIntegBlks bl))"
    proof -
      have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
        using findIntegBlksSubset3 by auto
    show ?thesis using tmp1 Cons(2) unfolding wf2_def by (meson Graph_def subsetD)
    qed
    have tmp5: "Ball (set (a # findIntegBlks bl)) Available' "
    proof -
      have tmp1: "set (a # findIntegBlks bl) \<subseteq> set (a#bl)"
        using findIntegBlksSubset3 by auto
      show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
    qed
    show ?thesis using False unfolding findIntegBlks.simps wf2_def apply simp 
      using tmp3 tmp4 tmp5 by (metis wf2_def wf2_lemma list.set_intros(1) list.simps(15))
    qed
  qed

lemma getCalBlkswf : "wf2 bl \<Longrightarrow> wf2 (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "set (get_offsets a) = {0}")
    case True
    have tmp1: "\<forall>j. j < (length bl) \<and> j \<ge> 0 \<longrightarrow> a \<noteq> (nth bl j) "
      using Cons(2) unfolding wf2_def Unique_def
      by (metis wf2_def Cons.prems Unique_k list.set_intros(1) remove_hd)
    have tmp2: "\<forall>j. j < (length (getCalBlks bl)) \<and> j \<ge> 0 
      \<longrightarrow> a \<noteq> (nth (getCalBlks bl) j)"
      using tmp1 getCalBlksSubset2
      by (metis in_set_conv_nth less_eq_nat.simps(1) subset_code(1))
    have tmp3: "Unique (a # getCalBlks bl)"
      using Cons Unique_add unfolding wf2_def tmp2 by (metis wf2_def wf2_lemma tmp2)
    have tmp4: "Graph (set (a # getCalBlks bl))"
    proof -
      have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
        using getCalBlksSubset2 by auto
    show ?thesis using tmp1 Cons(2) unfolding wf2_def by (meson Graph_def subsetD)
    qed
    have tmp5: "Ball (set (a # getCalBlks bl)) Available' "
    proof -
      have tmp1: "set (a # getCalBlks bl) \<subseteq> set (a#bl)"
        using getCalBlksSubset2 by auto
      show ?thesis using tmp1 Cons(2) unfolding wf2_def by blast
    qed
    then show ?thesis unfolding getCalBlks.simps using Cons True tmp3 tmp4 wf2_def by presburger
  next
    case False
    show ?thesis using False unfolding getCalBlks.simps using Cons
      by (simp add: wf2_lemma)
    qed
qed


lemma IntegInterComputationalBlocks : "wf2 bl \<Longrightarrow>
Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "Outputs (findIntegBlks bl) \<inter> Outputs (getCalBlks bl) = {}"
    using Cons wf2_lemma by auto
  have 2: "set (get_outputs b) \<inter> Outputs bl = {}"
    using Cons(2) unfolding wf2_def Unique_def Graph_def 
    by (meson wf2_def Cons.prems Graph_lemma2 disjoint_iff)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 3: "set (get_outputs b) \<inter> Outputs (getCalBlks bl) = {}"
      using getCalBlksSubset 2 by auto
    show ?thesis using True unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 3 by (simp add: Int_Un_distrib2)
  next
    case False
    then show ?thesis  unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 findIntegBlksSubset 2 by auto
  qed
qed

lemma IntegCalOutputsUniun: "wf2 bl \<Longrightarrow>
Outputs bl = Outputs (getCalBlks bl) \<union> Outputs (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "Outputs bl = Outputs (getCalBlks bl) \<union> Outputs (findIntegBlks bl)"
    using Cons wf2_lemma by simp
  have 2: "set (get_outputs b) \<inter> Outputs bl = {}"
    using Cons(2) unfolding wf2_def Unique_def Graph_def 
    by (meson wf2_def Cons.prems Graph_lemma2 disjoint_iff)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 3: "set (get_outputs b) \<inter> Outputs (getCalBlks bl) = {}"
      using getCalBlksSubset 2 by auto
    show ?thesis using True unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using "1" by blast
  next
    case False
    note F1 = False
    then show ?thesis
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 findIntegBlksSubset 2 by force
    next
      case False
      have 3: "set (get_offsets b) = {}"
        using Cons(2) F1 False unfolding wf2_def Available'_def by simp
      have 4: "set (get_outputs b) = {}"
        using 3 Cons(2) unfolding wf2_def Available'_def by simp
      then show ?thesis unfolding findIntegBlks.simps getCalBlks.simps using 1 by simp
    qed
  qed
qed

lemma IntegCalUniun: "wf2 bl \<Longrightarrow>
set bl = set (getCalBlks bl) \<union> set (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  have 1: "set bl = set (getCalBlks bl) \<union> set (findIntegBlks bl)"
    using Cons wf2_lemma by simp
  have 2: "set (get_outputs b) \<inter> Outputs bl = {}"
    using Cons(2) unfolding wf2_def Unique_def Graph_def 
    by (meson wf2_def Cons.prems Graph_lemma2 disjoint_iff)
  then show ?case
  proof(cases "set (get_offsets b) = {1}")
    case True
    have 3: "set (get_outputs b) \<inter> Outputs (getCalBlks bl) = {}"
      using getCalBlksSubset 2 by auto
    show ?thesis using True unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using "1" by blast
  next
    case False
    note F1 = False
    then show ?thesis
    proof(cases "set (get_offsets b) = {0}")
      case True
      then show ?thesis unfolding findIntegBlks.simps getCalBlks.simps apply simp
      using 1 findIntegBlksSubset 2 by force
    next
      case False
      have 3: "set (get_offsets b) = {}"
        using Cons(2) F1 False unfolding wf2_def Available'_def by simp
      have 4: "set (get_outputs b) = {}"
        using 3 Cons(2) unfolding wf2_def Available'_def by simp
      then show ?thesis unfolding findIntegBlks.simps getCalBlks.simps using 1
        by (metis Cons.prems Graph_def length_greater_0_conv list.set_intros(1) set_empty2 wf2_def)
    qed
  qed
qed

lemma findIntegBlksPerm : "bl1 <~~> bl2 \<Longrightarrow> (findIntegBlks bl1) <~~> (findIntegBlks bl2)"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 1: "b1 \<in> set bl2"
    using Cons(2) by (simp add: prem_seteq)
  have 2: "bl1 <~~> remove1 b1 bl2"
    using Cons(2) 1 by (metis perm_remove_perm remove_hd)
  have 3: "findIntegBlks bl1 <~~> findIntegBlks (remove1 b1 bl2)"
    using Cons 2 by simp
  then show ?case
  proof(cases "set (get_offsets b1) = {1}")
    case True
    have 4: "findIntegBlks (remove1 b1 bl2) = remove1 b1 (findIntegBlks bl2)"
    using True proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case
      proof(cases "a = b1")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by simp
      qed
    qed
    have 5: "b1 \<in> set (findIntegBlks bl2)"
      using 1 True
    proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons a bl2)
      then show ?case by auto
    qed
    then show ?thesis unfolding findIntegBlks.simps using True 3 4 perm_remove2 by fastforce
  next
    case False
    have 5: "findIntegBlks (remove1 b1 bl2) = findIntegBlks bl2"
    using False proof(induction bl2)
      case Nil
      then show ?case by simp
    next
      case (Cons b2 bl2)
      then show ?case
      proof(cases "b1 = b2")
        case True
        then show ?thesis unfolding findIntegBlks.simps using Cons(2) by simp
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by simp
      qed
    qed
    then show ?thesis unfolding findIntegBlks.simps using Cons 3 False by presburger
  qed
qed

lemma findIntegBlks_remove: "wf2 bl \<Longrightarrow>
findIntegBlks (remove1 c bl) = remove1 c (findIntegBlks bl)"
proof(induction bl)
  case Nil
  then show ?case unfolding findIntegBlks.simps by auto
next
  case (Cons a bl)
  then show ?case
  proof(cases "(set (get_offsets a)) = {1}")
    case True
    have "wf2 bl"
      using Cons(2) wf2_lemma by simp
    then show ?thesis unfolding findIntegBlks.simps using Cons True by auto
  next
    case False
    note F1 = False
    then show ?thesis
    proof(cases "a = c")
      case True
      have "c \<notin> set bl"
        using Cons(2) True unfolding wf2_def Unique_def by (metis Cons.prems Unique_k gr0I 
            in_set_conv_nth le_numeral_extra(3) list.set_intros(1) nat_less_le remove_hd wf2_def)
      then show ?thesis unfolding findIntegBlks.simps using False Cons 
        by (simp add: True remove1_idem wf2_lemma)
    next
      case False
      have 1: "remove1 c (a # bl) = a#(remove1 c bl)"
        using False by auto
      then show ?thesis unfolding findIntegBlks.simps using F1 Cons 
        using findIntegBlks.simps(2) wf2_lemma by presburger
    qed
  qed
qed

\<comment> \<open>End section\<close>

section \<open>definitions and theorems for combination of ODE\<close>

\<comment> \<open>we classify those blocks by calling function "compute_st_forward" and "compute_st_backward"\<close>

text \<open>Then check the blocks(no blocks whose sample_time = -1) and split them\<close>
fun checkType :: "block list \<Rightarrow> bool" where
  "checkType [] = True" |
  "checkType (b#bl) = (if (get_sample_time b = -1) then False else checkType bl)"

fun classifyBlocks :: "block list \<Rightarrow> DisBlk list \<times> ConBlk list" where
  "classifyBlocks [] = ([],[])" |
  "classifyBlocks (b#bl) = (let x = classifyBlocks bl in 
      (if (get_sample_time b = 0) then (fst x, b#(snd x)) else (b#(fst x), snd x)))"

text \<open>The following functions are for the combination.
note: combine block "a" into block "b"
we call block "b" the basic block and block "a" the additional block\<close>
(*combine the inputs, basic inputs vl1; additional inputs vl2; additional output v
we remain the inputs in vl2 and delete those same inputs and produced inputs for vl1.
note: when calling this function, we have already validated the additional block produces
outputs for the basic block inputs.*)
fun combineInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> var list" where
  "combineInputs [] vl2 v = vl2" |
  "combineInputs (v1#vl1) vl2 v = (if v = v1 \<or> v1 \<in> set vl2 then (combineInputs vl1 vl2 v)
  else v1#(combineInputs vl1 vl2 v))"

lemma combineInputs_subset: "set (combineInputs vl1 vl2 v) \<subseteq> set (vl1@vl2)"
proof(induction vl1)
  case Nil
  then show ?case by simp
next
  case (Cons v1 vl1)
  then show ?case unfolding combineInputs.simps by auto
qed

lemma combineInputs_subset2: "set (combineInputs vl1 vl2 v) \<subseteq> set vl2 \<union> (set vl1 - {v})"
proof(induction vl1)
  case Nil
  then show ?case by simp
next
  case (Cons v1 vl1)
  then show ?case unfolding combineInputs.simps using Cons by auto
qed

lemma combineInputs_lengtheq: "drop (length (combineInputs a2 a1 b) - length a1) 
(map (\<lambda>a. h a t) (combineInputs a2 a1 b)) = map (\<lambda>a. h a t) a1"
proof(induction a2)
  case Nil
  then show ?case by simp
next
  case (Cons a a2)
  then show ?case unfolding combineInputs.simps by (smt (verit, ccfv_threshold) 
        Suc_diff_le diff_le_self drop_Suc_Cons length_Cons length_drop 
        length_map list.simps(9))
qed

lemma combineInputs_length: "length (combineInputs vl1 vl2 v) \<ge> length vl2"
proof(induction vl1)
  case Nil
  then show ?case by simp
next
  case (Cons a vl1)
  then show ?case unfolding combineInputs.simps by auto
qed



\<comment> \<open>for ODE\<close>
fun combineInputs2 :: "var list \<Rightarrow> var list \<Rightarrow> var list" where
  "combineInputs2 [] vl2 = vl2" |
  "combineInputs2 (v1#vl1) vl2 = (if v1 \<in> set vl2 then (combineInputs2 vl1 vl2)
  else v1#(combineInputs2 vl1 vl2))"

lemma combineInputs2_subset: "set (combineInputs2 vl1 vl2) \<subseteq> set (vl1@vl2)"
proof(induction vl1)
  case Nil
  then show ?case by simp
next
  case (Cons v1 vl1)
  then show ?case unfolding combineInputs2.simps by auto
qed

lemma combineInputs2_valeq: "drop (length (combineInputs2 a2 a1) - length a1) (map (\<lambda>a. h a t) (combineInputs2 a2 a1))
  = map (\<lambda>a. h a t) a1"
proof(induction a2)
  case Nil
  then show ?case by simp
next
  case (Cons a a2)
  then show ?case
  proof(cases "a \<in> set a1")
    case True
    then show ?thesis using Cons unfolding combineInputs2.simps by auto
  next
    case False
    then show ?thesis using Cons unfolding combineInputs2.simps by (smt (verit) Suc_pred 
          diff_commute diff_is_0_eq diff_zero drop_Suc_Cons impossible_Cons length_drop 
          length_map length_tl linorder_not_le list.sel(2) list.sel(3) list.simps(9) 
          list.size(3) zero_less_diff)
  qed
qed

lemma combineInputs2_length : "length (combineInputs2 vl1 vl2) \<ge> length vl2" 
proof(induction vl1)
  case Nil
  then show ?case by simp
next
  case (Cons v1 vl1)
  then show ?case unfolding combineInputs2.simps by auto
qed

text\<open>Return the position of "a" in a list bl\<close>
fun findPos :: "'a list \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int" where
  "findPos [] a i = -1" |
  "findPos (b#bl) a i = (if a = b then i else (findPos bl a (i+1)))"

lemma findPos_notin: "i \<ge> 0 \<Longrightarrow> findPos bl a i = -1 \<Longrightarrow> a \<notin> set bl"
proof(induction bl arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findPos.simps by (smt (verit, best) set_ConsD)
qed

lemma findPos_in: "i \<ge> 0 \<Longrightarrow> findPos bl a i \<noteq> -1 \<Longrightarrow> a \<in> set bl"
proof(induction bl arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findPos.simps by (metis add_nonneg_nonneg list.set_intros(1) 
        list.set_intros(2) zero_less_one_class.zero_le_one)
qed

lemma findPos_lengthleq: "i \<ge> 0 \<Longrightarrow> findPos bl a i < i + length bl"
proof(induction bl arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding findPos.simps by (smt (z3) One_nat_def list.size(4) 
        of_nat_1 of_nat_le_0_iff zadd_int_left)
qed

lemma findPos_ith: "i \<ge> 0 \<Longrightarrow> a \<in> set bl \<Longrightarrow> bl ! (nat (findPos bl a i) - i) = a"
proof(induction bl arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis unfolding findPos.simps by auto
  next
    case False
    then show ?thesis unfolding findPos.simps apply simp using Cons by (smt (verit) 
          diff_diff_left diff_is_0_eq findPos.simps(2) lessI less_zeroE list.set_cases nat_int 
          nth_Cons' of_nat_1 of_nat_add plus_1_eq_Suc set_ConsD zero_less_diff zero_order(1))
  qed
qed

lemma combineInputs2_ith: "a \<in> set a1 \<Longrightarrow> (combineInputs2 a2 a1) !
    (length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) = a"
proof(induction a2)
  case Nil
  then show ?case apply simp using findPos_ith by (metis diff_zero of_nat_0 zero_le)
next
  case (Cons b a2)
  then show ?case
  proof(cases "b \<in> set a1")
    case True
    then show ?thesis unfolding combineInputs2.simps using Cons by auto
  next
    case False
    have 1: "(length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) \<ge> 0 \<and> 
      (length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) < length (combineInputs2 a2 a1)"
      using combineInputs2_length findPos_lengthleq[of 0 a1 a] apply simp by (metis Cons.prems 
          add.commute add_mono_thms_linordered_field(3) le_refl length_pos_if_in_set 
          less_diff_conv2 nat_eq_iff nat_less_iff trans_le_add2)
    show ?thesis using False unfolding combineInputs2.simps using Cons apply simp using 1
      by (simp add: Suc_diff_le combineInputs2_length)
  qed
qed

lemma combineInputs_ith: "a \<in> set a1 \<Longrightarrow> (combineInputs a2 a1 b) !
    (length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) = a"
proof(induction a2)
  case Nil
  then show ?case apply simp using findPos_ith by (metis diff_zero of_nat_0 zero_le)
next
  case (Cons a' a2)
  then show ?case
  proof(cases "b = a' \<or> a' \<in> set a1")
    case True
    then show ?thesis unfolding combineInputs.simps using Cons by auto
  next
    case False
    have 1: "(length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) \<ge> 0 \<and> 
      (length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) < length (combineInputs a2 a1 b)"
      using combineInputs_length findPos_lengthleq[of 0 a1 a] apply simp by (metis Cons.prems
      add.commute add_mono_thms_linordered_field(3) dual_order.refl length_pos_if_in_set 
      less_diff_conv2 nat_eq_iff2 nat_less_iff trans_le_add2)
    show ?thesis using False unfolding combineInputs.simps using Cons apply simp using 1
      by (simp add: Suc_diff_le combineInputs_length)
  qed
qed

text\<open>f: real list \<Rightarrow> real;
so this function is to update real list in combination(the new real list is for the basic block).
basic inputs vl1; additional inputs vl2; additional output v; basic real list xl1;
additional real list xl2; additional outupd f.
And the result list length = length vl1\<close>
fun replaceInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow>
real list \<Rightarrow> real list \<Rightarrow> outupd \<Rightarrow> real list" where
  "replaceInputs [] vl2 v xl1 xl2 f = []" |
  "replaceInputs (v1#vl1) vl2 v xl1 xl2 f = (if v1 = v then 
  (f xl2)#(replaceInputs vl1 vl2 v xl1 xl2 f)
  else (if (findPos vl2 v1 0) = -1 then (hd xl1)#(replaceInputs vl1 vl2 v (tl xl1) xl2 f) else 
  (xl2 ! nat (findPos vl2 v1 0))#(replaceInputs vl1 vl2 v xl1 xl2 f)))"

lemma replaceInputs_funeq: "h b t = f1 (map (\<lambda>a. h a t) a1) \<Longrightarrow> replaceInputs a2 a1 b
        (take (length (combineInputs a2 a1 b) - length a1) (map (\<lambda>a. h a t) (combineInputs a2 a1 b)))
        (drop (length (combineInputs a2 a1 b) - length a1) (map (\<lambda>a. h a t) (combineInputs a2 a1 b)))
        f1 = map (\<lambda>a. h a t) a2"
proof(induction a2)
  case Nil
  then show ?case by simp
next
  case (Cons a a2)
  then show ?case
  proof(cases "a = b")
    case True
    then show ?thesis unfolding replaceInputs.simps using Cons apply simp 
      using combineInputs_lengtheq[of a2 a1 b h t] by auto
  next
    case False
    note F1 = False
    then show ?thesis
    proof(cases "findPos a1 a 0 = -1")
      case True
      have 1: "a \<notin> set a1"
        using findPos_notin True by fastforce
      have 2: "hd (take (Suc (length (combineInputs a2 a1 b)) - length a1)
         (h a t # map (\<lambda>a. h a t) (combineInputs a2 a1 b))) = h a t"
        using combineInputs_length by (simp add: Suc_diff_le)
      have 3: "(tl (take (Suc (length (combineInputs a2 a1 b)) - length a1)
           (h a t # map (\<lambda>a. h a t) (combineInputs a2 a1 b)))) = 
        (take (length (combineInputs a2 a1 b) - length a1) (map (\<lambda>a. h a t) (combineInputs a2 a1 b)))"
        using combineInputs_length by (simp add: Suc_diff_le)
      have 4: "(drop (Suc (length (combineInputs a2 a1 b)) - length a1)
       (h a t # map (\<lambda>a. h a t) (combineInputs a2 a1 b))) = 
        (drop (length (combineInputs a2 a1 b) - length a1) (map (\<lambda>a. h a t) (combineInputs a2 a1 b)))"
        using combineInputs_length by (simp add: Suc_diff_le)
      show ?thesis using 1 2 3 4 F1 True unfolding replaceInputs.simps using Cons by simp
    next
      case False
      have 1: "a \<in> set a1"
        using findPos_in False by fastforce
      have 2: "(combineInputs a2 a1 b) !
    (length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) = a"
      using 1 combineInputs_ith by auto
    have 3: "(length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) \<ge> 0 \<and> 
      (length (combineInputs a2 a1 b) - length a1 + nat (findPos a1 a 0)) < length (combineInputs a2 a1 b)"
      using combineInputs_length findPos_lengthleq[of 0 a1 a] apply simp by (metis "1" add.commute
      add_mono_thms_linordered_field(3) dual_order.refl length_pos_if_in_set less_diff_conv2 
      nat_eq_iff2 nat_less_iff trans_le_add2)
      show ?thesis using 1 Cons False F1 unfolding replaceInputs.simps apply simp using 2 3 by auto
    qed
  qed
qed

fun removeSameInputs :: "var list \<Rightarrow> var list \<Rightarrow> real list  \<Rightarrow> real list \<Rightarrow> real list" where
  "removeSameInputs [] vl2 xl1 xl2 = []" |
  "removeSameInputs (v1#vl1) vl2 xl1 xl2 = (if (findPos vl2 v1 0) = -1 then 
  (hd xl1)#(removeSameInputs vl1 vl2 (tl xl1) xl2 ) else 
  (xl2 ! nat (findPos vl2 v1 0))#(removeSameInputs vl1 vl2 xl1 xl2))"

lemma removeSameInputs_eq: "(removeSameInputs a2 a1
        (take (length (combineInputs2 a2 a1) - length a1) (map (\<lambda>a. h a t) (combineInputs2 a2 a1)))
        (drop (length (combineInputs2 a2 a1) - length a1) (map (\<lambda>a. h a t) (combineInputs2 a2 a1))))
         = map (\<lambda>a. h a t) a2"
proof(induction a2)
  case Nil
  then show ?case by simp
next
  case (Cons a a2)
  then show ?case
  proof(cases "(findPos a1 a 0) = -1")
    case True
    have 1: "a \<notin> set a1"
      using findPos_notin True by fastforce
    have 2: "hd (take (Suc (length (combineInputs2 a2 a1)) - length a1)
         (h a t # map (\<lambda>a. h a t) (combineInputs2 a2 a1))) = h a t"
      using combineInputs2_length by (simp add: Suc_diff_le)
    have 3: "(tl (take (Suc (length (combineInputs2 a2 a1)) - length a1)
           (h a t # map (\<lambda>a. h a t) (combineInputs2 a2 a1)))) = 
          (take (length (combineInputs2 a2 a1) - length a1) 
          (map (\<lambda>a. h a t) (combineInputs2 a2 a1)))"
      using combineInputs2_length by (simp add: Suc_diff_le)
    have 4: "(drop (Suc (length (combineInputs2 a2 a1)) - length a1)
       (h a t # map (\<lambda>a. h a t) (combineInputs2 a2 a1))) = 
        (drop (length (combineInputs2 a2 a1) - length a1) 
        (map (\<lambda>a. h a t) (combineInputs2 a2 a1)))"
      using combineInputs2_length by (simp add: Suc_diff_le)
    show ?thesis using 1 Cons True unfolding removeSameInputs.simps apply simp using 2 3 4 by simp
  next
    case False
    have 1: "a \<in> set a1"
      using False findPos_in by fastforce
    have 2: "(combineInputs2 a2 a1) !
    (length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) = a"
      using 1 combineInputs2_ith by simp
    have 3: "(length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) \<ge> 0 \<and> 
      (length (combineInputs2 a2 a1) - length a1 + nat (findPos a1 a 0)) < length (combineInputs2 a2 a1)"
      using combineInputs2_length findPos_lengthleq[of 0 a1 a] apply simp by (metis "1" add.commute
          add_strict_right_mono length_pos_if_in_set less_diff_conv2 nat_eq_iff nat_less_iff trans_le_add2)
    show ?thesis using 1 Cons False unfolding removeSameInputs.simps apply simp using 2 3 by auto
  qed
qed

(*from the final real list to the final list for the basic outupd function,
here f is the additional function*)
fun splitInputs :: "var list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> real list \<Rightarrow> outupd \<Rightarrow> real list" where
  "splitInputs vl1 vl2 v xl f = replaceInputs vl1 vl2 v (take (length xl - length vl2) xl) 
  (drop (length xl - length vl2) xl) f"

fun splitInputs2 :: "var list \<Rightarrow> var list \<Rightarrow> real list \<Rightarrow> real list" where
  "splitInputs2 vl1 vl2 xl = removeSameInputs vl1 vl2 (take (length xl - length vl2) xl) 
  (drop (length xl - length vl2) xl)"


text\<open>when combination happens in two ODEs, we don't delete those produced inputs
and just combine those ODEs. So this function is for updating basic outupds when
combination happens in two ODEs.
"combineInputs a1 a2 (CHR '' '')" means that we don't delete those produced inputs and only
delete those same inputs, (CHR '' '') means a useless output not in basic inputs a1.
"(splitInputs a1 a2 (CHR '' '') s (\<lambda>x.0))" return the real list for f which only find the 
inputs for a1, so outupd "(\<lambda>x.0)" is useless.\<close>
fun reviseFun :: "outupd list \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> outupd list" where
  "reviseFun [] a1 a2 = []" |
  "reviseFun (f#fl) a1 a2 = (\<lambda>s. (if length s = length (combineInputs2 a2 a1) then
  (f (splitInputs2 a2 a1 s)) else 0))#(reviseFun fl a1 a2)"

lemma reviseFun_funeq: "\<forall>i. i \<ge> 0 \<and> i < length fl \<longrightarrow>
(reviseFun fl a1 a2 ! i) (map (\<lambda> a. h a t) (combineInputs2 a2 a1)) = (fl ! i) (map (\<lambda> a. h a t) a2)"
  apply clarify subgoal premises pre for i using pre
  proof(induction fl arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons f fl)
    then show ?case 
    proof(cases "i = 0")
      case True
      then show ?thesis unfolding reviseFun.simps apply simp using removeSameInputs_eq[of a2 a1 h t] 
          True by presburger
    next
      case False
      have 1: "i-1 \<ge> 0"
        using Cons by simp
      have 2: "reviseFun fl a1 a2 ! (i - 1) = reviseFun (f # fl) a1 a2 ! i"
        unfolding reviseFun.simps using 1 False by force
      have 3: "(f # fl) ! i = fl ! (i-1)"
        using False by force
      have 4: "i - 1 < length fl"
        using Cons by (simp add: False order_le_less)
      then show ?thesis using Cons(1)[of "i-1"] 1 2 3 by simp
    qed
  qed
  done

lemma reviseFunEq: "length (reviseFun fl a1 a2) = length fl"
proof(induction fl)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case unfolding reviseFun.simps by simp
qed

(*combine the function f1(calculation function) into the function list (f#f2), 
a1 is the initial input list, a2 is the additional input list, v is the output*)
fun updateFunc :: "outupd list \<Rightarrow> var list \<Rightarrow> var \<Rightarrow> outupd \<Rightarrow> var list \<Rightarrow> outupd list" where
  "updateFunc [] a1 v f1 a2 = []" |
  "updateFunc (f#f2) a1 v f1 a2 = (\<lambda>xl. (if length xl = length (combineInputs a1 a2 v)
  then (f (splitInputs a1 a2 v xl f1)) else 0))#(updateFunc f2 a1 v f1 a2)"

lemma updateFuncEq: "length (updateFunc fl a1 v f1 a2) = length fl"
proof(induction fl)
  case Nil
  then show ?case by simp
next
  case (Cons a fl)
  then show ?case by simp
qed

lemma updateFunc_funeq: "h b t = f1 (map (\<lambda>a. h a t) a1) \<Longrightarrow> i < length f2 \<and> i \<ge> 0 \<Longrightarrow>
(updateFunc f2 a2 b f1 a1 ! i) (map (\<lambda>a. h a t) (combineInputs a2 a1 b)) 
= (f2 ! i) (map (\<lambda>a. h a t) a2)"
proof(induction f2 arbitrary:i)
  case Nil
  then show ?case by simp
next
  case (Cons f f2)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis unfolding updateFunc.simps apply simp using Cons(2) 
        replaceInputs_funeq[of h b t f1 a1 a2] by auto
  next
    case False
    then show ?thesis unfolding updateFunc.simps using Cons(1)[of "i-1"] Cons(2,3) by fastforce
  qed
qed


(*combine the function f1(ODE) into the function list (f#f2), 
a1 is the initial input list, a2 is the additional input list*)
fun updateFunc2 :: "outupd list \<Rightarrow> var list \<Rightarrow> outupd \<Rightarrow> var list \<Rightarrow> outupd list" where
  "updateFunc2 fl a1 f1 a2 = reviseFun fl a1 a2 @[(\<lambda>s. (if length s = length (combineInputs2 a2 a1)
   then (f1 (drop (length s - length a1) s)) else 0))]"

value "combineInputs [CHR ''x'', CHR ''c''] [CHR ''a'', CHR ''b''] (CHR ''c'')"
value "splitInputs [CHR ''x'', CHR ''c''] [CHR ''a'', CHR ''b''] (CHR ''c'') [1,2,3] 
(\<lambda>s.(if length s = 2 then (s ! 0) * (s ! 1) else 0) )"

value "hd (updateFunc [\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0)] 
[CHR ''x'', CHR ''c''] (CHR ''c'') 
(\<lambda>s.(if length s = 2 then (s ! 0) * (s ! 1) else 0) ) [CHR ''a'', CHR ''b'']) [1,2,3] "

(*Combine the outputs when additional block is a computational block;
c is always 0 in this situation *)
fun variableSubstitute :: "var list \<Rightarrow> var \<Rightarrow> offset \<Rightarrow> outupd \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2) = (Block (combineInputs a2 a1 b) 
b2 c2 0 (updateFunc f2 a2 b f a1))"

lemma variableSubstitute_funeq: "h b t = f (map (\<lambda> a. h a t) a1) \<Longrightarrow>
\<forall>i. i \<ge> 0 \<and> i < length f2 \<longrightarrow>
((get_outupd (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2))) ! i) (map (\<lambda> a. h a t) 
(get_inputs (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2)))) = (f2 ! i) (map (\<lambda> a. h a t) a2)"
  apply clarify subgoal premises pre for i 
proof -
  show ?thesis using pre unfolding variableSubstitute.simps apply simp 
    unfolding reviseFun.simps using updateFunc_funeq[of h b t f a1 i f2 a2] by blast
qed
  done

lemma variableSubstituteSubset : "set (get_outputs (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2))) = set b2"
  unfolding variableSubstitute.simps by auto

lemma variableSubstituteSubset2 : "set b2 \<subseteq>set (get_outputs (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding variableSubstitute.simps by auto

lemma variableSubstituteSubset3 : "set (get_inputs (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2))) \<subseteq> set (a1@a2)"
proof(cases "b \<in> set b2")
  case True
  then show ?thesis unfolding variableSubstitute.simps using combineInputs_subset by auto
next
  case False
  then show ?thesis unfolding variableSubstitute.simps using combineInputs_subset by auto
qed

lemma variableSubstituteSubset5 : "set (get_inputs (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2))) \<subseteq> set a1 \<union> (set a2 - {b})"
unfolding variableSubstitute.simps using combineInputs_subset2 by auto

lemma variableSubstituteSubset4 : "set (get_inputs (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2))) \<subseteq> set (a1@a2)"
proof(cases "b \<in> set b2")
  case True
  then show ?thesis unfolding variableSubstitute.simps using combineInputs_subset by auto
next
  case False
  then show ?thesis unfolding variableSubstitute.simps using combineInputs_subset by auto
qed

lemma variableSubstituteOffsetsEq : "set c2 = {1} \<Longrightarrow> set (get_offsets (variableSubstitute 
a1 b c f (Block a2 b2 c2 d2 f2))) = {1}"
  unfolding variableSubstitute.simps by auto

lemma variableSubstituteEq : "length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outputs (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outupd (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding variableSubstitute.simps updateFunc.simps using updateFuncEq by force

(*Combine the outputs when additional block is a integrator block;
c is always 1 in this situation, means type integrator*)
fun combineIntegs :: "var list \<Rightarrow> var \<Rightarrow> offset \<Rightarrow> outupd \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "combineIntegs a1 b c f (Block a2 b2 c2 d2 f2) = (if b \<in> set b2 then (Block a2 b2 c2 0 f2)
else (Block (combineInputs2 a2 a1) (b2@[b]) (c2@[c]) 0 (updateFunc2 f2 a1 f a2)))"

lemma combineIntegs_funeq : "length b2 = length f2 \<Longrightarrow> b \<notin> set b2 \<Longrightarrow> 
\<forall>i. i \<ge> 0 \<and> i < length (get_outputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) - 1 \<longrightarrow>
((get_outupd (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) ! i) 
(map (\<lambda> a. h a t) (get_inputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2)))) = 
(f2 ! i) (map (\<lambda> a. h a t) a2)"
  apply clarify subgoal premises pre for i
proof -
  have 1: "(reviseFun f2 a1 a2 @
      [\<lambda>s. if length s = length (combineInputs2 a2 a1) then f (drop (length s - length a1) s) else 0]) !
     i = reviseFun f2 a1 a2 ! i"
    using reviseFunEq[of f2 a1 a2] pre(2,3,4) unfolding combineIntegs.simps 
    by (simp add: nth_append pre(1))
  show ?thesis using pre unfolding combineIntegs.simps apply simp 
    unfolding reviseFun.simps using reviseFun_funeq[of f2 a1 a2 h t] 1 by force
qed
  done

lemma combineIntegs_funeq2 : "length b2 = length f2 \<Longrightarrow> b \<notin> set b2 \<Longrightarrow> 
(last (get_outupd (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2)))) 
(map (\<lambda> a. h a t) (get_inputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2)))) = 
f (map (\<lambda> a. h a t) a1)"
  unfolding combineIntegs.simps apply simp using combineInputs2_valeq[of a2 a1 h t]
  by presburger

lemma combineIntegs_funeq3 : "length b2 = length f2 \<Longrightarrow> b \<in> set b2 \<Longrightarrow> 
\<forall>i. i \<ge> 0 \<and> i < length (get_outputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) \<longrightarrow>
((get_outupd (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) ! i) 
(map (\<lambda> a. h a t) (get_inputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2)))) = 
(f2 ! i) (map (\<lambda> a. h a t) a2)"
  unfolding combineIntegs.simps by simp


lemma combineIntegsSubset : "set (get_outputs (combineIntegs 
a1 b c f (Block a2 b2 c2 d2 f2))) = set (b#b2)"
  unfolding variableSubstitute.simps by auto

lemma combineIntegsSubset2 : "set b2 \<subseteq> set (get_outputs (combineIntegs 
a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding variableSubstitute.simps by auto

lemma combineIntegsSubset3 : "set (get_inputs (combineIntegs 
a1 b c f (Block a2 b2 c2 d2 f2))) \<subseteq> set (a1@a2)"
proof(cases "b \<in> set b2")
  case True
  then show ?thesis unfolding combineIntegs.simps using combineInputs2_subset by auto
next
  case False
  then show ?thesis unfolding combineIntegs.simps using combineInputs2_subset by auto
qed

lemma combineIntegsEq : "length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outputs (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) =
length (get_outupd (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2)))"
  unfolding combineIntegs.simps updateFunc2.simps using reviseFunEq by force

(*Combine additional block "(Block a1 b1 c1 d1 f1)"
into the basic block "(Block a2 b2 c2 d2 f2)",
note: d1 = d2 = 0*)

\<comment> \<open>key function for combination!!!\<close>
fun combineOneBlock :: "var list \<Rightarrow> var list \<Rightarrow> offset list \<Rightarrow> outupd list \<Rightarrow> 
  ConBlk \<Rightarrow> ConBlk" where
  "combineOneBlock a1 [] c1 f1 (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 b1 [] f1 (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 b1 c1 [] (Block a2 b2 c2 d2 f2) = (Block a2 b2 c2 0 f2)" |
  "combineOneBlock a1 (b#b1) (c#c1) (f#f1) (Block a2 b2 c2 d2 f2) = (if c = 1 then
  (combineOneBlock a1 b1 c1 f1 (combineIntegs a1 b c f (Block a2 b2 c2 d2 f2))) 
  else combineOneBlock a1 b1 c1 f1 (variableSubstitute a1 b c f (Block a2 b2 c2 d2 f2)))"

lemma combineOneBlock_Inputssubset: 
"set (get_inputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<subseteq> set (a1@a2)"
proof(induction b1 arbitrary: c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by simp
  next
    case False
    note F1 = False
    have 1: "c1 = hd c1 # tl c1"
      using F1 by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using F1 by (metis combineOneBlock.simps(3) get_inputs.simps 
            list_encode.cases set_append sup.cobounded2)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
      using False by simp
    then show ?thesis
    proof(cases "hd c1 = 1")
      case True
      have 3: "combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2) = Block
      (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_sample_time (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        by auto
      then show ?thesis using True combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1" "tl f1"
          a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "(get_inputs (combineIntegs a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outputs (combineIntegs a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_offsets (combineIntegs a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_sample_time (combineIntegs a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outupd (combineIntegs a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))"] combineIntegsSubset3 1 2 by fastforce
    next
      case False
      have 4: "variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2) = Block
      (get_inputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_offsets (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outupd (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        by auto
      then show ?thesis using False combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1" "tl f1"
          a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "(get_inputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_offsets (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outupd (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))"] variableSubstituteSubset3 1 2 by fastforce
    qed
    qed
  qed
qed

lemma combineOneBlock_Inputssubset2: " length c1 = length b1 \<and> length c1 = length f1 \<Longrightarrow> 
\<forall>c \<in> set c1. c = 0 \<Longrightarrow>
set (get_inputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<subseteq> set a1 \<union> (set a2 - set b1)"
proof(induction b1 arbitrary: c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons.prems(1) by force
  next
    case False
    note F1 = False
    have 1: "c1 = hd c1 # tl c1"
      using F1 by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using F1 using Cons.prems(1) by force
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(3) F1 list.set_sel(1) by blast
      have 4: "variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2) = Block
      (get_inputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_offsets (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outupd (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        by auto
      have 5: "set a1 \<union> (set (get_inputs (variableSubstitute a1 b (hd c1) (hd f1) 
      (Block a2 b2 c2 d2 f2))) - set b1) \<subseteq> set a1 \<union> (set a2 - set (b # b1))"
        using variableSubstituteSubset5[of a1 b "hd c1" "hd f1" a2 b2 c2 d2 f2] 
        using Diff_insert0 Un_iff insertCI insert_Diff1 insert_Diff_single insert_absorb by auto
    then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1" "tl f1"
          a2 b2 c2 d2 f2] Cons(1)[of "tl c1" "tl f1" "(get_inputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_offsets (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outupd (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))"] 5 by (smt (verit, del_insts) "1" "2" "3" "4" Cons.prems(1) 
          Cons.prems(2) F1 le_numeral_extra(3) length_tl list.sel(3) list.set_sel(2) 
          not_one_le_zero order_trans)
  qed
qed
qed

lemma combineOneBlock_funeq2: "length c1 = length b1 \<Longrightarrow> length c1 = length f1 \<Longrightarrow>
\<forall>x \<in> set c1. x = 0 \<Longrightarrow> \<forall>i < length b1.
          h (b1 ! i) t = (f1 ! i) (map (\<lambda>a. h a t) a1) \<Longrightarrow> \<forall>j < length f2.
(get_outupd (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) ! j)
     (map (\<lambda>a. h a t) (get_inputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)))) = 
    (f2 ! j) (map (\<lambda>a. h a t) a2)"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons.prems(2) by force
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(4) 1 by (metis list.set_intros(1))
      have 4: "length (get_outupd (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) =
            length f2"
        unfolding variableSubstitute.simps using updateFuncEq by auto
      have 5: "length (tl c1) = length b1"
        using 1 Cons(2) by auto
      have 6: "length (tl c1) = length (tl f1)"
        using 2 Cons(3) by auto
      have 7: "\<forall>x\<in>set (tl c1). x = 0"
        using Cons(4) 1 by (metis list.distinct(1) list.set_sel(2))
      have 8: "\<forall>i<length b1. h (b1 ! i) t = (tl f1 ! i) (map (\<lambda>a. h a t) a1)"
        using Cons(5) by (metis "5" "6" Suc_less_eq length_Cons nth_Cons_Suc nth_tl)
      have 9: "\<forall>j<length f2.(get_outupd (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! j)
        (map (\<lambda>a. h a t)
          (get_inputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))) = 
          (f2 ! j) (map (\<lambda>a. h a t) a2)"
      proof -
        have tmp1: "h b t = hd f1 (map (\<lambda>a. h a t) a1)"
          using Cons(5) by (metis "2" length_greater_0_conv list.distinct(1) nth_Cons_0)
        then show ?thesis using variableSubstitute_funeq[of h b t 
              "hd f1" a1 f2 "(hd c1)" a2 b2 c2 d2] by auto
      qed
      have 10: "variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2) = Block
      (get_inputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_offsets (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
      (get_outupd (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        by auto
      then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] using Cons(1)[of "tl c1" "tl f1" "(get_outupd (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_inputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_outputs (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_offsets (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" "(get_sample_time (variableSubstitute a1 b (hd c1) (hd f1) 
          (Block a2 b2 c2 d2 f2)))" ] 1 2 3 4 5 6 7 8 9 by simp
    qed
  qed
qed

lemma combineOneBlock_lengtheq: "length c1 = length b1 \<Longrightarrow> length c1 = length f1 \<Longrightarrow>
\<forall>x \<in> set c1. x = 0 \<Longrightarrow> length (get_outupd (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = 
length f2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons.prems(2) by force
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(4) by (metis "1" list.set_intros(1))
      then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons updateFuncEq by (metis False le_numeral_extra(3) 
            length_0_conv length_tl list.sel(3) list.set_sel(2) not_one_le_zero 
            variableSubstitute.simps)
    qed
  qed
qed

lemma combineOneBlockSubset : "set (get_outputs (combineOneBlock a1 b1 c1 f1 
(Block a2 b2 c2 d2 f2))) \<subseteq> set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps 
            subset_refl sup.coboundedI2)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "get_inputs 
              ((combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
              "get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))"] 
            combineIntegsSubset by (smt (verit, del_insts) UnE UnI2 Un_commute 
              combineIntegs.simps dual_order.trans get_outputs.simps hd_in_set list.discI 
              list.sel(1) local.Cons set_ConsD set_subset_Cons subset_iff sup.orderE sup_mono)
          
      next
        case False
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons[of "tl c1" "tl f1" "get_inputs 
              ((variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
              "get_outputs (variableSubstitute a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))"] 
            variableSubstituteSubset by (metis Un_mono variableSubstitute.simps 
              equalityE local.Cons order_trans set_subset_Cons)
      qed
    qed
  qed
qed

lemma combineOneBlockSubset2 : "set b2 \<subseteq> set (get_outputs (combineOneBlock a1 b1 c1 f1 
(Block a2 b2 c2 d2 f2)))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps subset_refl)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons combineIntegsSubset2 by force
      next
        case False
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons variableSubstituteSubset2 by force 
      qed
    qed
  qed
qed

lemma combineOneBlockSubset3 : "set c1 = {0} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(2) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (variableSubstitute a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set b2"
        using variableSubstituteSubset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by simp
        next
          case False
          then show ?thesis using 1 2 3 4 T combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by (metis combineOneBlock.simps(2) variableSubstitute.simps 
                get_outputs.simps le_zero_eq list.collapse not_one_le_zero)
        qed
      next
        case False
        have 5: "set (tl c1) = {0}"
          using False Cons(2) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons by simp
      qed
    qed
  qed
qed

lemma combineOneBlockOutputseq: "set c1 = {0} \<Longrightarrow>
 get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) = b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis by (metis "1" combineOneBlock.simps(3) get_outputs.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 0"
        using Cons(2) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (variableSubstitute a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set b2"
        using variableSubstituteSubset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by simp
        next
          case False
          then show ?thesis using 1 2 3 4 T combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by (metis combineOneBlock.simps(2) variableSubstitute.simps 
                get_outputs.simps le_zero_eq list.collapse not_one_le_zero)
        qed
      next
        case False
        have 5: "set (tl c1) = {0}"
          using False Cons(2) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons by simp
      qed
    qed
  qed
qed

lemma combineOneBlockSubset4 : "set c1 = {} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b2"
proof(induction b1)
  case Nil
  then show ?case by simp
next
  case (Cons a b1)
  then show ?case using Cons(2) by simp
qed

lemma combineOneBlockSubset5 : "Available' (Block a1 b1 c1 d1 f1) \<Longrightarrow> set c1 = {1} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) unfolding Available'_def by simp
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(3) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (combineIntegs a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set (b#b2)"
        using combineIntegsSubset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by auto
        next
          case False                       
          then show ?thesis using 1 2 3 4 T Cons(2) unfolding Available'_def by force
        qed
      next
        case False
        note F1 = False
        have 5: "set (tl c1) = {1}"
          using False Cons(3) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def by (metis 
                get_offsets.simps get_outputs.simps length_greater_0_conv length_tl list.sel(3))
        next
          case False
          note F2 = False
          then show ?thesis
          proof(cases "tl f1 = []")
            case True
            then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def
              by (metis get_outputs.simps get_outupd.simps length_0_conv length_tl list.sel(3))
          next
            case False
            have 6: "Available' (Block a1 b1 (tl c1) d1 (tl f1))"
              using Cons(2) 1 2 F1 F2 False unfolding Available'_def by (metis "5" Suc_less_eq 
                  bot_nat_0.extremum get_offsets.simps get_outputs.simps get_outupd.simps 
                  get_sample_time.simps insert_iff length_Cons length_tl list.sel(3) nth_Cons_Suc)
            have 7: "set (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
            (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
              using Cons(1) 5 6 by presburger
            then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] "5" "6" Cons.IH by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma combineOneBlockEq : "length c1 = length b1 \<and> length c1 = length f1  \<Longrightarrow> set c1 = {1} \<Longrightarrow>
 set (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) by force
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(3) by (metis "1" list.set_intros(1) singleton_iff)
      have 4: "set (get_outputs (combineIntegs a1 b (hd c1) (hd f1) 
    (Block a2 b2 c2 d2 f2))) = set (b#b2)"
        using combineIntegsSubset by simp
      then show ?thesis
      proof(cases "tl c1 = []")
        case True
        note T = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] by auto
        next
          case False                       
          then show ?thesis using 1 2 3 4 T Cons(2) unfolding Available'_def by force
        qed
      next
        case False
        note F1 = False
        have 5: "set (tl c1) = {1}"
          using False Cons(3) by (metis "1" set_empty2 set_subset_Cons subset_singletonD)
        then show ?thesis
        proof(cases "b1 = []")
          case True
          then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def by (metis 
                length_greater_0_conv length_tl list.sel(3))
        next
          case False
          note F2 = False
          then show ?thesis
          proof(cases "tl f1 = []")
            case True
            then show ?thesis using 1 2 3 4 False Cons(2) unfolding Available'_def
              by (metis length_0_conv length_tl list.sel(3))
          next
            case False
            have 6: "length b1 = length (tl c1) \<and> length b1 = length (tl f1)"
              using Cons(2) 1 2 F1 F2 False by force
            have 7: "set (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
            (Block a2 b2 c2 d2 f2))) = set b1 \<union> set b2"
              using Cons(1) 5 6 by simp
            then show ?thesis using 1 2 3 4 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] "5" "6" Cons.IH by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma combineOneBlockEq2: "length b1 = length c1 \<and> length b1 = length f1 \<Longrightarrow>
length b2 = length c2 \<and> length b2 = length f2 \<Longrightarrow>
length (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = 
length (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<and>
length (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = 
length (get_outupd (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(2) by simp
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) by simp
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons 1 2 combineIntegsEq by (smt (verit, best) 
              combineIntegs.simps get_offsets.simps get_outputs.simps get_outupd.simps 
              length_tl list.sel(3))
      next
        case False
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons variableSubstituteEq "1" "2" by (metis (no_types, lifting) 
              variableSubstitute.simps length_tl list.sel(3) updateFuncEq)
      qed
    qed
  qed
qed

lemma combineOneBlock_Integeq: "\<forall>x \<in> set c1. x = 1 \<Longrightarrow> length c1 = length b1 \<Longrightarrow>
length c1 = length f1 \<Longrightarrow> length c2 = length b2 \<Longrightarrow> length c2 = length f2 \<Longrightarrow>
(\<forall>i j. i < j \<and> j < length (get_outputs (Block a2 b2 c2 d2 f2))
\<longrightarrow> (get_outputs (Block a2 b2 c2 d2 f2)) ! i \<noteq> (get_outputs (Block a2 b2 c2 d2 f2)) ! j) \<Longrightarrow> 
i < length b2 \<Longrightarrow> j < length (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<Longrightarrow>
b2 ! i = get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) ! j \<Longrightarrow>
(f2 ! i) (map (\<lambda>a. h a t) a2) = 
    (get_outupd
      (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) ! j)
     (map (\<lambda>a. h a t)
       (get_inputs
         (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2 i)
  case Nil
  then show ?case by (metis combineOneBlock.simps(1) get_inputs.simps get_outputs.simps 
        get_outupd.simps nat_neq_iff)
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(3,9) by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(3,4,9) by auto
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(2) 1 by (metis list.set_intros(1))
      have 4: "\<forall>x\<in>set (tl c1). x = 1"
        using Cons(2) 1 by (metis list.set_intros(2))
      have 5: "length (tl c1) = length b1"
        using Cons(3) 1 by simp
      have 6: "length (tl c1) = length (tl f1)"
        using Cons(4) 1 2 by simp
      have 7: "length (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) =
    length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        using Cons(5) by auto
      have 8: "length (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) =
    length (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        using Cons(6) by (metis Cons.prems(4) combineIntegsEq)
      have 9: "j < length
         (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
           (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))))"
        using Cons(9) by (metis "1" "2" "3" combineOneBlock.simps(4))
      have 13: "\<forall>i j. i < j \<and> j < length
               (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) \<longrightarrow>
          get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i \<noteq>
          get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! j"
          proof(cases "b \<in> set b2")
            case True
            then show ?thesis using Cons(7) unfolding combineIntegs.simps by auto
          next
            case False
            then show ?thesis using Cons(7) unfolding combineIntegs.simps apply simp by (smt 
         (verit, best) Suc_less_eq less_Suc_eq less_trans_Suc nth_append nth_append_length nth_mem)
          qed
      have 15: "(combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) = (Block 
                   (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_sample_time (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))))"
        by auto
      have 16: "get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i =
                    get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
                    (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j"
        using Cons(10) combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
          "tl f1" a2 b2 c2 d2 f2 ] 3 by (metis "1" "2" Cons.prems(7) combineIntegs.simps 
          get_outputs.simps nth_append)
      then show ?thesis
      proof(cases "i = 0")
        case True
        note T1 = True
        then show ?thesis
        proof(cases "b1 = []")
          case True
          have 10: "combineOneBlock a1 (b # b1) c1 f1 (Block a2 b2 c2 d2 f2) =
                    combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)"
          proof -
            have tmp1: "combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2) = Block 
            (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
            (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
            (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) 0
            (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
              by auto
            show ?thesis using tmp1 True combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2 ] 1 2 3 by simp
          qed
          then show ?thesis
          proof(cases "b \<in> set b2")
            case True
            have 11: "i = j"
              using Cons(7,10) T1 10 unfolding combineIntegs.simps 
              using Cons.prems(8) True by force
            then show ?thesis using T1 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2 ] combineIntegs_funeq3[of b2 f2 b a1 "(hd c1)" "(hd f1)" a2
              c2 d2 h t] 10 by (simp add: True)
          next
            case False
            have 11: "i = j"
              using Cons(7,10) T1 10 False unfolding combineIntegs.simps 
              using Cons.prems(8) by (metis One_nat_def Suc_eq_plus1 bot_nat_0.not_eq_extremum 
                  get_outputs.simps in_set_conv_nth length_Cons length_append less_Suc_eq 
                  list.size(3) nth_append nth_append_length)
            have 12: "length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) - 1 > 0"
              using Cons(8) T1 False by simp
            then show ?thesis using False T1 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2 ] 10 11 combineIntegs_funeq[of b2 f2 b a1 "(hd c1)" "(hd f1)" a2
              c2 d2 h t] using Cons.prems(4) Cons.prems(5) by auto
          qed
        next
          case False
          have 14: "i < length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
            using T1 unfolding combineIntegs.simps by auto
          have 17: "(get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i)
     (map (\<lambda>a. h a t) (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))) = 
          (f2 ! i) (map (\<lambda>a. h a t) a2)"
            using combineIntegs_funeq[of b2 f2 b a1 "hd c1" "hd f1" a2 c2 d2 h t] 
            combineIntegs_funeq3[of b2 f2 b a1 "hd c1" "hd f1" a2 c2 d2 h t] unfolding 
              combineIntegs.simps using Cons.prems(4) Cons.prems(5) Cons.prems(7) by auto
          have 18: "(get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i)
     (map (\<lambda>a. h a t) (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))) =
    (get_outupd (combineOneBlock a1 b1 (tl c1) (tl f1) 
      (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j)
     (map (\<lambda>a. h a t) (get_inputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
      (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))))"
            using 1 2 3 4 5 6 7 8 9 Cons(1)[of "tl c1" "tl f1" "get_offsets ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outputs ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outupd ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_inputs (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_sample_time (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" i] False 13 14 15 16 
            by presburger
          then show ?thesis using 1 2 3 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2 ] 17 by auto
        qed
      next
        case False
        have 14: "i < length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
          using Cons(8) unfolding combineIntegs.simps by auto
        have 17: "(get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i)
     (map (\<lambda>a. h a t) (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))) = 
          (f2 ! i) (map (\<lambda>a. h a t) a2)"
            using combineIntegs_funeq[of b2 f2 b a1 "hd c1" "hd f1" a2 c2 d2 h t] 
            combineIntegs_funeq3[of b2 f2 b a1 "hd c1" "hd f1" a2 c2 d2 h t] unfolding 
              combineIntegs.simps using Cons.prems(4) Cons.prems(5) Cons.prems(7) by auto
        have 18: "(get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i)
     (map (\<lambda>a. h a t) (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))) =
    (get_outupd (combineOneBlock a1 b1 (tl c1) (tl f1) 
      (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j)
     (map (\<lambda>a. h a t) (get_inputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
      (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))))"
            using 1 2 3 4 5 6 7 8 9 Cons(1)[of "tl c1" "tl f1" "get_offsets ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outputs ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outupd ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_inputs (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_sample_time (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" i] False 13 14 15 16 
            by presburger
        then show ?thesis using 1 2 3 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2 ] 17 by auto
      qed
    qed
  qed
qed

lemma combineOneBlock_Integeq2: "\<forall>x \<in> set c1. x = 1 \<Longrightarrow> length c1 = length b1 \<Longrightarrow>
length c1 = length f1 \<Longrightarrow> length c2 = length b2 \<Longrightarrow> length c2 = length f2 \<Longrightarrow> set b1 \<inter> set b2 = {} \<Longrightarrow>
(\<forall>i j. i < j \<and> j < length (get_outputs (Block a2 b2 c2 d2 f2))
\<longrightarrow> (get_outputs (Block a2 b2 c2 d2 f2)) ! i \<noteq> (get_outputs (Block a2 b2 c2 d2 f2)) ! j) \<Longrightarrow> 
\<forall>i j. i < j \<and> j < length b1 \<longrightarrow> b1 ! i \<noteq> b1 ! j \<Longrightarrow> 
i < length b1 \<Longrightarrow> j < length (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) \<Longrightarrow>
b1 ! i = get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) ! j \<Longrightarrow>
(f1 ! i) (map (\<lambda>a. h a t) a1) = 
    (get_outupd
      (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)) ! j)
     (map (\<lambda>a. h a t)
       (get_inputs
         (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))))"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2 i)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(3,7,10) by auto
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(3,4,7,10) by auto
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      have 3: "hd c1 = 1"
        using Cons(2) 1 by (metis list.set_intros(1))
      have 4: "(combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) = (Block 
                   (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_sample_time (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))
                   (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))))"
        by auto
      have 5: "b \<notin> set b2"
        using Cons(7) by auto
      have 6: "\<forall>x\<in>set (tl c1). x = 1"
        using Cons(2) 1 by (metis list.set_intros(2))
      have 7: "length (tl c1) = length b1"
        using Cons(3) 1 by simp
      have 8: "length (tl c1) = length (tl f1)"
        using Cons(4) 1 2 by simp
      have 9: "length (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) =
    length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        using Cons(5) by auto
      have 10: "length (get_offsets (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) =
    length (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
        using Cons(6) by (metis Cons.prems(4) combineIntegsEq)
      have 11: "j < length
         (get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
           (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))))"
        using Cons(11) by (metis "1" "2" "3" combineOneBlock.simps(4))
      then show ?thesis
      proof(cases "i = 0")
        case True
        have 12: "(hd f1) (map (\<lambda>a. h a t) a1) = (get_outupd 
     (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! (length f2))
     (map (\<lambda>a. h a t) (get_inputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))))"
        proof -
          have tmp1: "get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! (length f2) =
            last (get_outupd (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
            unfolding combineIntegs.simps 5 by (smt (verit, best) "5" get_outupd.simps last_snoc 
                nth_append_length reviseFunEq updateFunc2.simps)
          then show ?thesis using combineIntegs_funeq2[of b2 f2 b a1 "(hd c1)" "(hd f1)" a2
                c2 d2 h t] 5 Cons(6) Cons.prems(4) by auto
        qed
        have 13: "length f2 < length (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))"
          unfolding combineIntegs.simps using 5 Cons.prems(4) Cons.prems(5) by force
        have 14: "get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! length f2 =
                  get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
                  (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j"
          using Cons(12) True 5 1 2 3 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] unfolding combineIntegs.simps 
          using Cons.prems(4) Cons.prems(5) by force
        then show ?thesis using 1 2 3 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] combineOneBlock_Integeq[of "tl c1" b1 "tl f1" "get_offsets ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outputs ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outupd ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_inputs (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_sample_time (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(length f2)" j a1 h t] 4 5 6 7 8 9 10 11
              12 13 by (smt (z3) Cons.prems(11) Cons.prems(7) One_nat_def Suc_eq_plus1 
              Suc_less_eq True combineIntegs.simps get_outputs.simps in_set_conv_nth length_Cons 
              length_append less_SucE less_trans_Suc list.size(3) nth_Cons_0 nth_append)
      next
        case False
        have 15: "set b1 \<inter> set (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) = {}"
        proof -
          have tmp: "set b1 \<inter> set (b2 @ [b]) = {}"
            using Cons(7,9) 5 by (smt (verit, ccfv_threshold) Un_iff 
          disjoint_iff_not_equal empty_set in_set_conv_nth length_Cons less_Suc_eq less_trans_Suc 
          list.sel(3) list.simps(15) nth_Cons_0 nth_tl set_append singletonD zero_less_Suc)
          then show ?thesis using 5 unfolding combineIntegs.simps by auto
        qed
        have 16: "\<forall>i j. i < j \<and> j < length
               (get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) \<longrightarrow>
          get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! i \<noteq>
          get_outputs (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)) ! j"
        proof(cases "b \<in> set b2")
            case True
            then show ?thesis using Cons(8) unfolding combineIntegs.simps by auto
          next
            case False
            then show ?thesis using Cons(8) unfolding combineIntegs.simps apply simp by (smt 
         (verit, best) Suc_less_eq less_Suc_eq less_trans_Suc nth_append nth_append_length nth_mem)
        qed
        have 17: "\<forall>i j. i < j \<and> j < length b1 \<longrightarrow> b1 ! i \<noteq> b1 ! j"
          using Cons(9) by (metis Suc_less_eq length_Cons nth_Cons_Suc)
        have 18: "i - 1 < length b1"
          using Cons(10) False by auto
        have 19: "b1 ! (i - 1) = get_outputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
          (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j"
          using Cons(12) combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] "1" "2" "3" False by force
        have 20: "(tl f1 ! (i - 1)) (map (\<lambda>a. h a t) a1) = (get_outupd (combineOneBlock a1 b1 (tl c1) (tl f1) 
          (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2))) ! j) (map (\<lambda>a. h a t)
         (get_inputs (combineOneBlock a1 b1 (tl c1) (tl f1) 
          (combineIntegs a1 b (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))))"
          using Cons(1)[of "tl c1" "tl f1" "get_offsets ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outputs ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "get_outupd ((combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_inputs (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "(get_sample_time (combineIntegs a1 b 
               (hd c1) (hd f1) (Block a2 b2 c2 d2 f2)))" "i-1"] 1 2 3 4 5 6 7 8 9 10 11 
              15 16 17 18 19 by presburger
        have 21: "(f1 ! i) (map (\<lambda>a. h a t) a1) = (tl f1 ! (i - 1)) (map (\<lambda>a. h a t) a1)"
          using 2 False by (metis nth_Cons')
        then show ?thesis using 1 2 combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] 20 3 by presburger
      qed
    qed
  qed
qed

lemma combineOneBlockOffsetsEq : "set c2 = {1} \<Longrightarrow>
set (get_offsets (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) = {1}"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(2) by simp
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) 1 by (metis combineOneBlock.simps(3) get_offsets.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis 
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons 1 2 by auto
      next
        case False
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons variableSubstituteOffsetsEq "1" "2" by auto
      qed
    qed
  qed
qed

lemma combineOneBlock_noteq: "(\<forall>i j. i < j \<and> j < length (get_outputs (Block a2 b2 c2 d2 f2))
\<longrightarrow> (get_outputs (Block a2 b2 c2 d2 f2)) ! i \<noteq> (get_outputs (Block a2 b2 c2 d2 f2)) ! j) \<Longrightarrow> 
(\<forall>i j. i < j \<and> j < length (get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2)))\<longrightarrow>
(get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) ! i \<noteq>
(get_outputs (combineOneBlock a1 b1 c1 f1 (Block a2 b2 c2 d2 f2))) ! j)"
proof(induction b1 arbitrary:c1 f1 a2 b2 c2 d2 f2)
  case Nil
  then show ?case using combineOneBlock.simps(1) by simp
next
  case (Cons b b1)
  then show ?case
  proof(cases "c1 = []")
    case True
    then show ?thesis using Cons(2) combineOneBlock.simps(2) by simp
  next
    case False
    have 1: "c1 = hd c1 # tl c1"
      using False by simp
    then show ?thesis
    proof(cases "f1 = []")
      case True
      then show ?thesis using Cons(2) 1 combineOneBlock.simps(3) by (metis get_outputs.simps)
    next
      case False
      have 2: "f1 = hd f1 # tl f1"
        using False by simp
      then show ?thesis 
      proof(cases "hd c1 = 1")
        case True
        then show ?thesis
        proof(cases "b \<in> set b2")
          case True
          then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons 1 2 unfolding combineIntegs.simps updateFunc2.simps 
            by simp
        next
          case False
          then show ?thesis using True combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons(1)[of "(combineInputs2 a2 a1)" "(b2 @ [b])" "(c2 @ [Suc 0])" 
              0 "(reviseFun f2 a1 a2 @ [\<lambda>s. if length s = length (combineInputs2 a2 a1)
              then hd f1 (drop (length s - length a1) s) else 0])" "tl c1" "tl f1"] Cons(2) 
            1 2 unfolding combineIntegs.simps by (smt (z3) Cons.IH Suc_pred add_diff_cancel_right' 
                get_outputs.simps in_set_conv_nth length_Cons length_append length_greater_0_conv 
                less_Suc_eq less_trans_Suc list.discI not_less_eq nth_append nth_append_length)
        qed
      next
        case False
        then show ?thesis using combineOneBlock.simps(4)[of a1 b b1 "hd c1" "tl c1" "hd f1"
              "tl f1" a2 b2 c2 d2 f2] Cons(1)[of "(combineInputs2 a2 a1)" "(b2 @ [b])" "(c2 @ [Suc 0])" 
              0 "(reviseFun f2 a1 a2 @ [\<lambda>s. if length s = length (combineInputs2 a2 a1)
              then hd f1 (drop (length s - length a1) s) else 0])" "tl c1" "tl f1"] Cons(2) 
            1 2 unfolding variableSubstitute.simps by (smt (z3) Cons.IH Suc_pred add_diff_cancel_right' 
                get_outputs.simps in_set_conv_nth length_Cons length_append length_greater_0_conv 
                less_Suc_eq less_trans_Suc list.discI not_less_eq nth_append nth_append_length)
      qed
    qed
  qed
qed

(*Combine additional block list "al" into a basic block "b"*)
fun combineBlocks :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> ConBlk" where
  "combineBlocks [] b = b" |
  "combineBlocks (a#al) b = combineBlocks al (combineOneBlock (get_inputs a) 
  (get_outputs a) (get_offsets a) (get_outupd a) b)"

lemma combineBlocks_Inputssubset: "set (get_inputs (combineBlocks al b)) \<subseteq> Inputs (b#al)"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by auto
next
  case (Cons a al)
  have 1: "set (get_inputs (combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) b)) \<subseteq> Inputs (b#[a])"
    using combineOneBlock_Inputssubset unfolding Inputs.simps by (metis (no_types, opaque_lifting) 
        get_inputs.simps get_outupd.elims set_append sup_bot_left sup_commute)
  then show ?case unfolding combineBlocks.simps using Cons[of "(combineOneBlock 
  (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"] by auto
qed

lemma combineBlocks_Inputssubset2: "\<forall>b \<in> set al. set (get_offsets b) = {0} \<Longrightarrow>
 \<forall>b \<in> set al. Available' b \<Longrightarrow>  besorted2 (rev al) \<Longrightarrow>
set (get_inputs (combineBlocks al b)) \<subseteq> Inputs (b#al) - Outputs al"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "set (get_inputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
   b)) \<subseteq> set (get_inputs a)\<union> (set (get_inputs b) - set (get_outputs a))"
    using combineOneBlock_Inputssubset2 Cons(2,3) unfolding Available'_def by (metis (no_types, 
  opaque_lifting) all_not_in_conv get_inputs.simps get_outupd.elims insert_iff list.set_intros(1))
  have 2: "set (get_inputs a) \<union> (set (get_inputs b) - set (get_outputs a)) = 
      set (get_inputs a) \<union> set (get_inputs b) - set (get_outputs a)"
    using Cons(2,3) unfolding Available'_def by (metis Diff_Int2 Diff_empty Un_Diff Un_Int_eq(1) 
    insert_absorb insert_iff insert_not_empty less_numeral_extra(4) less_one list.set_intros(1))
  have 3: "set (get_outputs a) \<inter> Inputs al = {}"
    using besorted2_last2 Cons(4) by (metis Inputs_rev rev.simps(2))
  have 4: "(set (get_inputs a) \<union> set (get_inputs b) - set (get_outputs a)) \<union> Inputs al = 
    set (get_inputs a) \<union> set (get_inputs b) \<union> Inputs al - set (get_outputs a)"
    using 3 by blast
  have 5: "Inputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b # al) -
      Outputs al \<subseteq> Inputs (b # a # al) - Outputs (a # al)"
    using 1 2 unfolding Inputs.simps Outputs.simps using 4 by blast
  then show ?case unfolding combineBlocks.simps using Cons(1)[of "(combineOneBlock 
  (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"] Cons(2,3,4) besorted2_last by auto
qed

lemma combineBlocks_zero: "\<forall>x \<in> set al. length (get_outputs x) = length (get_offsets x) \<Longrightarrow>
\<forall>x \<in> set al. length (get_outupd x) = length (get_offsets x) \<Longrightarrow>
\<forall>x \<in> set al. set (get_offsets x) = {0} \<Longrightarrow> \<forall>b \<in> set al. 
\<forall>i < length (get_outputs b).
h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda> a. h a t) (get_inputs b)) \<Longrightarrow>
\<forall>j < length (get_outupd c).
(get_outupd c ! j) (map (\<lambda>a. h a t) (get_inputs c)) = (get_outupd (
(combineBlocks al c)) ! j) (map (\<lambda>a. h a t) (get_inputs (combineBlocks al c)))"
proof(induction al arbitrary: c)
  case Nil
  then show ?case by auto
next
  case (Cons a al)
  have 1: "\<forall>x \<in> set al. length (get_outputs x) = length (get_offsets x)"
    using Cons(2) by auto
  have 2: "\<forall>x \<in> set al. length (get_outupd x) = length (get_offsets x)"
    using Cons(3) by auto
  have 3: "\<forall>x\<in>set al. set (get_offsets x) = {0}"
    using Cons(4) by simp
  have 4: "\<forall>b\<in>set al. \<forall>i < length (get_outputs b). h (get_outputs b ! i) t 
      = (get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b))"
    using Cons(5) by simp
  have 5: "length (get_outupd c) = length (get_outupd
          (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))"
  proof -
    have tmp1: "length (get_offsets a) = length (get_outputs a)"
      using Cons(2) by auto
    have tmp2: "length (get_offsets a) = length (get_outupd a)"
      using Cons(3) by auto
    have tmp3: "\<forall>x\<in>set (get_offsets a). x = 0"
      using Cons(4) by auto
    show ?thesis using combineOneBlock_lengtheq[of "(get_offsets a)" "get_outputs a" "get_outupd a"
          "get_inputs a" "(get_inputs c)" "(get_outputs c)" "(get_offsets c)" 
          "get_sample_time c" "(get_outupd c)"] tmp1 tmp2 tmp3 by (smt (verit, best) 
          get_inputs.simps get_offsets.simps get_outputs.simps get_outupd.simps 
          get_sample_time.cases get_sample_time.simps)
  qed
  have 6: "\<forall>j < length (get_outupd c).(get_outupd (combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c) ! j) (map (\<lambda>a. h a t) (get_inputs
         (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))) = 
    (get_outupd c ! j) (map (\<lambda>a. h a t) (get_inputs c))"
  proof -
    have tmp1: "length (get_offsets a) = length (get_outputs a)"
      using Cons(2) by auto
    have tmp2: "length (get_offsets a) = length (get_outupd a)"
      using Cons(3) by auto
    have tmp3: "\<forall>x\<in>set (get_offsets a). x = 0"
      using Cons(4) by auto
    have tmp4: "\<forall>i<length (get_outputs a). h ((get_outputs a) ! i) t = 
      ((get_outupd a) ! i) (map (\<lambda>a. h a t) (get_inputs a))"
      using Cons(5) by auto      
    show ?thesis using combineOneBlock_funeq2[of "get_offsets a" "get_outputs a" "get_outupd a"
          h t "get_inputs a" "(get_outupd c)" "(get_inputs c)" "(get_outputs c)" "(get_offsets c)" 
          "get_sample_time c"] tmp1 tmp2 tmp3 tmp4 5 by (smt (verit, best) get_inputs.simps 
          get_offsets.simps get_outputs.simps get_outupd.simps get_sample_time.cases 
          get_sample_time.simps)
  qed
  then show ?case unfolding combineBlocks.simps using Cons(1)[of "(combineOneBlock (get_inputs a) 
  (get_outputs a) (get_offsets a) (get_outupd a) c)"] 1 2 3 4 5 by auto
qed

lemma combineBlocks_funeq1: "b \<in> set(c#al) \<Longrightarrow> \<forall>x \<in> set(c#al). length (get_offsets x) = 
length (get_outputs x) \<and> length (get_offsets x) = length (get_outupd x) \<and> 
(\<forall>i j. i < j \<and> j < length (get_outputs x) \<and> 0 \<le> j \<longrightarrow>
get_outputs x ! i \<noteq> get_outputs x ! j) \<Longrightarrow>
i < length (get_outputs b) \<Longrightarrow> j < length (get_outputs (combineBlocks al c)) \<Longrightarrow>
\<forall>x \<in> set(c#al). set (get_offsets x) = {1} \<Longrightarrow>
get_outputs b ! i = get_outputs (combineBlocks al c) ! j \<Longrightarrow>  
\<forall>i j. i < j \<and> j < length (c#al) \<longrightarrow>
set (get_outputs ((c#al) ! i)) \<inter> set (get_outputs ((c#al) ! j)) = {} \<Longrightarrow>
(get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b)) =
(get_outupd (combineBlocks al c) ! j) (map (\<lambda>a. h a t) (get_inputs (combineBlocks al c)))"
proof(induction al arbitrary:c i j b)
  case Nil
  have 1: "b = c"
    using Nil by auto
  have 2: "i = j"
    using Nil(2,3,4) by (metis "1" Nil.prems(1) Nil.prems(6) combineBlocks.simps(1) 
        gr_implies_not0 le_neq_implies_less nle_le)
  then show ?case using 1 by auto
next
  case (Cons a al)
  have 1: "\<forall>x\<in>set (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c # al).
       length (get_offsets x) = length (get_outputs x) \<and>
       length (get_offsets x) = length (get_outupd x) \<and>
       (\<forall>i j. i < j \<and> j < length (get_outputs x) \<and> 0 \<le> j \<longrightarrow>
              get_outputs x ! i \<noteq> get_outputs x ! j)"
      apply clarify subgoal premises pre for x
    proof(cases "x \<in> set al")
      case True
      then show ?thesis using Cons(3) by auto
    next
      case False
      have tmp1: "x = combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c"
        using False pre by auto
      have tmp2: "length (get_offsets x) = length (get_outputs x) \<and>
       length (get_offsets x) = length (get_outupd x)"
        using tmp1 combineOneBlockEq2[of "get_outputs a" "get_offsets a"
            "get_outupd a" "get_outputs c" "get_offsets c" "get_outupd c"] Cons(3) by (smt 
            (verit, best) get_offsets.simps get_outputs.simps get_outupd.simps 
            get_sample_time.cases list.set_intros(1) list.set_intros(2))
      have tmp3: "(\<forall>i j. i < j \<and> j < length (get_outputs x) \<and> 0 \<le> j 
          \<longrightarrow> get_outputs x ! i \<noteq> get_outputs x ! j)"
        using combineOneBlock_noteq[of "get_inputs c" "get_outputs c" "get_offsets c" 
            "get_sample_time c" "get_outupd c" "get_inputs a" "get_outputs a" "get_offsets a"
            "get_outupd a"] tmp1 Cons(3) by (metis bot_nat_0.extremum get_inputs.simps 
            get_offsets.simps get_outputs.simps get_outupd.simps get_sample_time.cases 
            get_sample_time.simps list.set_intros(1))
      then show ?thesis using tmp1 tmp2 by auto
    qed
    done
  have 2: "\<forall>x\<in>set (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) 
    (get_outupd a) c # al). set (get_offsets x) = {1}"
    using Cons(6) combineOneBlockOffsetsEq by (smt (verit, best) get_offsets.simps 
        get_outupd.elims list.set_intros(1) list.set_intros(2) set_ConsD)
  have 4: "\<forall>i j. i < j \<and> j < length ((combineOneBlock (get_inputs a) (get_outputs a) 
          (get_offsets a) (get_outupd a) c) # al) \<longrightarrow> set (get_outputs (((combineOneBlock 
      (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) # al) ! i)) 
    \<inter> set (get_outputs (((combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) 
    (get_outupd a) c) # al) ! j)) = {}"
    proof -
      have tmp1: "\<forall>i < length al. (set (get_outputs a)) 
        \<inter> set (get_outputs (al!i)) = {}"
        apply clarify subgoal premises pre for i
          using Cons(8) pre apply simp by (metis One_nat_def Suc_less_eq diff_Suc_1 not_gr_zero 
              nth_Cons_0 nth_Cons_Suc old.nat.distinct(1)) done
      have tmp2: "\<forall>i < length al. (set (get_outputs c)) 
        \<inter> set (get_outputs (al!i)) = {}"
        apply clarify subgoal premises pre for i
          using Cons(8) pre apply simp by (metis One_nat_def Suc_less_eq diff_Suc_1 not_gr_zero 
              nth_Cons_0 nth_Cons_Suc old.nat.distinct(1)) done
      have tmp3: "\<forall>i < length al. (set (get_outputs a) \<union> set (get_outputs c)) 
        \<inter> set (get_outputs (al!i)) = {}"
        using tmp1 tmp2 by blast 
      have tmp4: "set (get_outputs (combineOneBlock (get_inputs a) (get_outputs a) 
        (get_offsets a) (get_outupd a) c)) = set (get_outputs a) \<union> set (get_outputs c)"
        using combineOneBlockEq Cons by (metis get_outputs.simps get_sample_time.cases 
            insertCI list.simps(15))
      show ?thesis apply clarify subgoal premises pre for i j 
        proof(cases "i = 0")
          case True
          then show ?thesis using tmp3 tmp4 Cons(8) pre 
            by (metis diff_Suc_1 length_Cons less_Suc_eq_0_disj nth_Cons' order_less_irrefl)
        next
          case False
          have tmp: "i > 0"
            using False by simp
          have tmp2: "set (get_outputs (al !  (i-1))) \<inter>
    set (get_outputs (al ! (j-1)))  = {}"
            using Cons(8) pre tmp by (smt (verit, ccfv_SIG) length_Cons not_gr_zero 
                not_less_eq nth_Cons_Suc nth_Cons_pos zero_less_Suc)
          then show ?thesis using tmp pre by simp
        qed
         done
  qed
  then show ?case
  proof(cases "b \<in> set al")
    case True
  have 3: "get_outputs b ! i =
    get_outputs
     (combineBlocks al
       (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)) !
    j"
    using Cons(7) unfolding combineBlocks.simps by simp
    
    then show ?thesis using Cons(1)[of "(combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c)"] Cons 1 2 4 unfolding combineBlocks.simps 
      by (smt (verit, best) True list.set_intros(2))
  next
    case False
    note F1 = False
    then show ?thesis 
    proof(cases "b = a")
      case True
      have tmp1: "set (get_outputs
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)) =
        set (get_outputs a) \<union> set (get_outputs c)"
        using combineOneBlockEq Cons(3,6) by (metis (no_types, opaque_lifting) Cons.prems(1) 
            True get_outputs.simps get_outupd.elims)
      obtain k where tmp: "(get_outputs a ! i) = (get_outputs
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k) \<and>
      k < length (get_outputs
         (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))"
        using tmp1 by (metis Cons.prems(3) True UnCI in_set_conv_nth)
      have 5: "(get_outupd a ! i) (map (\<lambda>a. h a t) (get_inputs a)) = (get_outupd
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k)
     (map (\<lambda>a. h a t) (get_inputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)))"
      proof -
        have tmp1: "\<forall>x\<in>set (get_offsets a). x = 1"
          using Cons(6) by simp
        have tmp2: "length (get_offsets a) = length (get_outputs a)"
          using Cons(3) by simp
        have tmp3: "length (get_offsets a) = length (get_outupd a)"
          using Cons(3) by simp
        have tmp4: "length (get_offsets c) = length (get_outputs c)"
          using Cons(3) by simp
        have tmp5: "length (get_offsets c) = length (get_outupd c)"
          using Cons(3) by simp
        have tmp6: "set (get_outputs a) \<inter> set (get_outputs c) = {}"
          using Cons(8) by (metis Cons.prems(1) Suc_leI inf_commute length_Cons length_pos_if_in_set
              nat_less_le not_less_eq nth_Cons_0 nth_Cons_Suc old.nat.distinct(1))
        have tmp7: "\<forall>i j. i < j \<and>
        j < length (get_outputs c) \<longrightarrow> get_outputs c ! i \<noteq> get_outputs c ! j"
          using Cons(3) by auto
        have tmp8: "\<forall>i j. i < j \<and> j < length (get_outputs a) \<longrightarrow> get_outputs a ! i \<noteq> get_outputs a ! j"
          using Cons(3) by auto
        have tmp9: "i < length (get_outputs a)"
          using Cons(4) True by simp
        have tmp10: "k < length
       (get_outputs
         (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
           (Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c)
             (get_outupd c))))"
          using tmp by (smt (verit) get_inputs.simps get_offsets.simps get_outputs.simps 
              get_outupd.simps get_sample_time.cases get_sample_time.simps)
        have tmp11: "(Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c)
             (get_outupd c)) = c"
          by (smt (verit, ccfv_SIG) get_inputs.simps get_offsets.simps get_outputs.simps 
              get_outupd.simps get_sample_time.cases get_sample_time.simps)
        have tmp12: "get_outputs a ! i =
          get_outputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
             (Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c) (get_outupd c))) !
          k"
          using tmp tmp11 by auto
        show ?thesis using combineOneBlock_Integeq2[of "get_offsets a" "get_outputs a" "get_outupd a"
              "get_offsets c" "get_outputs c" "get_outupd c" "get_inputs c" "get_sample_time c"
              i k "get_inputs a" h t] tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 tmp9 tmp10 tmp11 tmp12
          by auto
      qed
      have 6: "(get_outupd (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k)
   (map (\<lambda>a. h a t)
     (get_inputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))) =
      (get_outupd (combineBlocks (a # al) c) ! j)
     (map (\<lambda>a. h a t) (get_inputs (combineBlocks (a # al) c)))"
      proof - 
        have tmp1: "k < length
         (get_outputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))"
          using tmp by auto
        have tmp2: "j < length
         (get_outputs
           (combineBlocks al
             (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)))"
          using Cons(5) by auto
        have tmp3: " get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) !
    k =
    get_outputs
     (combineBlocks al
       (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)) !
    j"
          using Cons(7) tmp True by auto
        show ?thesis unfolding combineBlocks.simps using Cons(1)[of "(combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c)" "(combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c)" k j] 1 2  tmp1 tmp2 tmp3 4 by fastforce
      qed
      then show ?thesis using 5 True unfolding combineBlocks.simps by presburger
    next
      case False
      have 7: "b = c"
        using False F1 Cons(2) by simp
      have tmp1: "set (get_outputs
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)) =
        set (get_outputs a) \<union> set (get_outputs c)"
        using combineOneBlockEq Cons(3,6) by (metis (no_types, opaque_lifting) get_outputs.simps 
            get_sample_time.cases list.set_intros(1) list.set_intros(2))
      obtain k where tmp: "(get_outputs c ! i) = (get_outputs
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k) \<and>
      k < length (get_outputs
         (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))"
        using tmp1 by (metis "7" Cons.prems(3) UnI2 in_set_conv_nth)
      have 8: "(get_outupd c ! i) (map (\<lambda>a. h a t) (get_inputs c)) = (get_outupd
        (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k)
     (map (\<lambda>a. h a t) (get_inputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)))"
      proof -
        have tmp1: "\<forall>x\<in>set (get_offsets a). x = 1"
          using Cons(6) by simp
        have tmp2: "length (get_offsets a) = length (get_outputs a)"
          using Cons(3) by simp
        have tmp3: "length (get_offsets a) = length (get_outupd a)"
          using Cons(3) by simp
        have tmp4: "length (get_offsets c) = length (get_outputs c)"
          using Cons(3) by simp
        have tmp5: "length (get_offsets c) = length (get_outupd c)"
          using Cons(3) by simp
        have tmp7: "\<forall>i j. i < j \<and>
        j < length (get_outputs c) \<longrightarrow> get_outputs c ! i \<noteq> get_outputs c ! j"
          using Cons(3) by auto
        have tmp8: "\<forall>i j. i < j \<and> j < length (get_outputs a) \<longrightarrow> get_outputs a ! i \<noteq> get_outputs a ! j"
          using Cons(3) by auto
        have tmp9: "i < length (get_outputs c)"
          using Cons(4) 7 by simp
        have tmp10: "k < length
       (get_outputs
         (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
           (Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c)
             (get_outupd c))))"
          using tmp by (smt (verit) get_inputs.simps get_offsets.simps get_outputs.simps 
              get_outupd.simps get_sample_time.cases get_sample_time.simps)
        have tmp11: "(Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c)
             (get_outupd c)) = c"
          by (smt (verit, ccfv_SIG) get_inputs.simps get_offsets.simps get_outputs.simps 
              get_outupd.simps get_sample_time.cases get_sample_time.simps)
        have tmp12: "get_outputs c ! i =
          get_outputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
             (Block (get_inputs c) (get_outputs c) (get_offsets c) (get_sample_time c) (get_outupd c))) !
          k"
          using tmp tmp11 by auto
        show ?thesis using combineOneBlock_Integeq[of "get_offsets a" "get_outputs a" "get_outupd a"
              "get_offsets c" "get_outputs c" "get_outupd c" "get_inputs c" "get_sample_time c"
              i k "get_inputs a" h t] tmp1 tmp2 tmp3 tmp4 tmp5 tmp7 tmp8 tmp9 tmp10 tmp11 tmp12
          by auto
      qed
      have 9: "(get_outupd (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) ! k)
   (map (\<lambda>a. h a t)
     (get_inputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))) =
      (get_outupd (combineBlocks (a # al) c) ! j)
     (map (\<lambda>a. h a t) (get_inputs (combineBlocks (a # al) c)))"
      proof - 
        have tmp1: "k < length
         (get_outputs
           (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c))"
          using tmp by auto
        have tmp2: "j < length
         (get_outputs
           (combineBlocks al
             (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)))"
          using Cons(5) by auto
        have tmp3: " get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c) !
    k =
    get_outputs
     (combineBlocks al
       (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) c)) !
    j"
          using Cons(7) tmp 7 by auto
        show ?thesis unfolding combineBlocks.simps using Cons(1)[of "(combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c)" "(combineOneBlock (get_inputs a) (get_outputs a) 
      (get_offsets a) (get_outupd a) c)" k j] 1 2  tmp1 tmp2 tmp3 4 by fastforce
      qed
      then show ?thesis using 8 7 unfolding combineBlocks.simps by presburger
    qed
  qed
qed

lemma combineBlocks_outputseq: "\<forall>x \<in> set al. set (get_offsets x) = {0} \<Longrightarrow> 
(get_outputs b) = (get_outputs (combineBlocks al b))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "get_outputs b = get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"
    using combineOneBlockOutputseq Cons(2) by (metis block.exhaust get_outputs.simps list.set_intros(1))
  then show ?case unfolding combineBlocks.simps using Cons by (metis list.set_intros(2))
qed

lemma combineBlocks_wf2: "\<forall>x \<in> set (b#al). ((length (get_offsets x)) = (length (get_outputs x))
    \<and> ((length (get_outputs x)) = (length (get_outupd x)))
    \<and> (\<forall>i j. i < j \<and> j < (length (get_outputs x)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs x) i) \<noteq> (nth (get_outputs x) j))) 
\<Longrightarrow> length (get_offsets (combineBlocks al b)) 
= length (get_outputs (combineBlocks al b)) \<and> length (get_outputs (combineBlocks al b)) 
= length (get_outupd (combineBlocks al b)) \<and>  (\<forall>i j. i < j \<and> j < (length (get_outputs (combineBlocks al b))) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs (combineBlocks al b)) i) \<noteq> (nth (get_outputs (combineBlocks al b)) j))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case unfolding Available'_def by simp
next
  case (Cons a al)
  have 1: "length (get_offsets (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) 
          = length (get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) \<and>
       length (get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) 
          = length (get_outupd (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) \<and>
       (\<forall>i j. i < j \<and>
              j < length
                   (get_outputs
                     (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
                       b)) \<and>
              0 \<le> j \<longrightarrow>
              get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b) ! i 
            \<noteq> get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b) ! j)"
  proof -
    have tmp1: "length (get_offsets (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) 
          = length (get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) \<and>
       length (get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)) 
          = length (get_outupd (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b))"
      using combineOneBlockEq2[of "(get_outputs a)" "(get_offsets a)" "(get_outupd a)" "(get_outputs b)" 
        "(get_offsets b)" "(get_outupd b)" "(get_inputs a)" "(get_inputs b)"] Cons(2) by (metis 
          get_inputs.simps get_offsets.simps get_outputs.simps get_outupd.elims list.set_intros(1)
          list.set_intros(2))
    have tmp2: "(\<forall>i j. i < j \<and>
              j < length
                   (get_outputs
                     (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a)
                       b)) \<and>
              0 \<le> j \<longrightarrow>
              get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b) ! i 
            \<noteq> get_outputs (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b) ! j)"
      using combineOneBlock_noteq[of "(get_inputs b)" "(get_outputs b)" 
        "(get_offsets b)" "get_sample_time b" "(get_outupd b)" "(get_inputs a)" "(get_outputs a)" 
        "(get_offsets a)" "(get_outupd a)" ] Cons(2) by (smt (verit, ccfv_threshold) 
          get_inputs.simps get_offsets.simps get_outputs.simps get_outupd.simps 
          get_sample_time.cases get_sample_time.simps list.set_intros(1) zero_order(1))
    show ?thesis using tmp1 tmp2 by simp
  qed
  show ?case unfolding combineBlocks.simps using Cons(1)[of "(combineOneBlock 
(get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"] Cons(2) 1 by auto
qed

lemma combineBlocksSubset : "set (get_outputs (combineBlocks al b)) \<subseteq> Outputs (b#al)"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockSubset[of "(get_inputs a)"
        "(get_outputs a)" "(get_offsets a)" "(get_outupd a)" "(get_inputs b)" "(get_outputs b)" 
        "(get_offsets b)" "(get_sample_time b)" "(get_outupd b)"] Cons[of 
        "(combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) b)"]
    by auto
qed

lemma combineBlocksSubset2 : "\<forall>b \<in> set al. set (get_offsets b) = {0} \<or>
 set (get_offsets b) = {1} \<or> set (get_offsets b) = {} \<Longrightarrow>
set (get_outputs (combineBlocks al b)) \<subseteq> Outputs (b#(findIntegBlks al))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case 
    proof(cases "set (get_offsets a) = {1}")
      case True
      have 2: "a \<in> set (findIntegBlks (a # al))"
        unfolding findIntegBlks.simps True by simp
      then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset
        by (smt (verit, ccfv_SIG) Outputs.simps(2) True dual_order.trans 
            findIntegBlks.simps(2) le_sup_iff list.set_intros(2) set_eq_subset)
    next
      case False
      note F = False
      then show ?thesis
      proof(cases "set (get_offsets a) = {0}")
        case True
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset3
        by (smt (verit, best) False Outputs.elims findIntegBlks.simps(2) list.distinct(1) 
            list.inject list.set_intros(2))
      next
        case False
        have 3: "(get_offsets a) = []"
          using Cons(2) False F by auto
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset4
  by (smt (verit, best) F Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2) set_empty)
      qed
    qed
qed

lemma combineBlocksSubset3 : "set (get_outputs b) \<subseteq> set (get_outputs (combineBlocks al b))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockSubset2
    by (metis local.Cons subset_trans)
qed

lemma combineBlocksSubset4 : "\<forall>b \<in> set al. set (get_offsets b) = {0} \<or>
 set (get_offsets b) = {1} \<or> set (get_offsets b) = {} \<Longrightarrow> wf2 al \<Longrightarrow>
set (get_outputs (combineBlocks al b)) = Outputs (b#(findIntegBlks al))"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case 
    proof(cases "set (get_offsets a) = {1}")
      case True
      have 2: "a \<in> set (findIntegBlks (a # al))"
        unfolding findIntegBlks.simps True by simp
      have 3: "Available' (Block (get_inputs a) (get_outputs a) 
        (get_offsets a) (get_sample_time a) (get_outupd a))"
        using Cons(3) unfolding wf2_def by (simp add: Available'_def)
      have 4: "set (get_outputs
          (combineOneBlock (get_inputs a) (get_outputs a) (get_offsets a) (get_outupd a) 
      b)) = set (get_outputs a) \<union> set (get_outputs b)"
        using combineOneBlockSubset5 True 1 3 by metis
      then show ?thesis using 1 unfolding combineBlocks.simps using Cons 
        wf2_lemma True by auto
    next
      case False
      note F = False
      then show ?thesis
      proof(cases "set (get_offsets a) = {0}")
        case True
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset3
          by (metis wf2_lemma False Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2))
      next
        case False
        have 3: "(get_offsets a) = []"
          using Cons(2) False F by auto
        then show ?thesis using 1 unfolding combineBlocks.simps using Cons combineOneBlockSubset4
   by (metis wf2_lemma F Outputs.simps(2) findIntegBlks.simps(2) list.set_intros(2) set_empty)
      qed
    qed
  qed

lemma combineBlocksEq : "\<forall>b \<in> set al. set (get_offsets b) = {1} \<and> 
length (get_offsets b) = length (get_outputs b) \<and>
length (get_offsets b) = length (get_outupd b) \<Longrightarrow>
set (get_outputs (combineBlocks al b)) = Outputs (b#al)"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockEq Cons by (smt (verit, best) 
        Outputs.simps(2) list.set_intros(1) list.set_intros(2) sup.assoc sup_commute)
qed

lemma combineBlockEq2 : "\<forall>b \<in> set(b#al). length (get_offsets b) = length (get_outputs b) \<and>
length (get_offsets b) = length (get_outupd b) \<Longrightarrow> length (get_offsets 
(combineBlocks al b)) = length (get_outputs (combineBlocks al b)) \<and> length (get_offsets 
(combineBlocks al b)) = length (get_outupd (combineBlocks al b))"
proof(induction al arbitrary: b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  have 1: "b = Block (get_inputs b) (get_outputs b) (get_offsets b) (get_sample_time b) (get_outupd b)"
    by (metis block.exhaust get_inputs.simps get_offsets.simps get_outputs.simps 
        get_outupd.simps get_sample_time.simps)
  then show ?case unfolding combineBlocks.simps using combineOneBlockEq2 Cons
    by (metis list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma combineBlocksOffsetEq : "set (get_offsets b) = {1} \<Longrightarrow>
set (get_offsets (combineBlocks al b)) = {1}"
proof(induction al arbitrary:b)
  case Nil
  then show ?case by simp
next
  case (Cons a al)
  then show ?case unfolding combineBlocks.simps using combineOneBlockOffsetsEq
    by (metis get_offsets.elims)
qed

text\<open>bl: all continuous blocks; c: basic integrator block;
cl: those related blocks of c which have been found before\<close>
fun getOneRelatedBlock :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> 
  ConBlk list \<Rightarrow> ConBlk option" where
  "getOneRelatedBlock [] c cl = None" |
  "getOneRelatedBlock (b#bl) c cl = (if ((set (get_outputs b) \<inter> set (get_inputs c) \<noteq> {} \<or>
  set (get_outputs b) \<inter> (Inputs cl) \<noteq> {}) \<and> set (get_offsets b) = {0}) then (Some b) else 
  getOneRelatedBlock bl c cl)"

lemma getOneRelatedBlockNone: "getOneRelatedBlock bl c cl = None \<Longrightarrow> \<forall>x \<in> set (getCalBlks bl).
set (get_outputs x) \<inter> set (get_inputs c) = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding getOneRelatedBlock.simps using getCalBlks_offsets 
    by (metis getCalBlks.simps(2) option.distinct(1) set_ConsD)
qed

lemma getOneRelatedBlockNone2: "getOneRelatedBlock bl c cl = None \<Longrightarrow> \<forall>x \<in> set (getCalBlks bl).
set (get_outputs x) \<inter> Inputs cl = {}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding getOneRelatedBlock.simps using getCalBlks_offsets 
    by (metis getCalBlks.simps(2) option.distinct(1) set_ConsD)
qed

lemma getOneRelatedBlockSubset: "getOneRelatedBlock bl c cl = Some y \<Longrightarrow> y \<in> set bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding getOneRelatedBlock.simps
    by (metis list.set_intros(1) list.set_intros(2) option.inject)
qed

lemma getOneRelatedBlockOffset: "getOneRelatedBlock bl c cl = Some y \<Longrightarrow> set (get_offsets y) = {0}"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding getOneRelatedBlock.simps by (metis option.inject)
qed

lemma getOneRelatedBlockCalBlks: "getOneRelatedBlock bl c cl = Some y \<Longrightarrow> 
y \<in> set (getCalBlks bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case
  proof(cases "set (get_outputs b) \<inter> set (get_inputs c) \<noteq> {} \<or> set (get_outputs b) \<inter> Inputs cl \<noteq> {} \<and>
        set (get_offsets b) = {0}")
    case True
    then show ?thesis using Cons unfolding getOneRelatedBlock.simps getCalBlks.simps
      by (smt (verit, best) insertI1 list.simps(15) option.inject)
  next
    case False
    then show ?thesis using Cons unfolding getOneRelatedBlock.simps getCalBlks.simps
      by (smt (z3) insert_iff list.simps(15))
  qed
qed

fun getSortedBlocks :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> ConBlk list \<Rightarrow> ConBlk list" where
  "getSortedBlocks bl c cl = (if besorted2 (rev cl) then cl else rev (sortDiag ((getCalBlks bl)@cl)))"

lemma getSortedBlocks_clsubset: "loop_free ((getCalBlks bl)@cl) \<Longrightarrow>
set cl \<subseteq> set (getSortedBlocks bl c cl)"
  subgoal premises pre
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis unfolding getSortedBlocks.simps using sort_perm pre 
    by (smt (z3) prem_seteq set_append set_rev subset_code(1) sup_ge2)
qed
  done

lemma getSortedBlocks_subset: "Outputs (getSortedBlocks bl c cl) \<subseteq> Outputs bl \<union> Outputs cl"
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis unfolding getSortedBlocks.simps using sortDiag_subset getCalBlksSubset by (smt 
    (z3) Outputs_Cons Outputs_eq Outputs_rev set_append subset_Un_eq sup.left_commute sup_commute)
qed

lemma getSortedBlocks_offsets: "\<forall>x \<in> set cl. set (get_offsets x) = {0} \<Longrightarrow> 
\<forall>x \<in> set (getSortedBlocks bl c cl). set (get_offsets x) = {0}"
  subgoal premises pre
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis unfolding getSortedBlocks.simps using pre by presburger
next
  case False
  then show ?thesis unfolding getSortedBlocks.simps using getCalBlks_offsets sortDiag_subset 
    pre by fastforce
qed
  done

lemma getSortedBlocks_besorted: "wf2 ((getCalBlks bl)@cl) \<Longrightarrow> loop_free ((getCalBlks bl)@cl) \<Longrightarrow>
\<forall>x \<in> set cl. set (get_offsets x) = {0} \<Longrightarrow> besorted2 (rev (getSortedBlocks bl c cl))"
  subgoal premises pre
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis unfolding getSortedBlocks.simps using pre by presburger
next
  case False
  then show ?thesis unfolding getSortedBlocks.simps using pre sort_is_sorted3
    by (smt (verit, ccfv_threshold) UnE getCalBlks_offsets rev_rev_ident set_append)
qed
  done


lemma getSortedBlocks_subset2: "set (getSortedBlocks bl c cl) \<subseteq> set bl \<union> set cl"
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis unfolding getSortedBlocks.simps using sortDiag_subset getCalBlksSubset2 
    by (smt (z3) UnE UnI1 UnI2 set_append set_rev subset_code(1))
qed

lemma getSortedBlocks_Unique: "Unique (bl@cl) \<Longrightarrow> Unique (getSortedBlocks bl c cl)"
  subgoal premises pre
proof(cases "besorted2 (rev cl)")
  case True
  then show ?thesis unfolding getSortedBlocks.simps using pre Unique_Cons by auto
next
  case False
  have 1: "Unique (getCalBlks bl @ cl)"
    using pre proof(induction bl)
    case Nil
    then show ?case by simp
  next
    case (Cons b bl)
    then show ?case unfolding getCalBlks.simps by (smt (verit, ccfv_threshold) Un_iff Unique_add 
          Unique_k Unique_lemma append_Cons getCalBlksSubset2 in_mono in_set_conv_nth 
          list.set_intros(1) remove_hd set_append zero_order(1))
  qed
  then show ?thesis unfolding getSortedBlocks.simps using sortDiag_Unique
    by (simp add: False Unique_rev)
qed
  done

(*give the block list bl, return the related blocks of the integrator block c;
here cl are those related blocks of c which have been found before(initialized to [])*)
function getRelatedBlocks :: "ConBlk list \<Rightarrow> ConBlk \<Rightarrow> 
  ConBlk list \<Rightarrow> ConBlk list" where
  "getRelatedBlocks bl c cl = (if getOneRelatedBlock bl c cl = None 
  then getSortedBlocks bl c cl else 
  getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
  (cl@[(the (getOneRelatedBlock bl c cl))]))"
  by pat_completeness auto
termination 
  apply (relation "measures[(\<lambda>(bl::ConBlk list , c::ConBlk,
cl::ConBlk list). length bl)]", auto)
  subgoal premises pre for bl c cl y
  proof -
    show ?thesis using pre getOneRelatedBlockSubset
      by (metis length_Cons lessI perm_length perm_remove)
  qed
  done

lemma getRelatedBlocksSubsetCl: "loop_free ((getCalBlks bl)@cl) \<Longrightarrow> Unique ((getCalBlks bl)@cl)
\<Longrightarrow> set cl \<subseteq> set (getRelatedBlocks bl c cl)"
proof(induction bl arbitrary:cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] 2(2) getSortedBlocks_clsubset
      by presburger
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
    using False getOneRelatedBlockSubset 
    by (metis One_nat_def Suc_pred length_pos_if_in_set length_remove1 lessI option.collapse)
    have 4: "(the (getOneRelatedBlock bl c cl)) \<in> set bl"
      using False getOneRelatedBlock.simps "3" remove1_idem by force
    have 5: "loop_free (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(2) 4 loop_free_perm by (metis "2.prems"(2) False getCalBlks_remove 
          getOneRelatedBlockCalBlks option.exhaust_sel perm_remove3) 
    have 6 : "Unique (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
    proof -
      have "(the (getOneRelatedBlock bl c cl)) \<in> set (getCalBlks bl)"
      using False getOneRelatedBlock.simps "3" remove1_idem  getOneRelatedBlockCalBlks by simp
      then show ?thesis using Unique_Permutation by (metis "2.prems"(2) "4" getCalBlks_remove perm_remove3) 
    qed
    then show ?thesis using 2(1) 3 4 5 getRelatedBlocks.simps[of bl c cl] by (metis (no_types, lifting) 
          False case_prodI mem_Collect_eq set_append subset_trans sup_ge1)
  qed
qed

lemma getRelatedBlocksIn: "getOneRelatedBlock bl c cl = Some b \<Longrightarrow> Unique ((getCalBlks bl)@cl) \<Longrightarrow>
loop_free ((getCalBlks bl)@cl) \<Longrightarrow> b \<in> set (getRelatedBlocks bl c cl)"
proof(induction bl arbitrary: b cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
    using 2(2) getOneRelatedBlockSubset 
    by (metis One_nat_def Suc_pred length_pos_if_in_set length_remove1 lessI option.sel)
  then show ?case
  proof(cases "getOneRelatedBlock (remove1 (the (getOneRelatedBlock bl c cl)) bl) 
        c (cl@[the (getOneRelatedBlock bl c cl)]) = None")
    case True
    have 5: "b \<in> set (getCalBlks bl)"
      using 2(2) getOneRelatedBlock.simps "3" remove1_idem  getOneRelatedBlockCalBlks by presburger
    have 4: "sortDiag (getCalBlks (remove1 b bl) @ cl @ [b]) <~~> (getCalBlks bl)@cl"
    proof -
      have tmp1: "getCalBlks (remove1 b bl) @ cl @ [b] <~~> (getCalBlks bl)@cl"
        using 5 by (metis "2.prems"(1) getCalBlks_remove getOneRelatedBlockSubset perm_remove3 perm_sym)
      then show ?thesis using 2(3,4) loop_free_perm sort_perm
        by (meson perm.trans perm_sym)
    qed
    show ?thesis using True 2(2) getRelatedBlocks.simps[of bl c cl] getRelatedBlocks.simps[of 
          "(remove1 (the (getOneRelatedBlock bl c cl)) bl)" c "(cl@[the (getOneRelatedBlock bl c cl)])"]
      apply simp using 4 by (metis 5 Un_iff perm_sym prem_seteq set_append)
  next
    case False
    have 5: "b \<in> set (getCalBlks bl)"
      using 2(2) getOneRelatedBlock.simps "3" remove1_idem  getOneRelatedBlockCalBlks by presburger
    have 4: "sortDiag (getCalBlks (remove1 b bl) @ cl @ [b]) <~~> (getCalBlks bl)@cl"
    proof -
      have tmp1: "getCalBlks (remove1 b bl) @ cl @ [b] <~~> (getCalBlks bl)@cl"
        using 5 by (metis "2.prems"(1) getCalBlks_remove getOneRelatedBlockSubset perm_remove3 perm_sym)
      then show ?thesis using 2(3,4) loop_free_perm sort_perm 
        by (meson perm.trans perm_sym)
    qed
    have 6: "loop_free (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(3) 4 loop_free_perm by (metis "2.prems"(1) "2.prems"(3) "5" getCalBlks_remove 
          getOneRelatedBlockSubset option.sel perm_remove3) 
    have 7 : "Unique (getCalBlks (remove1 b bl) @ (cl@[b]))"
    proof -
      have "getCalBlks (remove1 b bl) @ cl @ [b] <~~> (getCalBlks bl)@cl"
        using 5 by (metis "2.prems"(1) getCalBlks_remove getOneRelatedBlockSubset perm_remove3 perm_sym)
      then show ?thesis using Unique_Permutation by (metis "2.prems"(2) perm_sym)
    qed
    then show ?thesis using 2(2,3,4) 3 4 5 6 getRelatedBlocks.simps[of bl c cl] getRelatedBlocksSubsetCl
      by (metis in_mono in_set_conv_decomp not_None_eq option.sel)
  qed
qed

lemma getRelatedBlocksOffsets: "\<forall>x \<in> set cl. set (get_offsets x) = {0} \<Longrightarrow> 
\<forall>b \<in> set (getRelatedBlocks bl c cl). set (get_offsets b) = {0}"
  apply clarify subgoal for b
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] 2(2) using "2.prems"(2) 
        getSortedBlocks_offsets by presburger
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "\<forall>x \<in> set(cl@[the (getOneRelatedBlock bl c cl)]). set (get_offsets x) = {0}"
      using 2(2) getOneRelatedBlockOffset False by auto
    then show ?thesis using 3 getSortedBlocks_subset 2 
      by (metis False case_prodI getRelatedBlocks.simps mem_Collect_eq)
  qed
qed
  done

lemma getRelatedBlocks_besorted: "wf2 ((getCalBlks bl) @ cl) \<Longrightarrow> 
loop_free ((getCalBlks bl) @ cl) \<Longrightarrow> \<forall>x\<in>set cl. set (get_offsets x) = {0} \<Longrightarrow>
besorted2 (rev (getRelatedBlocks bl c cl))"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] 2(2) using "2.prems"(1,2,3) 
        getSortedBlocks_besorted by presburger
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "(the (getOneRelatedBlock bl c cl)) \<in> set bl"
      using False getOneRelatedBlock.simps "3" remove1_idem by force
    have 5: "wf2 (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(2) 4 by (metis False getCalBlks_remove getOneRelatedBlockCalBlks 
          option.collapse perm_remove3 wf2_lemma2)
    have 6: "loop_free (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(2,3) 4 loop_free_perm unfolding wf2_def by (metis False getCalBlks_remove 
          getOneRelatedBlockCalBlks option.exhaust_sel perm_remove3)
    have 7: "\<forall>x\<in>set (cl@[the (getOneRelatedBlock bl c cl)]). set (get_offsets x) = {0}"
      using 2(4) getOneRelatedBlockOffset by (simp add: False)
    then show ?thesis using 3 4 5 6 2(1) by (simp add: False)
  qed
qed

lemma getRelatedBlocksInputs1: "wf2 bl \<Longrightarrow> \<forall>x \<in> set cl. set (get_offsets x) = {0} 
\<Longrightarrow> c \<in> set bl \<Longrightarrow> set (get_offsets c) = {1} \<Longrightarrow> loop_free ((getCalBlks bl)@cl) \<Longrightarrow> 
Unique ((getCalBlks bl)@cl) \<Longrightarrow>
\<forall>x \<in> set (get_inputs c). x \<in> Outputs (getRelatedBlocks bl c cl) \<or> 
      x \<in> Inputs bl - Outputs bl \<or> x \<in> Outputs (findIntegBlks bl)"
  apply clarify subgoal for x
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case     
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    note T1 = True
    then show ?thesis
    proof(cases "besorted2 (rev cl)")
      case True
      have 3: "(getRelatedBlocks bl c cl) = cl"
        using True using getRelatedBlocks.simps[of bl c cl] T1 by force
      have 4: "\<forall>x\<in>set (getCalBlks bl). set (get_outputs x) \<inter> set (get_inputs c) = {}"
        using T1 getOneRelatedBlockNone[of bl c cl] by simp
      have 5: "set (get_inputs c) \<inter> Outputs (getCalBlks bl) = {}"
        using 4 proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        then show ?case
        proof(cases "set (get_offsets b) = {0}")
          case True
          then show ?thesis unfolding getCalBlks.simps using Cons Un_iff 
              getCalBlks.simps(2) list.set_intros(1) by auto
        next
          case False
          then show ?thesis unfolding getCalBlks.simps using Cons by auto
        qed
      qed
      have 6: "x \<notin> Outputs bl"
        using 2(2,9,10) 5 IntegCalOutputsUniun "2.prems"(7) by blast
      then show ?thesis using 2(4,8) by (metis DiffI Inputs_base2 Un_iff)
    next
      case False
      have 3: "(getRelatedBlocks bl c cl) = rev (sortDiag ((getCalBlks bl)@cl))"
        using False using getRelatedBlocks.simps[of bl c cl] True besorted2_is_besorted by force
      have 4: "Outputs (getRelatedBlocks bl c cl) = Outputs ((getCalBlks bl)@cl)"
        using 3 2(6) sort_perm Outputs_perm Outputs_rev by metis
      have 5: "x \<notin> Outputs bl"
        using 2(2,9,10) 4 IntegCalOutputsUniun using Outputs_Cons by blast
      then show ?thesis using 2(4,8) by (metis DiffI Inputs_base2 Un_iff)
    qed
  next
    case False
    note F1 = False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "(the (getOneRelatedBlock bl c cl)) \<in> set bl"
      using False getOneRelatedBlock.simps "3" remove1_idem by force
    have 5: "wf2 (remove1 (the (getOneRelatedBlock bl c cl)) bl)"
      using 2(2) 4 by (simp add: wf2_remove)
    have 6: "\<forall> x \<in> set (cl@[the (getOneRelatedBlock bl c cl)]). set (get_offsets x) = {0}"
      using 2(3) False getOneRelatedBlockOffset by auto
    have 7: "c \<in> set (remove1 (the (getOneRelatedBlock bl c cl)) bl)"
      using 2(4,5) getOneRelatedBlockOffset by (metis False One_nat_def in_set_remove1 insertI1 
          length_greater_0_conv lessI list.size(3) option.exhaust_sel singletonD)
    have 8: "loop_free (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(6) 4 loop_free_perm by (metis "2.prems"(6) False getCalBlks_remove 
          getOneRelatedBlockCalBlks option.exhaust_sel perm_remove3) 
    have 9: "x \<notin> Outputs (getRelatedBlocks (remove1 
      (the (getOneRelatedBlock bl c cl)) bl) c (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(8) getRelatedBlocks.simps[of bl c cl] False "2.prems"(8) by presburger
    have 10: "x \<notin> Outputs (findIntegBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl))"
      using findIntegBlks_forall by (meson "2.prems"(9) findIntegBlksSubset2 in_mono set_remove1_subset)
    have 11: "Unique (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
    proof -
      have "(the (getOneRelatedBlock bl c cl)) \<in> set (getCalBlks bl)"
      using False getOneRelatedBlock.simps "3" remove1_idem  getOneRelatedBlockCalBlks by simp
      then show ?thesis using Unique_Permutation by (metis "2.prems"(6) "4" getCalBlks_remove perm_remove3)
    qed
    have 12: "x \<in> Inputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) - 
                  Outputs (remove1 (the (getOneRelatedBlock bl c cl)) bl)"
      using 2(1,5,8) 3 4 5 6 7 8 9 10 11 by blast
    then show ?thesis
    proof(cases "x \<in> Inputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) - Outputs bl")
      case True
      then show ?thesis using 4 Inputs_base2 by auto
    next
      case False
      have 12: "x \<in> set (get_outputs (the (getOneRelatedBlock bl c cl)))"
        using False 4 12 Outputs_base2 by auto
      have 13: "the (getOneRelatedBlock bl c cl) \<in> set (getRelatedBlocks bl c cl)"
        using getRelatedBlocksIn F1 2(6,7) by force
      then show ?thesis using 2(9) 12 using Outputs_base2 by blast
    qed
  qed
qed
  done

lemma getRelatedBlocksInputs2: "wf2 bl \<Longrightarrow> \<forall>x \<in> set cl. set (get_offsets x) = {0} 
\<Longrightarrow> c \<in> set bl \<Longrightarrow> set (get_offsets c) = {1} \<Longrightarrow> loop_free ((getCalBlks bl)@cl) \<Longrightarrow>
(getOneRelatedBlock bl c cl = None \<longrightarrow> Inputs cl \<inter> Outputs (getCalBlks bl) = {}) \<Longrightarrow>
Unique ((getCalBlks bl)@cl) \<Longrightarrow>
\<forall>x \<in> Inputs (getRelatedBlocks bl c cl). x \<in> Outputs (getRelatedBlocks bl c cl) \<or> 
      x \<in> Inputs (bl@cl) - Outputs (bl@cl) \<or> x \<in> Outputs (findIntegBlks bl)"
  apply clarify subgoal for x
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    note T1 = True
    then show ?thesis
    proof(cases "besorted2 (rev cl)")
      case True
      have 3: "(getRelatedBlocks bl c cl) = cl"
        using True using getRelatedBlocks.simps[of bl c cl] T1 by force
      have 4: "Inputs cl \<inter> Outputs (getCalBlks bl) = {}"
        using 2(7) T1 by force
      have 4: "x \<notin> Outputs bl"
        using 2(2,9,10,11) 4 IntegCalOutputsUniun by (metis "3" UnE disjoint_iff)
      then show ?thesis using 2(9,10) 3 by (simp add: Inputs_Cons Outputs_Cons)
    next
      case False
      have 3: "(getRelatedBlocks bl c cl) = rev (sortDiag ((getCalBlks bl)@cl))"
        using False using getRelatedBlocks.simps[of bl c cl] True besorted2_is_besorted by force
      have 4: "Outputs (getRelatedBlocks bl c cl) = Outputs ((getCalBlks bl)@cl)"
        using 3 2(6) sort_perm Outputs_perm Outputs_rev by metis
      have 5: "x \<notin> Outputs bl"
        using 2(2,10,11) 4 IntegCalOutputsUniun using Outputs_Cons by blast
      have 6: "Inputs (getRelatedBlocks bl c cl) = Inputs ((getCalBlks bl)@cl)"
        using 3 2(6) sort_perm Inputs_perm Inputs_rev by metis
      have 7: "x \<notin> Outputs (bl @ cl)"
        using 5 2(10) 4 Outputs_Cons by force
      have 8: "x \<in> Inputs (bl @ cl)"
        using 6 getCalBlksSubset3 Inputs_Cons "2.prems"(8) by auto
      then show ?thesis using 7 by auto
    qed
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "(the (getOneRelatedBlock bl c cl)) \<in> set bl"
      using False getOneRelatedBlock.simps "3" remove1_idem by force
    have 5: "wf2 (remove1 (the (getOneRelatedBlock bl c cl)) bl)"
      using 2(2) 4 by (simp add: wf2_remove)
    have 6: "\<forall> x \<in> set (cl@[the (getOneRelatedBlock bl c cl)]). set (get_offsets x) = {0}"
      using 2(3) False getOneRelatedBlockOffset by auto
    have 7: "c \<in> set (remove1 (the (getOneRelatedBlock bl c cl)) bl)"
      using 2(4,5) getOneRelatedBlockOffset by (metis False One_nat_def in_set_remove1 insertI1 
          length_greater_0_conv lessI list.size(3) option.exhaust_sel singletonD)
    have 8: "loop_free (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(6) 4 loop_free_perm by (metis "2.prems"(7) False getCalBlks_remove 
          getOneRelatedBlockCalBlks option.collapse perm_remove3)
    have 9: "getOneRelatedBlock (remove1 (the (getOneRelatedBlock bl c cl)) bl)
           c (cl@[the (getOneRelatedBlock bl c cl)]) = None 
        \<longrightarrow> Inputs (cl@[the (getOneRelatedBlock bl c cl)]) \<inter> 
        Outputs (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl)) = {}"
    proof(cases "getOneRelatedBlock (remove1 (the (getOneRelatedBlock bl c cl)) bl)
           c (cl@[the (getOneRelatedBlock bl c cl)]) = None")
      case True
      have 4: "\<forall>x\<in>set (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl)). 
          set (get_outputs x) \<inter> Inputs (cl@[the (getOneRelatedBlock bl c cl)]) = {}"
        using True getOneRelatedBlockNone2 by simp
      then show ?thesis using InputsOutputs_forall by blast
    next
      case False
      then show ?thesis by blast
    qed
    have 10: "x \<notin> Outputs (getRelatedBlocks (remove1 
      (the (getOneRelatedBlock bl c cl)) bl) c (cl@[the (getOneRelatedBlock bl c cl)]))"
      using  getRelatedBlocks.simps[of bl c cl] False "2.prems"(9) by presburger
    have 11: "x \<notin> Outputs (findIntegBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl))"
      using findIntegBlks_remove getOneRelatedBlockOffset findIntegBlks_forall 
      by (meson "2.prems"(10) findIntegBlksSubset2 set_remove1_subset subsetD)
    have 12: "Unique (getCalBlks (remove1 (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
    proof -
      have "(the (getOneRelatedBlock bl c cl)) \<in> set (getCalBlks bl)"
      using False getOneRelatedBlock.simps "3" remove1_idem  getOneRelatedBlockCalBlks by simp
      then show ?thesis using Unique_Permutation by (metis "2.prems"(7) "4" getCalBlks_remove perm_remove3)
    qed
    have 13: "x \<in> Inputs ((remove1 (the (getOneRelatedBlock bl c cl)) bl) 
        @ (cl@[the (getOneRelatedBlock bl c cl)])) - Outputs ((remove1 
        (the (getOneRelatedBlock bl c cl)) bl) @ (cl@[the (getOneRelatedBlock bl c cl)]))"
      using 2(1,5,9) 3 4 5 6 7 8 9 10 11 12 False case_prodI 
        getRelatedBlocks.simps mem_Collect_eq by force
    have 14: "Outputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    Outputs (cl@[the (getOneRelatedBlock bl c cl)]) = Outputs bl \<union> Outputs cl"
      using False getOneRelatedBlockSubset by (metis (no_types, lifting) "3" Outputs_base 
          Outputs_base2 length_remove1 nat_neq_iff sup.commute sup.left_commute)
    have 15: "Inputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    Inputs (cl@[the (getOneRelatedBlock bl c cl)]) = Inputs bl \<union> Inputs cl"
      using False getOneRelatedBlockSubset "4" Inputs_base Inputs_base2 by blast
    then show ?thesis using 14 13 Inputs_Cons Outputs_Cons by auto
  qed
qed
  done

lemma getRelatedBlocksSubset : "Outputs (getRelatedBlocks bl c cl) \<subseteq> Outputs bl \<union> Outputs cl"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case 
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] getSortedBlocks_subset by auto
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "Outputs (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    Outputs (cl@[the (getOneRelatedBlock bl c cl)]) = Outputs bl \<union> Outputs cl"
      using False getOneRelatedBlockSubset by (metis (no_types, lifting) "3" Outputs_base 
          Outputs_base2 length_remove1 nat_neq_iff sup.commute sup.left_commute)
    have 5: "Outputs (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
    (cl@[the (getOneRelatedBlock bl c cl)])) \<subseteq> Outputs (remove1 (the 
    (getOneRelatedBlock bl c cl)) bl) \<union> Outputs (cl@[the (getOneRelatedBlock bl c cl)])"
      using 2 3 by blast
    then show ?thesis using 4 5 getSortedBlocks_subset by (simp add: False)
  qed
qed

lemma getRelatedBlocksSubset2 : "set (getRelatedBlocks bl c cl) \<subseteq> set bl \<union> set cl"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case 
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] getSortedBlocks_subset2 by auto
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "set (remove1 (the (getOneRelatedBlock bl c cl)) bl) \<union>
    set (cl@[the (getOneRelatedBlock bl c cl)]) \<subseteq> set bl \<union> set cl"
      using False getOneRelatedBlockSubset using "3" set_remove1_subset by fastforce
    have 5: "set (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c 
    (cl@[the (getOneRelatedBlock bl c cl)])) \<subseteq> set (remove1 (the 
    (getOneRelatedBlock bl c cl)) bl) \<union> set (cl@[the (getOneRelatedBlock bl c cl)])"
      using 2 3 by blast
    then show ?thesis using 4 5 using False by fastforce
  qed
qed

lemma getRelatedBlocksUnique: "Unique (bl@cl) \<Longrightarrow> Unique (getRelatedBlocks bl c cl)"
proof(induction bl arbitrary: cl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "getOneRelatedBlock bl c cl = None")
    case True
    then show ?thesis using 2(2) using getRelatedBlocks.simps[of bl c cl]
      using getSortedBlocks_Unique by metis
  next
    case False
    have 3: "length (remove1 (the (getOneRelatedBlock bl c cl)) bl) < length bl"
      using False getOneRelatedBlockSubset by (metis One_nat_def Suc_pred length_pos_if_in_set 
          length_remove1 lessI option.collapse)
    have 4: "Unique ((remove1 (the (getOneRelatedBlock bl c cl)) bl)
        @(cl @ [the (getOneRelatedBlock bl c cl)]))"
    proof -
      have tmp1: "\<forall>j. j < (length (remove1 (the (getOneRelatedBlock bl c cl)) 
        ((remove1 (the (getOneRelatedBlock bl c cl)) bl)@cl))) \<and> j \<ge> 0 \<longrightarrow> 
      (the (getOneRelatedBlock bl c cl)) \<noteq> (nth (remove1 (the (getOneRelatedBlock bl c cl)) 
      ((remove1 (the (getOneRelatedBlock bl c cl)) bl) @cl)) j)"      
        using Unique_k 2(2) by (metis Unique_remove nth_mem remove1_append remove1_idem)
      have tmp2: "(remove1 (the (getOneRelatedBlock bl c cl)) bl)@cl = 
            (remove1 (the (getOneRelatedBlock bl c cl)) (bl@cl))"
        using getOneRelatedBlockSubset by (metis "3" nat_less_le remove1_append remove1_idem)
      show ?thesis using tmp1 tmp2 Unique_remove getOneRelatedBlockSubset Unique_add2
        by (metis "2.prems" Unique_k append.assoc remove1_idem)
    qed
    have 5: "Unique (getRelatedBlocks (remove1 (the (getOneRelatedBlock bl c cl)) bl) c
           (cl @ [the (getOneRelatedBlock bl c cl)]))"
      using 2 3 4 by blast
    then show ?thesis using getRelatedBlocks.simps[of bl c cl] 5 False by presburger
  qed
qed


(*outputs_sorted block list; Integ blocks, Integ outputs vars return the blocks after combination*)
fun combination :: "ConBlk list \<Rightarrow> ConBlk list \<Rightarrow> ConBlk list" where
  "combination bl [] = []" |
  "combination bl (c#cl) = ((combineBlocks (getRelatedBlocks bl c []) c)#
  combination (remove1 c bl) cl)"

lemma combination_Inputssubset: "cl <~~> findIntegBlks bl \<Longrightarrow> wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>  
loop_free (getCalBlks bl) \<Longrightarrow> \<forall>c \<in> set cl. set (get_offsets c) = {1} \<Longrightarrow>
Inputs (combination bl cl) \<subseteq> (Inputs bl - Outputs bl) \<union> Outputs cl"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  have 1: "Inputs (combination (remove1 c bl) cl) \<subseteq> 
      (Inputs (remove1 c bl) - Outputs (remove1 c bl)) \<union> Outputs cl"
  proof -
    have tmp1: "cl <~~> findIntegBlks (remove1 c bl)"
    proof -
      have "findIntegBlks (remove1 c bl) = remove1 c (findIntegBlks bl)"
        using findIntegBlks_remove Cons(3) by simp
      then show ?thesis using perm_remove_perm Cons(2) by (metis remove_hd)
    qed
    have tmp2: "wf2 (remove1 c bl)"
      using Cons(2,3) by (metis remove1_idem wf2_remove)
    have tmp3: "Unique cl"
      using Cons(4) unfolding wf2_def using Unique_lemma by fastforce
    have tmp4: "(getCalBlks (remove1 c bl))  = (getCalBlks bl)"
      using Cons(6)
    proof(induction bl)
      case Nil
      then show ?case by auto
    next
      case (Cons b bl)
      then show ?case unfolding getCalBlks.simps by auto
    qed
    have tmp6: "c \<notin> set (remove1 c bl)"
      using Cons(3) unfolding wf2_def Unique_def by (metis Cons.prems(2) Unique_k 
          bot_nat_0.extremum in_set_conv_nth notin_set_remove1 wf2_def)
    have tmp8: "wf2 cl"
      using Cons(4) wf2_lemma by blast
    have tmp9: "loop_free (getCalBlks (remove1 c bl))"
      using tmp4 Cons(5) by simp
    have tmp10: "\<forall>c\<in>set cl. set (get_offsets c) = {1}"
      using Cons(6) by simp
    show ?thesis using Cons(1)[of "(remove1 c bl)"] tmp1 tmp2 tmp8 tmp9 tmp10 by simp
  qed
  have 2: "Inputs (remove1 c bl) - Outputs (remove1 c bl) \<union> Outputs cl \<subseteq>
      (Inputs bl - Outputs bl) \<union> Outputs (c # cl)"
  proof -
    have tmp1: "set (c # cl) \<subseteq> set bl"
      using Cons(2) by (simp add: Cons.prems(2) IntegCalUniun prem_seteq subset_code(1))
    have "Inputs (remove1 c bl) \<noteq> Inputs bl \<or> Outputs (remove1 c bl) \<noteq> Outputs bl \<or> Inputs (remove1 c bl) - Outputs (remove1 c bl) = Inputs bl - Outputs bl"
      by presburger
    then show ?thesis using tmp1 Cons(2) by (smt (verit, ccfv_threshold) Diff_subset_conv Inputs_base2 
          Outputs.simps(2) Outputs_base2 Set.set_insert Un_assoc insert_subset list.set_intros(1) 
          subset_Un_eq sup_ge1 sup_ge2 sup_least)
  qed
  have 3: "set (get_inputs (combineBlocks (getRelatedBlocks bl c []) c))
    \<subseteq> Inputs (c # getRelatedBlocks bl c []) - Outputs (getRelatedBlocks bl c [])"
  proof -
    have tmp1: "\<forall>b\<in>set (getRelatedBlocks bl c []). set (get_offsets b) = {0}"
      using getRelatedBlocksOffsets by (metis empty_iff empty_set)
    have tmp2: "\<forall>b\<in>set (getRelatedBlocks bl c []). Available' b"
      using getRelatedBlocksSubset2 Cons(3) unfolding wf2_def 
      by (metis empty_set in_mono sup_bot.right_neutral)
    have tmp3: "besorted2 (rev (getRelatedBlocks bl c []))"
      using getRelatedBlocks.simps[of bl c "[]"] getRelatedBlocks_besorted Cons(3,5) 
      by (simp add: getCalBlkswf)
    show ?thesis using combineBlocks_Inputssubset2[of "getRelatedBlocks bl c []" c] tmp1 tmp2
      tmp3 by auto
  qed
  have 4: "\<forall>x \<in> Inputs (getRelatedBlocks bl c []). x \<in> Outputs (getRelatedBlocks bl c []) \<or> 
      x \<in> Inputs bl - Outputs bl \<or> x \<in> Outputs (c # cl)"
  proof -
    have tmp1: "Outputs (c # cl) = Outputs (findIntegBlks bl)"
      using IntegCalOutputsUniun[of bl] Cons(2) Outputs_perm by presburger
    have tmp2: "c \<in> set bl"
      using Cons(2) by (meson findIntegBlksSubset3 list.set_intros(1) prem_seteq subset_iff)
    have tmp3: "set (get_offsets c) = {1}"
      by (simp add: Cons.prems(5))
    have tmp4: "Unique (getCalBlks bl)"
      using Cons(3) getCalBlkswf wf2_def by blast
    have tmp: "\<forall>x \<in> Inputs (getRelatedBlocks bl c []).
     x \<in> Outputs (getRelatedBlocks bl c []) \<or>
     x \<in> Inputs bl - Outputs bl \<or> x \<in> Outputs (findIntegBlks bl)"
      using getRelatedBlocksInputs2[of bl "[]" c] Cons(3,5) tmp2 tmp3 tmp4 by auto
    then show ?thesis using tmp1 by blast
  qed
  have 5: "\<forall>x \<in> set (get_inputs c). x \<in> Outputs (getRelatedBlocks bl c []) \<or> 
      x \<in> Inputs bl - Outputs bl \<or> x \<in> Outputs (c # cl)"
  proof -
    have tmp1: "Outputs (c # cl) = Outputs (findIntegBlks bl)"
      using IntegCalOutputsUniun[of bl] Cons(2) Outputs_perm by presburger
    have tmp2: "c \<in> set bl"
      using Cons(2) by (meson findIntegBlksSubset3 list.set_intros(1) prem_seteq subset_iff)
    have tmp3: "set (get_offsets c) = {1}"
      by (simp add: Cons.prems(5))
    have tmp4: "Unique (getCalBlks bl)"
      using Cons(3) getCalBlkswf wf2_def by blast
    have tmp: "\<forall>x\<in>set (get_inputs c).
     x \<in> Outputs (getRelatedBlocks bl c []) \<or>
     x \<in> Inputs bl - Outputs bl \<or> x \<in> Outputs (findIntegBlks bl)"
      using getRelatedBlocksInputs1[of bl "[]" c] Cons(3,5) tmp2 tmp3 tmp4 by auto
    then show ?thesis using tmp1 by blast
  qed
  (* b \<in> bl \<and> b \<notin> (c#cl)   2. b \<in> bl \<and> b \<in> (c#cl)  \<alpha> \<in> Inputs c \<union> Outputs bl *)
  then show ?case unfolding combination.simps using 1 2 3 4 unfolding Inputs.simps by blast
qed

lemma combination_funeq: "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
\<forall>b \<in> set (getCalBlks bl). \<forall>i. i \<ge> 0 \<and> i < length (get_outputs b) \<longrightarrow> 
h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda> a. h a t) (get_inputs b)) \<Longrightarrow>
i < length cl \<Longrightarrow> j < length (get_outupd (cl ! i)) \<Longrightarrow>
((get_outupd (cl ! i)) ! j) (map (\<lambda> a. h a t) (get_inputs (cl ! i))) = 
((get_outupd ((combination bl cl) ! i)) ! j) (map (\<lambda> a. h a t) (get_inputs ((combination bl cl) ! i)))"
proof(induction cl arbitrary: i j bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case
  proof(cases "i = 0")
    case True
    have 1: "(get_outupd c ! j) (map (\<lambda>a. h a t) (get_inputs c)) = (get_outupd (
(combineBlocks (getRelatedBlocks bl c []) c)) ! j) (map (\<lambda>a. h a t) (get_inputs
         (combineBlocks (getRelatedBlocks bl c []) c)))"
    proof -
      have tmp1: "\<forall>x\<in>set (getRelatedBlocks bl c []). 
              length (get_outputs x) = length (get_offsets x)"
        using getRelatedBlocksSubset2 Cons(2) unfolding wf2_def Available'_def 
        by (metis append_self_conv set_append subset_code(1))
      have tmp2: "\<forall>x\<in>set (getRelatedBlocks bl c []). length (get_outupd x) = length (get_offsets x)"
        using getRelatedBlocksSubset2 Cons(2) unfolding wf2_def Available'_def 
        by (metis append_self_conv set_append subset_code(1))
      have tmp3: "\<forall>x\<in>set (getRelatedBlocks bl c []). set (get_offsets x) = {0}"
        using getRelatedBlocksOffsets by (metis empty_iff empty_set)
      have tmp4: "\<forall>b\<in>set (getRelatedBlocks bl c []).
       \<forall>i<length (get_outputs b).
          h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b))"
      proof -
        have tmp1: "\<forall>b\<in>set bl. set (get_offsets b) = {0} \<longrightarrow> 
          b \<in> set (getCalBlks bl)"
        apply clarify subgoal for b
        proof(induction bl)
          case Nil
          then show ?case by auto
        next
          case (Cons b bl)
          then show ?case
          proof(cases "(set (get_offsets b)) = {0}")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          qed
        qed
        done
        have tmp: "set (getRelatedBlocks bl c []) \<subseteq> set (getCalBlks bl)"
          using tmp1 tmp3 getRelatedBlocksSubset2 by (metis empty_set subset_code(1) 
              sup_bot.right_neutral)
        then show ?thesis using Cons(5) by blast
      qed
      show ?thesis using combineBlocks_zero[of "getRelatedBlocks bl c []" h t c ] 
          getRelatedBlocksSubset2 tmp1 tmp2 tmp3 tmp4 Cons(7) by (smt (z3) True nth_Cons_0)
    qed
    then show ?thesis unfolding combination.simps by (simp add: True)
  next
    case False
    have 2: "wf2 (remove1 c bl)"
      using Cons(2,4) wf2_remove by simp
    have 3: "wf2 cl"
      using Cons(3) wf2_lemma by simp
    have 4: "set cl \<subseteq> set (remove1 c bl)"
      using Cons(2,3,4) unfolding wf2_def Unique_def by (metis Cons.prems(2) Unique_k 
          in_set_conv_nth in_set_remove1 less_nat_zero_code linorder_not_le remove_hd 
          set_subset_Cons subset_code(1) wf2_def)
    have 5: "\<forall>b\<in>set (getCalBlks (remove1 c bl)).
       \<forall>i. 0 \<le> i \<and> i < length (get_outputs b) \<longrightarrow>
           h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b))"
    proof -
      have tmp1: "set (getCalBlks (remove1 c bl)) \<subseteq> set (getCalBlks bl)"
      proof(induction bl)
        case Nil
        then show ?case by simp
      next
        case (Cons b bl)
        then show ?case unfolding getCalBlks.simps by auto
      qed
      then show ?thesis using Cons(5) by auto
    qed
    have 6: "i - 1 < length cl"
      using Cons(6) False by fastforce
    have 7: "j < length (get_outupd (cl ! (i - 1)))"
      using Cons(7) False by simp
    then show ?thesis unfolding combination.simps using Cons(1)[of "remove1 c bl" "i-1" j] 
      2 3 4 5 6 False nth_Cons' by auto
  qed
qed

lemma combination_outputeq: "i < length cl \<Longrightarrow>
(get_outputs (cl ! i))=  (get_outputs ((combination bl cl) ! i))"
proof(induction cl arbitrary: i bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case
  proof(cases "i = 0")
    case True
    have 1: "\<forall>x\<in>set (getRelatedBlocks bl c []). set (get_offsets x) = {0}"
      using getRelatedBlocksOffsets[of "[]"] by auto
    then show ?thesis unfolding combination.simps using combineBlocks_outputseq True 
      by (metis nth_Cons')
  next
    case False
    have 1: "i - 1 < length cl"
      using Cons(2) False by fastforce
    then show ?thesis unfolding combination.simps using Cons(1)[of "i-1" "remove1 c bl"] 
      by (simp add: False nth_Cons')
  qed
qed

lemma combination_wf2: "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>a \<in> set (combination bl cl). length (get_offsets a) = length (get_outputs a) \<and>
length (get_outputs a) = length (get_outupd a) \<and> 
(\<forall>i j. i < j \<and> j < (length (get_outputs a)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs a) i) \<noteq> (nth (get_outputs a) j))"
  apply clarify subgoal premises pre for a
    using pre
  proof(induction cl arbitrary:bl)
    case Nil
    then show ?case by simp
  next
    case (Cons c cl)
    then show ?case
    proof(cases "a = combineBlocks (getRelatedBlocks bl c []) c")
      case True
      have 1: "wf2 (getRelatedBlocks bl c [])"
        using getRelatedBlocksSubset2 getRelatedBlocksUnique Cons(2) unfolding wf2_def by (smt 
       (verit, best) Graph_def append.right_neutral empty_set in_mono sup_bot.right_neutral)
      have 2: "\<forall>x\<in>set (c # (getRelatedBlocks bl c [])).
       length (get_offsets x) = length (get_outputs x) \<and>
       length (get_outputs x) = length (get_outupd x) \<and>
       (\<forall>i j. i < j \<and> j < length (get_outputs x) \<and> 0 \<le> j \<longrightarrow>
              get_outputs x ! i \<noteq> get_outputs x ! j)"
          using 1 Cons(3) unfolding wf2_def Available'_def
          by (metis list.set_intros(1) set_ConsD)
        then show ?thesis using Cons combineBlocks_wf2[of c "(getRelatedBlocks bl c [])"] True
          unfolding combination.simps by fastforce
    next
      case False
      then show ?thesis using Cons unfolding combination.simps 
        by (metis remove1_idem set_ConsD wf2_lemma wf2_remove)
    qed
  qed
  done

lemma combination_lengtheq: "length cl = length (combination bl cl)"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons a cl)
  then show ?case unfolding combination.simps by auto
qed

lemma combination_outputsInter: "\<forall>i j. i < j \<and> j < length cl \<longrightarrow> set (get_outputs (cl ! i)) 
\<inter> set (get_outputs (cl ! j)) = {}
 \<Longrightarrow> \<forall>i j. i < j \<and> j < length (combination bl cl) \<longrightarrow> set (get_outputs ((combination bl cl) ! i)) 
\<inter> set (get_outputs ((combination bl cl) ! j)) = {}"
  using combination_outputeq combination_lengtheq by auto

lemma combinationEq : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
Outputs (combination bl cl) = Outputs cl"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  have 1: "Outputs (findIntegBlks (getRelatedBlocks bl c [])) \<subseteq> Outputs (c#cl)"
  proof -
    have tmp1: "Outputs (findIntegBlks bl) \<subseteq> Outputs (c#cl)"
    using Cons(4) proof(induction bl)
      case Nil
      then show ?case by simp
    next
      case (Cons b bl)
      then show ?case
      proof(cases "set (get_offsets b) = {1}")
        case True
        then show ?thesis using Cons unfolding findIntegBlks.simps
          using Cons.IH by auto
      next
        case False
        then show ?thesis unfolding findIntegBlks.simps using Cons by auto
      qed
    qed
    have tmp2: "Outputs (findIntegBlks (c#cl)) \<subseteq> Outputs (c#cl)"
      using findIntegBlksSubset by auto
    show ?thesis using getRelatedBlocksSubset2 tmp1 tmp2 by (metis empty_set 
          findIntegBlksSubset2 subset_eq sup_bot.right_neutral)
  qed
  have 2: "Outputs (combination (remove1 c bl) cl) = Outputs cl"
  proof -
    have tmp1: "c \<in> set bl"
      using Cons(6) by auto
    have tmp2: "wf2 (remove1 c bl)"
      using Cons(2) wf2_remove by (metis remove1_idem)
    have tmp3: "\<forall>b\<in>set (remove1 c bl). set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<inter> (set (get_outputs c)) = {}"
      using Cons(2,3) tmp1 unfolding wf2_def Unique_def Graph_def by (metis wf2_def 
          Cons.prems(1) Unique_k in_set_conv_nth linorder_not_le not_less0 notin_set_remove1)
    have tmp4: "\<forall>b\<in>set (remove1 c bl). set (get_offsets b) = {1} \<longrightarrow> 
      set (get_outputs b) \<subseteq> Outputs cl"
      using Cons(2,4) tmp1 by (smt (verit) Outputs.simps(2) Un_iff disjoint_iff_not_equal 
          in_mono notin_set_remove1 subsetI tmp3)
    have tmp5: "\<forall>c\<in>set cl. set (get_offsets c) = {1}"
      using Cons(5) by auto
    have tmp6: "set cl \<subseteq> set (remove1 c bl)"
      using Cons(3,5) unfolding wf2_def Unique_def Graph_def by (smt (verit, ccfv_threshold) 
          wf2_def Cons.prems(2) Cons.prems(5) Set.set_insert Unique_k in_set_conv_nth 
          in_set_remove1 insert_subset less_nat_zero_code linorder_not_le remove_hd set_subset_Cons subsetI)
    show ?thesis using Cons(1,3) tmp4 tmp2 tmp5 tmp6 using wf2_lemma by presburger
  qed
  have 3: "set (get_outputs (combineBlocks (getRelatedBlocks bl c []) c)) 
      = Outputs (c # findIntegBlks (getRelatedBlocks bl c []))"
  proof -
    have tmp1: "\<forall>b\<in>set (getRelatedBlocks bl c []). 
    set (get_offsets b) = {0} \<or> set (get_offsets b) = {1} \<or> set (get_offsets b) = {}"
      using Cons(2) unfolding wf2_def Available'_def using getRelatedBlocksSubset2
      by (metis empty_set in_mono sup_bot.right_neutral)
    have tmp2: "wf2 (getRelatedBlocks bl c [])"
    proof -
      have tmp1: "Unique (getRelatedBlocks bl c [])"
        using getRelatedBlocksUnique Cons(2) unfolding wf2_def by simp
      show ?thesis using getRelatedBlocksSubset2 tmp1 Cons(2) unfolding wf2_def
        by (smt (verit) Graph_def empty_set subset_code(1) sup_bot.right_neutral)
    qed
    show ?thesis using combineBlocksSubset4 getRelatedBlocksSubset2 tmp2 Cons(2) Cons(2) 
      unfolding wf2_def Available'_def by (metis combineBlocksSubset4 tmp2)
  qed
  then show ?case unfolding combination.simps using 3 by (smt (verit, best) "1" "2" Outputs.simps(2) Outputs_base2 Un_assoc le_iff_sup list.set_intros(1) remove_hd)
qed

lemma combinationOffsetsEq : "
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> 
\<forall>c \<in> set (combination bl cl). (set (get_offsets c) = {1})"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case unfolding combination.simps using combineBlocksOffsetEq 
    by (metis list.set_intros(1) list.set_intros(2) set_ConsD)
qed

lemma combinationEq2 : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow> \<forall>c \<in> set (combination bl cl).
length (get_outputs c) = length (get_offsets c) \<and> length (get_offsets c) = length (get_outupd c)"
proof(induction cl arbitrary: bl)
  case Nil
  then show ?case by simp
next
  case (Cons a cl)
  have 1: "wf2 (remove1 a bl)"
    using Cons(2) wf2_remove by (metis remove1_idem)
  have 2: "wf2 cl"
    using Cons(3) wf2_lemma by simp
  have 3: "set cl \<subseteq> set (remove1 a bl)"
    using Cons(2,3,4) unfolding wf2_def Unique_def by (metis wf2_def Cons.prems(2) Unique_k 
        in_set_conv_nth in_set_remove1 less_nat_zero_code linorder_not_less remove_hd 
        set_subset_Cons subset_code(1))
  have 4: "\<forall>c\<in>set (combination (remove1 a bl) cl).
       length (get_outputs c) = length (get_offsets c) \<and>
       length (get_offsets c) = length (get_outupd c)"
    using Cons(1) 1 2 3 by presburger
  have 5: "\<forall>b\<in>set (a#bl).
       length (get_offsets b) = length (get_outputs b) \<and>
       length (get_offsets b) = length (get_outupd b)"
    using Cons(2,3,4) unfolding wf2_def Available'_def
    by (metis list.set_intros(1) set_ConsD)
  then show ?case unfolding combination.simps using combineBlockEq2 4 getRelatedBlocksSubset2 
    by (smt (verit, ccfv_SIG) empty_set empty_subsetI le_supI list.set_intros(1) set_ConsD 
        set_subset_Cons subset_eq)
qed

text\<open>Combine all block list; used for combine all Integrator blocks\<close>
fun Combine :: "ConBlk list \<Rightarrow> ConBlk" where
  "Combine [] = (Block [] [] [] 0 [])" |
  "Combine (b#bl) = combineBlocks bl b"

lemma Combine_Inputssubset: "set (get_inputs (Combine bl)) \<subseteq> Inputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocks_Inputssubset by auto
qed

lemma Combine_funeq: "\<forall>a\<in>set bl.
       length (get_offsets a) = length (get_outputs a) \<and>
       length (get_outputs a) = length (get_outupd a) \<and>
       (\<forall>i j. i < j \<and> j < length (get_outputs a) \<and> 0 \<le> j \<longrightarrow> get_outputs a ! i \<noteq> get_outputs a ! j)
\<Longrightarrow>   \<forall>i j. i < j \<and> j < length bl \<longrightarrow>
          set (get_outputs (bl ! i)) \<inter> set (get_outputs (bl ! j)) =
          {} \<Longrightarrow> i < length (get_outputs b) \<Longrightarrow> j < length (get_outputs (Combine bl))
\<Longrightarrow> b \<in> set bl \<Longrightarrow> (get_outputs b) ! i = (get_outputs (Combine bl)) ! j \<Longrightarrow>
\<forall>x\<in>set bl. set (get_offsets x) = {1} \<Longrightarrow>
((get_outupd b) ! i) (map (\<lambda> a. h a t) (get_inputs b)) = 
((get_outupd (Combine bl)) ! j) (map (\<lambda> a. h a t) (get_inputs (Combine bl)))"
proof(induction bl )
  case Nil
  then show ?case by simp
next
  case (Cons c bl)
  have 1 :"(get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b)) =
    (get_outupd (combineBlocks bl c) ! j) (map (\<lambda>a. h a t) (get_inputs (combineBlocks bl c)))"
  proof -
    have tmp1: "\<forall>x\<in>set (c # bl).
       length (get_offsets x) = length (get_outputs x) \<and>
       length (get_offsets x) = length (get_outupd x) \<and>
       (\<forall>i j. i < j \<and> j < length (get_outputs x) \<and> 0 \<le> j \<longrightarrow>
              get_outputs x ! i \<noteq> get_outputs x ! j)"
      using Cons(2) unfolding wf2_def Available'_def by auto
    have tmp2: "\<forall>i j. i < j \<and> j < length (c # bl) \<longrightarrow>
          set (get_outputs ((c # bl) ! i)) \<inter> set (get_outputs ((c # bl) ! j)) = {}"
      using Cons(3) by simp
    show ?thesis using combineBlocks_funeq1[of b c bl i j h t] Cons(3,4,5,6,7,8) unfolding Combine.simps 
        using tmp1 tmp2 by blast
  qed
  then show ?case unfolding Combine.simps combineBlocks.simps by simp
qed
                             
lemma CombineSubset : "set (get_outputs (Combine bl)) \<subseteq> Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocksSubset by auto
qed

lemma CombineEq : "\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<and> length (get_offsets b) 
= length (get_outputs b) \<and> length (get_offsets b) = length (get_outupd b) \<Longrightarrow>
set (get_outputs (Combine bl)) = Outputs bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocksEq by auto
qed

lemma Combine_wf2: "\<forall>a \<in> set bl. length (get_offsets a) = length (get_outputs a) \<and>
length (get_outputs a) = length (get_outupd a) \<and> 
(\<forall>i j. i < j \<and> j < (length (get_outputs a)) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs a) i) \<noteq> (nth (get_outputs a) j)) \<Longrightarrow>
 length (get_offsets (Combine bl)) = length (get_outputs (Combine bl)) \<and>
length (get_outputs (Combine bl)) = length (get_outupd (Combine bl)) \<and> 
(\<forall>i j. i < j \<and> j < (length (get_outputs (Combine bl))) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs (Combine bl)) i) \<noteq> (nth (get_outputs (Combine bl)) j))"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons b bl)
  then show ?case unfolding Combine.simps using combineBlocks_wf2[of b bl] by fastforce
qed



text \<open>sorted by outputs; get the smallest block\<close>
fun get_first_block :: "ConBlk list \<Rightarrow> ConBlk" where
  "get_first_block [] = undefined" |
  "get_first_block [b] = b" |
  "get_first_block (b#bl) = (if (integer_of_char (hd (get_outputs (get_first_block bl))) \<ge> 
  integer_of_char (hd (get_outputs b))) then b else (get_first_block bl))"

lemma get_first_block_in : "get_first_block (a # cl) \<in> set (a#cl)"
proof(induction cl)
  case Nil
  then show ?case by simp
next
  case (Cons c cl)
  then show ?case unfolding get_first_block.simps using Cons by (smt (verit, ccfv_SIG) 
  getCalBlks.cases get_first_block.simps(2) get_first_block.simps(3) 
  insert_iff list.simps(15))
qed

lemma get_first_block_add: "get_first_block (b#bl) = b \<Longrightarrow>
(integer_of_char (hd (get_outputs c)) \<ge> integer_of_char (hd (get_outputs b))) \<Longrightarrow>
get_first_block (b#c#bl) = b"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "(integer_of_char (hd (get_outputs (get_first_block (a#bl)))) \<ge> 
  integer_of_char (hd (get_outputs b)))"
    using Cons(2) unfolding get_first_block.simps by (metis nle_le)
  then show ?case using Cons(3) unfolding get_first_block.simps by presburger
qed

lemma get_first_block_noteq: "get_first_block (b#bl) \<noteq> b \<Longrightarrow>
(integer_of_char (hd (get_outputs c)) > integer_of_char (hd (get_outputs (get_first_block bl)))) \<Longrightarrow>
get_first_block (b#c#bl) = get_first_block bl"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case  unfolding get_first_block.simps 
    by (smt (verit, best) linorder_not_less)
qed

lemma get_first_block_reomve1: "get_first_block (b#c#bl) = b \<Longrightarrow>
get_first_block (b#bl) = b"
  subgoal premises pre
proof(cases "bl = []")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis using pre unfolding get_first_block.simps
    by (smt (verit, ccfv_threshold) dual_order.trans get_first_block.simps(3) list.exhaust)
  qed
  done

lemma get_first_block_reomve2: "get_first_block (b#bl) = b \<Longrightarrow>
get_first_block (b#(remove1 c bl)) = b"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  have 1: "get_first_block (b # remove1 c bl) = b"
    using Cons get_first_block_reomve1 by blast
  have 2: "(integer_of_char (hd (get_outputs a)) \<ge> integer_of_char (hd (get_outputs b)))"
    using Cons(2) unfolding get_first_block.simps
    by (metis get_first_block.simps(3) get_first_block_reomve1 nle_le)
  then show ?case
  proof(cases "c = a")
    case True
    then show ?thesis using Cons by (metis get_first_block_reomve1 remove_hd)
  next
    case False
    have 3: "get_first_block (b # remove1 c (a # bl)) = get_first_block (b # a # remove1 c bl)"
      using False by auto
    then show ?thesis using 1 2 get_first_block_add by presburger
  qed
qed


lemma get_first_block_lemma : "get_first_block (b#bl) = b \<Longrightarrow> \<forall>c \<in> set bl. (integer_of_char 
(hd (get_outputs c)) \<ge> integer_of_char (hd (get_outputs b)))"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case using get_first_block_reomve1 unfolding get_first_block.simps
    by (metis nle_le set_ConsD)
qed

lemma get_first_block_remove3 : "wf2 bl \<Longrightarrow> b \<in> set bl \<Longrightarrow> get_first_block bl =
get_first_block (b#remove1 b bl)"
proof(induction bl)
  case Nil
  then show ?case by simp
next
  case (Cons a bl)
  then show ?case
  proof(cases "b = a")
    case True
    then show ?thesis by auto
  next
    case False
    note F1 = False
    have 0 : "wf2 bl"
      using Cons(2) wf2_lemma by simp
    have 1: "get_first_block bl = get_first_block (b # remove1 b bl)"
      using False Cons 0 by simp
    have 2: "bl = hd bl # tl bl"
      using Cons(3) False by (metis hd_Cons_tl in_set_member member_rec(2) set_ConsD)
    have 3: "b \<in> set bl"
      using False Cons by simp
    then show ?thesis
    proof(cases "get_first_block (a # bl) = a")
      case True
      have tmp1: "integer_of_char (hd (get_outputs b))
        \<ge> integer_of_char (hd (get_outputs a))"
        using True get_first_block.simps(3)[of a "hd bl" "tl bl"] get_first_block_lemma 
        3 by presburger
      have tmp2: "get_first_block (b # remove1 b (a # bl)) = get_first_block (b # a # remove1 b bl)"
        using F1 by auto
      have tmp3: "get_first_block (a # remove1 b bl) = a"
        using True get_first_block_reomve2 by presburger
      have tmp4: "set (get_outputs b) \<inter> set (get_outputs a) = {}"
        using Cons(2,3) unfolding wf2_def Graph_def by (metis False True get_first_block_in)
      have tmp5: "(get_outputs b) \<noteq> [] \<and> (get_outputs a) \<noteq> []"
        using Cons(2,3) unfolding wf2_def Available'_def by (metis Graph_def 
            list.set_intros(1) list.size(3) not_gr_zero)
      have tmp6: "hd (get_outputs b) \<noteq> hd (get_outputs a)"
        using tmp4 tmp5 by (simp add: disjoint_iff_not_equal)
      have tmp7: "integer_of_char (hd (get_outputs b))
        \<noteq> integer_of_char (hd (get_outputs a))"
        using tmp6 by (simp add: integer_of_char_def)
      have tmp8: "integer_of_char (hd (get_outputs b))
        > integer_of_char (hd (get_outputs a))"
        using tmp1 tmp7 by simp
      have tmp9: "get_first_block (b # a # remove1 b bl) = a"
        using tmp8 tmp3 unfolding get_first_block.simps by simp
      then show ?thesis using tmp2 tmp9 True by simp
    next
      case False
      note F2 = False
      have tmp1: "get_first_block (a # bl) = get_first_block (b # remove1 b bl)"
        using False 1 2 get_first_block.simps(3)[of a "hd bl" "tl bl"] by presburger
      then show ?thesis
      proof(cases "get_first_block (b # remove1 b bl) = b")
        case True
        then show ?thesis using tmp1 False
          using get_first_block.simps(3) get_first_block_reomve2 by presburger
      next
        case False
        have tmp2: "(integer_of_char (hd (get_outputs a)) > 
          integer_of_char (hd (get_outputs (get_first_block bl))))"
          using F2 2 get_first_block.simps(3)[of a "hd bl" "tl bl"] by (metis linorder_not_le) 
        then show ?thesis using get_first_block_noteq False by (smt (verit, del_insts) 
              get_first_block.elims list.discI list.inject remove1.simps(2) tmp1)
      qed
    qed
  qed
qed

lemma get_first_block_same : "wf2 bl1 \<Longrightarrow> bl1 \<noteq> [] \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow>
get_first_block bl1 = get_first_block bl2"
proof(induction bl1 arbitrary:bl2)
  case Nil
  then show ?case by simp
next
  case (Cons b1 bl1)
  have 0: "wf2 bl1"
    using Cons(2) wf2_lemma by simp
  then show ?case
  proof(cases "bl1 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have 1: "bl1 <~~> remove1 b1 bl2"
      using Cons(4) by (metis perm_remove_perm remove_hd)
    have 2: "get_first_block bl1 = get_first_block (remove1 b1 bl2)"
      using Cons(1) 0 1 False by simp
    have 3: "wf2 bl2"
      using wf2_lemma2 Cons(2,4) by auto
    have 4: "get_first_block bl2 = get_first_block (b1#(remove1 b1 bl2))"
      using get_first_block_remove3 3 by (meson Cons.prems(3) list.set_intros(1) prem_seteq)
    then show ?thesis using Cons 2 False unfolding get_first_block.simps
      by (smt (verit, best) "1" get_first_block.elims list.inject perm.Cons perm_sing_eq)
  qed
qed

text \<open>sorted by outputs\<close>
function sort_by_outputs :: "ConBlk list \<Rightarrow> ConBlk list" where
  "sort_by_outputs [] = []" |
  "sort_by_outputs (c#cl) = (let b = get_first_block (c#cl) in 
  b # (sort_by_outputs (remove1 b (c#cl)) ))"
  by pat_completeness auto
termination 
  apply (relation "measures[(\<lambda>(cl::ConBlk list). length cl)]", auto)
  subgoal premises pre for a cl
  proof -
    show ?thesis using get_first_block_in pre using perm_length perm_remove
      by (metis impossible_Cons linorder_not_le set_ConsD)
  qed
  done

lemma sort_by_outputs_Outputs : "Outputs (sort_by_outputs bl) = Outputs bl"
proof(induction bl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "bl = hd bl # tl bl"
      using False by simp
    have 4: "length (remove1 (get_first_block bl) bl) < length bl"
      using 3 get_first_block_in by (metis length_Cons lessI perm_length perm_remove)
    have 5: "Outputs bl = Outputs ((get_first_block bl)#(remove1 (get_first_block bl) bl))"
      using Outputs_remove 3 get_first_block_in by metis
    have 6: "Outputs (sort_by_outputs bl) = 
    Outputs ((get_first_block bl)#(sort_by_outputs (remove1 (get_first_block bl) bl)))"
      using 3 sort_by_outputs.simps(2)[of "hd bl" "tl bl"] by metis
    have 7: "Outputs (sort_by_outputs (remove1 (get_first_block bl) bl)) 
    = Outputs (remove1 (get_first_block bl) bl)"
      using 4 2 by blast
    then show ?thesis using 5 6 7 by auto
  qed
qed

lemma sort_by_outputs_perm1 : "(sort_by_outputs bl) <~~> bl"
proof(induction bl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis by simp
  next
    case False
    have 3: "bl = hd bl # tl bl"
      using False by simp
    have 4: "length (remove1 (get_first_block bl) bl) < length bl"
      using 3 get_first_block_in by (metis length_Cons lessI perm_length perm_remove)
    then show ?thesis by (metis "2" "3" case_prodI get_first_block_in mem_Collect_eq perm_remove2 
          sort_by_outputs.simps(2))
  qed
qed

lemma sort_by_outputs_perm2 : "wf2 bl1 \<Longrightarrow>
bl1 <~~> bl2 \<Longrightarrow> sort_by_outputs bl1 = sort_by_outputs bl2"
proof(induction bl1 arbitrary: bl2 rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def
    using length_induct by auto
next
  case (2 bl1)
  then show ?case
  proof(cases "bl1 = []")
    case True
    then show ?thesis using "2.prems" by blast
  next
    case False
    have 3: "bl1 = hd bl1 # tl bl1"
      using False by simp
    have 4: "bl2 = hd bl2 # tl bl2"
      using False 2(3) using list.exhaust_sel by blast
    have tmp1: "get_first_block bl1 = get_first_block bl2"
      using 3 4 2(2,3) False get_first_block_same by presburger
    have tmp2: "remove1 (get_first_block bl1) bl1 <~~> remove1 (get_first_block bl2) bl2"
      using tmp1 2(3) by (simp add: perm_remove_perm)
    have tmp3: "wf2 (remove1 (get_first_block bl1) bl1)"
      using 2(2) get_first_block_in wf2_remove by (metis remove1_idem)
    have tmp4: "length (remove1 (get_first_block bl1) bl1) < length bl1"
      using get_first_block_in by (metis "3" length_Cons lessI perm_length perm_remove)
    then show ?thesis using 2 tmp2 tmp3 tmp4
      by (metis "3" "4" case_prod_conv mem_Collect_eq sort_by_outputs.simps(2) tmp1)
  qed
qed

lemma sort_by_outputs_wf2 : "wf2 bl \<Longrightarrow> wf2 (sort_by_outputs bl)"
proof(induction bl rule: wf_induct[of "{(x, y). length x < length y}"])
  case 1
  then show ?case unfolding wf_def using length_induct by auto
next
  case (2 bl)
  then show ?case
  proof(cases "bl = []")
    case True
    then show ?thesis using "2.prems" by force
  next
    case False
    have 3: "bl = hd bl # tl bl"
      using False by simp
    have 4: "length (remove1 (get_first_block bl) bl) < length bl"
      using 3 get_first_block_in by (metis length_Cons lessI perm_length perm_remove)
    have 5: "wf2 (remove1 (get_first_block bl) bl)"
      using 4 2 wf2_remove by (metis remove1_idem)
    then show ?thesis using  5 by (meson "2.prems" perm_sym sort_by_outputs_perm1 wf2_lemma2)
  qed
qed


(*all continuousBlocks; Integ blocks, return the combined block after combination*)
\<comment> \<open>note: root function for combination!!!\<close>
fun updateIntegBlks :: "ConBlk list \<Rightarrow> ConBlk list \<Rightarrow> ConBlk" where
  "updateIntegBlks bl cl = Combine (combination (sort_by_outputs bl) (sort_by_outputs cl))"

lemma updateIntegBlks_funeq: "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
\<forall>b \<in> set (getCalBlks bl). \<forall>i. i \<ge> 0 \<and> i < length (get_outputs b) \<longrightarrow> 
h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda> a. h a t) (get_inputs b)) \<Longrightarrow>
c \<in> set cl \<Longrightarrow> i < length (get_outputs c) \<Longrightarrow> j < length (get_outputs (updateIntegBlks bl cl)) \<Longrightarrow>
(get_outputs c) ! i = (get_outputs (updateIntegBlks bl cl)) ! j \<Longrightarrow>
\<forall>c\<in>set cl. set (get_offsets c) = {1} \<Longrightarrow>
((get_outupd c) ! i) (map (\<lambda> a. h a t) (get_inputs c)) = 
((get_outupd (updateIntegBlks bl cl)) ! j) (map (\<lambda> a. h a t) (get_inputs (updateIntegBlks bl cl)))"
  subgoal premises pre
  proof -
    obtain k1 where 1: "(sort_by_outputs cl) ! k1 = c \<and> k1 < length (sort_by_outputs cl)"
      using pre sort_by_outputs_perm1 by (meson in_set_conv_nth perm_sym prem_seteq)
    have 2: "(get_outupd c ! i) (map (\<lambda>a. h a t) (get_inputs c)) =
    (get_outupd (combination (sort_by_outputs bl) (sort_by_outputs cl) ! k1) ! i) 
      (map (\<lambda>a. h a t) (get_inputs (combination (sort_by_outputs bl) (sort_by_outputs cl) ! k1)))"
    proof -
      have tmp1: "wf2 (sort_by_outputs bl)"
        using pre(1) sort_by_outputs_perm1 by (simp add: sort_by_outputs_wf2)
      have tmp2: "wf2 (sort_by_outputs cl)"
        using pre(2) sort_by_outputs_perm1 by (simp add: sort_by_outputs_wf2)
      have tmp3: "set (sort_by_outputs cl) \<subseteq> set (sort_by_outputs bl)"
        using pre(3) sort_by_outputs_perm1 by (metis perm_sym prem_seteq subsetI subset_antisym)
      have tmp4: "\<forall>b\<in>set (getCalBlks (sort_by_outputs bl)).
     \<forall>i. 0 \<le> i \<and> i < length (get_outputs b) \<longrightarrow>
         h (get_outputs b ! i) t = (get_outupd b ! i) (map (\<lambda>a. h a t) (get_inputs b))"
        using pre(4) sort_by_outputs_perm1 by (meson getCalBlksPerm prem_seteq)
      have tmp5: "i < length (get_outupd (sort_by_outputs cl ! k1))"
        using pre(2,6) 1 unfolding wf2_def Available'_def by (simp add: pre(5))
      show ?thesis using combination_funeq[of "(sort_by_outputs bl)" "(sort_by_outputs cl)" h t k1 i] 
        using tmp1 tmp2 tmp3 tmp4 tmp5 1 by simp
    qed
    obtain b k2 where 3: "b = combination (sort_by_outputs bl) (sort_by_outputs cl) ! k1 \<and>
  get_outputs b ! k2 = (get_outputs (updateIntegBlks bl cl)) ! j
  \<and> k2 < length (get_outputs b)"
      using pre(8) unfolding updateIntegBlks.simps using combination_outputeq 1 pre(6) by auto
  have 4: "(get_outupd (combination (sort_by_outputs bl) (sort_by_outputs cl) ! k1) ! i) 
      (map (\<lambda>a. h a t) (get_inputs (combination (sort_by_outputs bl) (sort_by_outputs cl) ! k1))) =
    (get_outupd b ! k2) (map (\<lambda>a. h a t) (get_inputs b))"
    using 1 3 pre(2,5,6,8) by (metis  Available'_def combination_outputeq gr_implies_not0 
        linorder_neqE_nat linorder_not_le wf2_def)
  have 5: "(get_outupd b ! k2) (map (\<lambda>a. h a t) (get_inputs b)) =
    (get_outupd (Combine (combination (sort_by_outputs bl) (sort_by_outputs cl))) ! j)
     (map (\<lambda>a. h a t) (get_inputs (Combine (combination (sort_by_outputs bl) (sort_by_outputs cl)))))"
  proof -
    have tmp1: "wf2 (sort_by_outputs bl)"
      using pre(1) sort_by_outputs_perm1 by (simp add: sort_by_outputs_wf2)
    have tmp2: "wf2 (sort_by_outputs cl)"
      using pre(2) sort_by_outputs_perm1 by (simp add: sort_by_outputs_wf2)
    have tmp3: "\<forall>a\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)).
     length (get_offsets a) = length (get_outputs a) \<and>
     length (get_outputs a) = length (get_outupd a) \<and>
     (\<forall>i j. i < j \<and> j < length (get_outputs a) \<and> 0 \<le> j \<longrightarrow> get_outputs a ! i \<noteq> get_outputs a ! j)"
      using combination_wf2 tmp1 tmp2 by simp
    have tmp4: "\<forall>i j. i < j \<and> j < length (sort_by_outputs cl) \<longrightarrow>
          set (get_outputs ((sort_by_outputs cl) ! i)) \<inter> set (get_outputs ((sort_by_outputs cl) ! j)) = {}"
      using tmp2 unfolding wf2_def Unique_def Graph_def 
      by (meson dual_order.strict_trans less_eq_nat.simps(1) nth_mem)
    have tmp5: "\<forall>i j. i < j \<and> j < length (combination (sort_by_outputs bl) (sort_by_outputs cl)) \<longrightarrow>
        set (get_outputs (combination (sort_by_outputs bl) (sort_by_outputs cl) ! i)) \<inter>
        set (get_outputs (combination (sort_by_outputs bl) (sort_by_outputs cl) ! j)) =
        {}"
      using combination_outputsInter tmp4 by presburger
    have tmp6: "j < length (get_outputs (Combine (combination (sort_by_outputs bl) (sort_by_outputs cl))))"
      using pre(7) by auto
    have tmp7: "b \<in> set (combination (sort_by_outputs bl) (sort_by_outputs cl))"
      using 3 "1" combination_lengtheq by auto
    have tmp8: "\<forall>x\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)). set (get_offsets x) = {1}"
      using combinationOffsetsEq pre(9) by (meson prem_seteq sort_by_outputs_perm1)
    show ?thesis using Combine_funeq[of "(combination (sort_by_outputs bl) (sort_by_outputs cl))" 
          k2 b j h t] 3 tmp3 tmp5 tmp6 tmp7 tmp8 by auto
  qed
  show ?thesis using 2 4 5 by auto
qed
  done


lemma updateIntegBlksSubset : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
set (get_outputs (updateIntegBlks bl cl)) \<subseteq> Outputs cl"
  subgoal premises pre
proof -
  have 1: "wf2 (sort_by_outputs bl)"
    using pre(1) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 2: "wf2 (sort_by_outputs cl)"
    using pre(2) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  then show ?thesis unfolding updateIntegBlks.simps using sort_by_outputs_Outputs
combinationEq[of "sort_by_outputs bl" "sort_by_outputs cl" ] CombineSubset by (smt (verit, best) 
    "1" perm_sym pre(3) pre(4) pre(5) prem_seteq sort_by_outputs_perm1 subset_eq)
qed
  done

\<comment> \<open>Combination doesn't add or delete the outputs\<close>
lemma updateIntegBlksSubset2 : "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow>
\<forall>b \<in> set bl. (set (get_offsets b) = {1}) \<longrightarrow> set (get_outputs b) \<subseteq> Outputs cl \<Longrightarrow>
\<forall>c \<in> set cl. (set (get_offsets c) = {1}) \<Longrightarrow> set cl \<subseteq> set bl \<Longrightarrow>
set (get_outputs (updateIntegBlks bl cl)) = Outputs cl"
  subgoal premises pre
proof -
  have 1: "wf2 (sort_by_outputs bl)"
    using pre(1) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 2: "wf2 (sort_by_outputs cl)"
    using pre(2) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
  have 3: "\<forall>b\<in>set (sort_by_outputs bl).
       set (get_offsets b) = {1} \<longrightarrow> set (get_outputs b) \<subseteq> Outputs (sort_by_outputs cl)"
    using pre(3) by (metis prem_seteq sort_by_outputs_Outputs sort_by_outputs_perm1)
  have 4: "\<forall>c\<in>set (sort_by_outputs cl). set (get_offsets c) = {1}"
    using pre(4) by (meson prem_seteq sort_by_outputs_perm1)
  have 5: "set (sort_by_outputs cl) \<subseteq> set (sort_by_outputs bl)"
    using pre(5) by (meson in_mono perm_sym prem_seteq sort_by_outputs_perm1 subsetI)
  have 6: "\<forall>b\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)). 
    set (get_offsets b) = {1}"
    using combinationOffsetsEq 4 by blast
  have 7: "\<forall>b\<in>set (combination (sort_by_outputs bl) (sort_by_outputs cl)).
       set (get_offsets b) = {1} \<and>
       length (get_offsets b) = length (get_outputs b) \<and>
       length (get_offsets b) = length (get_outupd b)"
    using 6 pre(1) combinationEq2 1 2 5 by presburger
  then show ?thesis unfolding updateIntegBlks.simps using sort_by_outputs_Outputs
combinationEq[of "sort_by_outputs bl" "sort_by_outputs cl" ] CombineEq 1 2 3 4 5 6 7 by presburger
qed
  done

lemma updateIntegBlksPerm : "wf2 bl1 \<Longrightarrow> wf2 cl1 \<Longrightarrow> bl1 <~~> bl2 \<Longrightarrow> cl1 <~~> cl2 \<Longrightarrow>
updateIntegBlks bl1 cl1 = updateIntegBlks bl2 cl2"
  unfolding updateIntegBlks.simps using sort_by_outputs_perm2 by presburger

lemma updateIntegBlks_wf2: "wf2 bl \<Longrightarrow> wf2 cl \<Longrightarrow> (length (get_offsets (updateIntegBlks bl cl))) 
= (length (get_outputs (updateIntegBlks bl cl))) \<and> ((length (get_outputs (updateIntegBlks bl cl))) 
= (length (get_outupd (updateIntegBlks bl cl)))) \<and> (\<forall>i j. i < j \<and> j < 
(length (get_outputs (updateIntegBlks bl cl))) \<and> j \<ge> 0 
  \<longrightarrow> (nth (get_outputs (updateIntegBlks bl cl)) i) \<noteq> (nth (get_outputs (updateIntegBlks bl cl)) j))"
  unfolding updateIntegBlks.simps Combine.simps using sort_by_outputs_wf2 
Combine_wf2 combination_wf2 by (smt (verit, ccfv_threshold))

lemma updateIntegBlks_inputsSubset: "wf2 bl \<Longrightarrow> loop_free (getCalBlks bl) \<Longrightarrow>
set (get_inputs (updateIntegBlks bl (findIntegBlks bl))) -
set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) \<subseteq> Inputs bl - Outputs bl"
  subgoal premises pre
  proof -
    have 1: "Inputs (combination (sort_by_outputs bl) (sort_by_outputs (findIntegBlks bl))) 
      \<subseteq> Inputs (sort_by_outputs bl) - Outputs (sort_by_outputs bl) \<union>
       Outputs (sort_by_outputs (findIntegBlks bl))"
    proof -
      have 1: "wf2 (sort_by_outputs bl)"
        using pre(1) sort_by_outputs_perm1 wf2_lemma2 by (meson perm_sym)
      have 2: "loop_free (getCalBlks (sort_by_outputs bl))"
        using pre(2) sort_by_outputs_perm1 getCalBlksPerm loop_free_perm 1
        by (meson getCalBlkswf perm_sym pre(1) wf2_def)
      have 3: "set (sort_by_outputs (findIntegBlks bl)) \<subseteq> set (sort_by_outputs bl)"
        using findIntegBlksSubset3 sort_by_outputs_perm1 
        by (meson perm_sym prem_seteq subset_iff)
      have 4: "Unique (sort_by_outputs (findIntegBlks bl))"
        using findIntegBlkswf pre(1) sort_by_outputs_perm1 unfolding wf2_def 
        by (metis sort_by_outputs_wf2 wf2_def)
      have 5: "Outputs (sort_by_outputs bl) =Outputs 
      (getCalBlks (sort_by_outputs bl)) \<union> Outputs (sort_by_outputs (findIntegBlks bl))"
        using pre(1) IntegCalOutputsUniun sort_by_outputs_perm1 
        by (metis Outputs_perm getCalBlksPerm)
      have 6: "\<forall>c\<in>set (sort_by_outputs (findIntegBlks bl)). set (get_offsets c) = {1}"
        using findIntegBlks_forall sort_by_outputs_perm1 by (meson prem_seteq)
      have 7: "wf2 (sort_by_outputs (findIntegBlks bl))"
        using wf2_lemma2 findIntegBlkswf pre(1) sort_by_outputs_wf2 by blast
      have 8: "sort_by_outputs (findIntegBlks bl) <~~> findIntegBlks (sort_by_outputs bl)"
        using findIntegBlksPerm sort_by_outputs_perm1 by (meson perm.trans perm_sym)
      show ?thesis using combination_Inputssubset[of "(sort_by_outputs (findIntegBlks bl))"
            "(sort_by_outputs bl)" ] 1 2 3 4 5 6 7 8 by auto
    qed
    have 2: "Inputs (sort_by_outputs bl) - Outputs (sort_by_outputs bl) \<union> Outputs 
  (sort_by_outputs (findIntegBlks bl)) = Inputs bl - Outputs bl \<union> Outputs (findIntegBlks bl)"
      using Inputs_perm Outputs_perm sort_by_outputs_perm1 by metis
    have 3: "set (get_outputs (updateIntegBlks bl (findIntegBlks bl))) = Outputs (findIntegBlks bl)"
    proof -
      have tmp1: "wf2 (findIntegBlks bl)"
        using pre(1) findIntegBlkswf by auto
      have tmp2: "\<forall>b\<in>set bl. set (get_offsets b) = {1} \<longrightarrow> 
          set (get_outputs b) \<subseteq> Outputs (findIntegBlks bl)"
        apply clarify subgoal for b x
        proof(induction bl)
          case Nil
          then show ?case by auto
        next
          case (Cons b bl)
          then show ?case
          proof(cases "(set (get_offsets b)) = {1}")
            case True
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          next
            case False
            then show ?thesis unfolding findIntegBlks.simps using Cons by auto
          qed
        qed
        done
      have tmp3: "\<forall>c\<in>set (findIntegBlks bl). set (get_offsets c) = {1}"
        using findIntegBlks_forall by simp
      have tmp4: "set (findIntegBlks bl) \<subseteq> set bl"
        using findIntegBlksSubset3 by simp
      show ?thesis using updateIntegBlksSubset2 pre(1) tmp1 tmp2 tmp3 tmp4 by auto
    qed
    have 4: "set (get_inputs (updateIntegBlks bl (findIntegBlks bl))) \<subseteq> Inputs bl - Outputs bl \<union>
     Outputs (findIntegBlks bl)"
      unfolding updateIntegBlks.simps using Combine_Inputssubset 1 2 by blast
  have 5: "set (get_inputs (updateIntegBlks bl (findIntegBlks bl))) \<subseteq> Inputs bl - Outputs bl \<union>
    set (get_outputs (updateIntegBlks bl (findIntegBlks bl)))"
    using 4 3 by simp
  then show ?thesis unfolding updateIntegBlks.simps by auto
qed
  done

\<comment> \<open>End section\<close>

section \<open>definitions and theorems for translating block to ODE\<close>


text \<open>Before calculation, we get the min time step based on the discrete 
blocks(greatest common divisor)\<close>
fun commonDivisor:: "int \<Rightarrow> DisBlk list \<Rightarrow> int" where
  "commonDivisor x [] = x" |
  "commonDivisor x (a#al) = commonDivisor (gcd x (get_sample_time a)) al"
fun getTimeStep:: "DisBlk list \<Rightarrow> int" where
  "getTimeStep [] = 1" | 
  "getTimeStep (a#al) = commonDivisor (get_sample_time a) al"

value "getTimeStep [Block ''za'' ''a'' [1] 12 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))]
, Block ''za'' ''a'' [1] 18 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))],
Block ''za'' ''a'' [1] 30 [(\<lambda>s.(if length s = 2 then (s ! 0) + (s ! 1) else 0))]]"

text \<open>State\<close>
type_synonym state = "var \<Rightarrow> real"

text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

definition zeroExp :: "exp" where "zeroExp = (\<lambda>s.0)"

text \<open>States as a vector\<close>
type_synonym vec = "real^(var)"

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma transform_eq1: "s1 = s2 \<Longrightarrow> state2vec s1 = state2vec s2"
  by simp

lemma transform_eq2: "v1 = v2 \<Longrightarrow> vec2state v1 = vec2state v2"
  by simp

subsection \<open>Definition of ODEs\<close>

type_synonym ODE = "var \<Rightarrow> exp"

(*time; values; derivatives*)
type_synonym ODE' = "real \<Rightarrow> vec \<Rightarrow> vec"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_eq: "\<forall>x. (v1::vec) $ x = v2 $ x \<Longrightarrow> v1 = v2"
  subgoal premises pre
proof -
  have 1: "\<forall>x. (vec2state v1) x = (vec2state v2) x"
    unfolding vec2state_def using pre by simp
  have 2: "(vec2state v1) = (vec2state v2)"
    using 1 by blast
  show ?thesis using 2 transform_eq1 vec_state_map2 by metis
qed
  done

text \<open>transformation between timed_vars and state\<close>
definition timedVar2timedState :: "timed_vars \<Rightarrow> (real \<Rightarrow> state)" where
  "timedVar2timedState h = (\<lambda>t. (\<lambda>v. (h v t)))"
                                                                  
definition timedVar2State :: "timed_vars \<Rightarrow> real \<Rightarrow> state" where
  "timedVar2State h t = (\<lambda>v. h v t)"

definition timedState2timedVar :: "(real \<Rightarrow> state) \<Rightarrow> timed_vars" where
  "timedState2timedVar p = (\<lambda>v. (\<lambda>t. p t v))"

lemma timedVar_state_map1[simp]: "timedState2timedVar (timedVar2timedState h) = h"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp

lemma timedVar_state_map2[simp]: "timedVar2timedState (timedState2timedVar p) = p"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp


fun exp2ODE :: "var list \<Rightarrow> exp list \<Rightarrow> ODE" where
  "exp2ODE [] Exps s = zeroExp" |
  "exp2ODE xs [] s = zeroExp" |
  "exp2ODE (x#xs) (Exp#Exps) s =(if x = s then Exp else (exp2ODE xs Exps s))"


text \<open>transformation between outupd and expression\<close>
definition outupd2exp :: "outupd \<Rightarrow> var list \<Rightarrow> exp" where
  "outupd2exp f il = (\<lambda>s. (f (map (\<lambda> a. s a) il)) )"

lemma outupd2exp_valeq: "\<forall>x \<in> set il. h1 x t = h2 x t \<Longrightarrow>
outupd2exp f il (timedVar2timedState h1 t) = f (map (\<lambda>a. h2 a t) il)"
  unfolding outupd2exp_def timedVar2timedState_def 
  by (smt (verit, best) map_eq_conv)

lemma exp2ODE_ith: "v1 \<in> set vl \<Longrightarrow> v2 \<notin> set vl \<Longrightarrow>
(\<forall>i j. i < j \<and> j < (length vl) \<and> j \<ge> 0 \<longrightarrow> (nth vl i) \<noteq> (nth vl j)) \<Longrightarrow>
state2vec (\<lambda>x. exp2ODE vl Exps x h) $ v1
= state2vec (\<lambda>x. exp2ODE (v2#vl) (Exp#Exps) x h) $ v1"
proof(induction vl arbitrary:Exps)
  case Nil
  then show ?case by simp
next
  case (Cons v vl)
  then show ?case
  proof(cases "v1 = v")
    case True
    then show ?thesis
    proof(cases "Exps = []")
      case True
      then show ?thesis using Cons.prems(1) Cons.prems(2) state2vec_def by force
    next
      case False
      have 1: "Exps = hd Exps #(tl Exps)" 
        using False by simp
      then show ?thesis using Cons.prems(1) Cons.prems(2) state2vec_def by fastforce
    qed
  next
    case False
    then show ?thesis
    proof(cases "Exps = []")
      case True
      then show ?thesis using Cons.prems(1) Cons.prems(2) state2vec_def by force
    next
      case False
      then show ?thesis using Cons.prems(1) Cons.prems(2) state2vec_def by force
    qed
  qed
qed

lemma ToExpEq : "\<forall>s. (f1 (map (\<lambda> a. s a) il1)) = (f2 (map (\<lambda> a. s a) il2))
\<Longrightarrow> outupd2exp f1 il1 = outupd2exp f2 il2"
  unfolding outupd2exp_def by simp

value "integer_of_char CHR ''a'' < integer_of_char CHR ''b''"

definition exp2outupd :: "exp \<Rightarrow> var list \<Rightarrow> outupd" where
  "exp2outupd Exp il = undefined"

(*outupd list to expression list*)
fun getExps :: "outupd list \<Rightarrow> var list \<Rightarrow> exp list" where
  "getExps [] il = []" |
  "getExps (f#fl) il = outupd2exp f il # (getExps fl il)"

lemma getExpsPerm : "\<forall>i. i \<ge> 0 \<and> i < length fl1 \<longrightarrow> (\<forall>s. ((fl1 ! i) (map (\<lambda> a. s a) il1)) = 
((fl2 ! i) (map (\<lambda> a. s a) il2))) \<Longrightarrow> length fl1 = length fl2
\<Longrightarrow> getExps fl1 il1 = getExps fl2 il2"
proof(induction fl1 arbitrary:fl2)
  case Nil
  then show ?case by simp
next
  case (Cons f1 fl1)
  have 1: "fl2 = hd fl2 # tl fl2"
    using Cons(3) by (metis length_0_conv list.exhaust_sel neq_Nil_conv)
  have 2: "outupd2exp f1 il1 = outupd2exp (hd fl2) il2"
    using Cons(2) by (metis "1" ToExpEq length_Cons nth_Cons_0 of_nat_0 of_nat_0_le_iff zero_less_Suc)
  have 3: "getExps fl1 il1 = getExps (tl fl2) il2"
    using Cons 1 by (metis (no_types, lifting) Suc_mono length_Cons length_tl linorder_le_cases 
        list.sel(3) not_less_eq_eq nth_tl)
  then show ?case using 1 2 3 getExps.simps(2)[of "hd fl2" "tl fl2" il2] unfolding getExps.simps 
    using \<open>getExps (hd fl2 # tl fl2) il2 = outupd2exp (hd fl2) il2 # getExps (tl fl2) il2\<close> by presburger
qed


fun ODE2vec :: "ODE  \<Rightarrow> (vec \<Rightarrow> vec)" where
  "ODE2vec ode v1 = state2vec (\<lambda>x.(ode x (vec2state v1)))"

lemma ODE2vec_valeq: "ode v (vec2state v1) = x \<Longrightarrow>
ODE2vec ode v1 $ v = x"
  unfolding ODE2vec.simps by (simp add: state2vec_def)

fun realvec2realstate :: "(real \<Rightarrow> vec) \<Rightarrow> (real \<Rightarrow> state)" where
  "realvec2realstate p t = vec2state (p t)"

fun realstate2realvec :: "(real \<Rightarrow> state) \<Rightarrow> (real \<Rightarrow> vec)" where
  "realstate2realvec p t = state2vec (p t)"

lemma timedVar_state_map3[simp]: "timedState2timedVar (realvec2realstate
(realstate2realvec (timedVar2timedState h))) = h"
  unfolding timedVar2timedState_def timedState2timedVar_def by simp

lemma timedVar_state_map4[simp]: "(realstate2realvec (timedVar2timedState
          (timedState2timedVar (realvec2realstate p)))) = p"
  unfolding timedVar2timedState_def timedState2timedVar_def realstate2realvec.simps by simp

lemma trans_eq3: "\<forall>x t. (h1::timed_vars) x t = h2 x t \<longrightarrow> 
(realstate2realvec (timedVar2timedState h1)) t $ x =
  (realstate2realvec (timedVar2timedState h2)) t $ x"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using state2vec_def by force

lemma trans_eq4: "\<forall>x t. (h1::timed_vars) x t = v2 t $ x \<longrightarrow> 
(realstate2realvec (timedVar2timedState h1)) t $ x = v2 t $ x"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using state2vec_def by force

lemma trans_eq5: "(realstate2realvec (timedVar2timedState h)) t = 
  state2vec (\<lambda>v. h v t)"
  unfolding realstate2realvec.simps timedVar2timedState_def
  using timedVar2State_def by force

lemma trans_eq6: "\<forall>t. h1 v t = h2 v t \<Longrightarrow>  
  (\<lambda>t. (realstate2realvec (timedVar2timedState h1)) t $ v) =
  (\<lambda>t. (realstate2realvec (timedVar2timedState h2)) t $ v)"
  using trans_eq3 by blast

(*update h for the outputs and time interval (t0, t0+t]*)
fun updTimedVar :: "(real \<Rightarrow> vec) \<Rightarrow> var list \<Rightarrow> timed_vars \<Rightarrow> real \<Rightarrow> real \<Rightarrow> timed_vars" where
  "updTimedVar p vl h t0 t v tt =(if v \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0+t) 
    then (p tt $ v) else h v tt)"

lemma updTimedVar_eq1 : "\<forall> v tt. v  \<notin> set vl \<or> (tt \<le> t0 \<or> tt > t0 + t) \<longrightarrow> 
      updTimedVar p vl h t0 t v tt = h v tt"
  unfolding updTimedVar.simps by simp

lemma updTimedVar_eq2 : "\<forall> v tt. v  \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0 + t) \<longrightarrow> 
      updTimedVar p vl h t0 t v tt = (p tt $ v)"
  unfolding updTimedVar.simps by simp

lemma updTimedVar_eq3: "updTimedVar p vl h t0 t = (\<lambda>vv tt. (if vv \<in> set vl \<and> (tt > t0 \<and> tt \<le> t0 + t)
  then (p tt $ vv) else h vv tt))"
  using updTimedVar_eq1 updTimedVar_eq2 by fastforce



text \<open>give a block including ODE, return a function(real => ODE => ODE)
) required by the definition of "fixed_point"\<close>
fun block2ODE :: "block \<Rightarrow> ODE'" where
  "block2ODE (Block il vl ol st fl) t v1 = ODE2vec (exp2ODE vl (getExps fl il)) v1"

lemma blockODE_zero: "length vl = length fl \<Longrightarrow>
\<forall>x. x \<notin> set vl \<longrightarrow> (\<forall>t v1. (block2ODE (Block il vl ol st fl) t v1) $ x = 0)"
  apply clarify subgoal premises pre for x t v1
    using pre unfolding block2ODE.simps 
proof(induction fl arbitrary: vl )
  case Nil
  have 1: "\<forall>s. exp2ODE vl [] s = zeroExp"
    using exp2ODE.elims by blast
  then show ?case unfolding getExps.simps exp2ODE.simps using 1 apply simp unfolding zeroExp_def
    state2vec_def by simp
next
  case (Cons f fl)
  have 2: "vl = hd vl # tl vl"
    using Cons(2) by (metis length_0_conv list.collapse list.discI)
  then show ?case
  proof(cases "hd vl = x")
    case True
    then show ?thesis unfolding getExps.simps using Cons(3)
      by (metis "2" list.set_intros(1))
  next
    case False
    then show ?thesis unfolding getExps.simps using Cons exp2ODE.simps(3)[of "hd vl" " tl vl"
          "outupd2exp f il" "getExps fl il" x]
      by (metis "2" ODE2vec_valeq length_tl list.sel(3) list.set_intros(2))
  qed
qed
  done

lemma block2ODE_eqFun : "length vl = length fl  \<Longrightarrow> 
(\<forall>i j. i < j \<and> j < (length vl) \<and> j \<ge> 0 \<longrightarrow> (nth vl i) \<noteq> (nth vl j)) \<Longrightarrow>
 h1 (vl ! i) t = h2 (vl ! i) t \<Longrightarrow> i \<ge> 0 \<and> i < length vl \<Longrightarrow> \<forall> x \<in> set il. h1 x t = h2 x t \<Longrightarrow> 
(block2ODE (Block il vl ol st fl) t ((realstate2realvec (timedVar2timedState h1)) t)
) $ (vl ! i) = (fl ! i) (map (\<lambda> a. h2 a t) il)"
  unfolding block2ODE.simps
proof(induction fl arbitrary: vl i)
  case Nil
  then show ?case by simp
next
  case (Cons f fl)
  note Cons1 = Cons
  then show ?case unfolding getExps.simps
  proof(induction vl)
    case Nil
    then show ?case by simp
  next
    case (Cons v vl)
    then show ?case
    proof(cases "i = 0")
      case True
      have 1: "ODE2vec (exp2ODE (v # vl) (outupd2exp f il # getExps fl il))
     (realstate2realvec (timedVar2timedState h1) t) $ v = (exp2ODE (v # vl) 
  (outupd2exp f il # getExps fl il)) v ((timedVar2timedState h1) t)"
      proof -            
        have tmp1: "(vec2state (realstate2realvec (timedVar2timedState h1) t)) = (timedVar2timedState h1) t"
          unfolding realstate2realvec.simps by auto
        show ?thesis using ODE2vec_valeq tmp1 by presburger
      qed
      show ?thesis using True 1 apply simp using outupd2exp_valeq Cons(7) by auto
    next
      case False
      have 1: "state2vec (\<lambda>x. exp2ODE vl (getExps fl il) x (timedVar2timedState h1 t)) $ vl ! (i - Suc 0)
          = state2vec (\<lambda>x. (if v = x then outupd2exp f il else exp2ODE vl (getExps fl il) x)
           (timedVar2timedState h1 t)) $ (v # vl) ! i"
      proof -
        have tmp1: "vl ! (i - Suc 0) = (v # vl) ! i"
          using False by simp
        have tmp2: "(v # vl) ! i \<in> set vl"
          using False Cons.prems(5) by auto
        have tmp3: "v \<notin> set vl"
          using Cons(4) by (metis bot_nat_0.extremum in_set_conv_nth length_Cons not_less_eq 
              nth_Cons_0 nth_Cons_Suc zero_less_Suc)
        have tmp4: "\<forall>i j. i < j \<and> j < length vl \<and> 0 \<le> j \<longrightarrow> vl ! i \<noteq> vl ! j"
          using Cons(4) by (metis bot_nat_0.extremum length_Cons not_less_eq nth_Cons_Suc)
        show ?thesis using exp2ODE_ith[of "(v # vl) ! i" vl v "(getExps fl il)" "(timedVar2timedState h1 t)"
            "outupd2exp f il"] unfolding exp2ODE.simps using tmp1 tmp2 tmp3 tmp4 by auto
      qed
      have 2: "state2vec (\<lambda>x. exp2ODE vl (getExps fl il) x (timedVar2timedState h1 t)) $ vl ! (i - Suc 0) =
     (fl ! (i - Suc 0)) (map (\<lambda>a. h2 a t) il)"
      proof -
        have tmp1: "length vl = length fl"
          using Cons(3) by simp
        have tmp2: "\<forall>i j. i < j \<and> j < length vl \<and> 0 \<le> j \<longrightarrow> vl ! i \<noteq> vl ! j"
          using Cons(4) by (metis Suc_less_eq bot_nat_0.extremum length_Cons nth_Cons_Suc)
        have tmp3: "h1 (vl ! (i - 1)) t = h2 (vl ! (i - 1)) t"
          using Cons(5) False by simp
        have tmp4: "0 \<le> i - 1 \<and> i - 1 < length vl"
          using Cons(6) False by simp
        have tmp5: "\<forall>x\<in>set il. h1 x t = h2 x t"
          using Cons(7) by simp
        show ?thesis using Cons(2)[of vl "(i-1)"] tmp1 tmp2 tmp3 tmp4 tmp5 by simp
      qed
      show ?thesis using 1 2 False by simp
    qed
  qed
qed

\<comment> \<open>End section\<close>

end
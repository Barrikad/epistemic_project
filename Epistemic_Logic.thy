(*
  File:      Epistemic_Logic.thy
  Author:    Asta Halkjær From
  Modified by: Jakub Eugeniusz Janaszkiewicz & Simon Tobias Lund

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).
  The extensions of system K (T, KB, K4, S4, S5) and their completeness proofs
  are based on the textbook "Modal Logic" by Blackburn, de Rijke and Venema
  (Cambridge University Press 2001).
*)

theory Epistemic_Logic imports "HOL-Library.Countable" begin

section \<open>Auxiliary\<close>

lemma list_of_lists_if_finite_set_of_sets: \<open>finite W \<Longrightarrow> \<forall> V \<in> W. finite V \<Longrightarrow> \<exists> xs. set (map set xs) = W\<close>
  by (induct W rule: finite.induct) (simp, metis finite_list insertCI list.simps(15) list.simps(9))

section \<open>Syntax\<close>

type_synonym id = string

datatype 'i fm
  = FF (\<open>\<^bold>\<bottom>\<close>)
  | Pro id
  | Dis \<open>'i fm\<close> \<open>'i fm\<close> (infixr \<open>\<^bold>\<or>\<close> 60)
  | Con \<open>'i fm\<close> \<open>'i fm\<close> (infixr \<open>\<^bold>\<and>\<close> 65)
  | Imp \<open>'i fm\<close> \<open>'i fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | K 'i \<open>'i fm\<close>
  | Ev \<open>'i list\<close> \<open>'i fm\<close>
  | Co \<open>'i list\<close> \<open>'i fm\<close>

abbreviation TT (\<open>\<^bold>\<top>\<close>) where
  \<open>TT \<equiv> \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where
  \<open>Neg p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation \<open>L i p \<equiv> \<^bold>\<not> K i (\<^bold>\<not> p)\<close>

section \<open>Semantics\<close>

record ('i, 'w) frame =
  \<W> :: \<open>'w set\<close>
  \<K> :: \<open>'i \<Rightarrow> 'w \<Rightarrow> 'w set\<close>

record ('i, 'w) kripke =
  \<open>('i, 'w) frame\<close> +
  \<pi> :: \<open>'w \<Rightarrow> id \<Rightarrow> bool\<close>

primrec f_size where
  \<open>f_size \<^bold>\<bottom> = 1\<close> |
  \<open>f_size (Pro x) = 1\<close> |
  \<open>f_size (p \<^bold>\<or> q) = f_size p + f_size q + 1\<close> |
  \<open>f_size (p \<^bold>\<and> q) = f_size p + f_size q + 1\<close> |
  \<open>f_size (p \<^bold>\<longrightarrow> q) = f_size p + f_size q + 1\<close> |
  \<open>f_size (K i p) = f_size p + 1\<close> |
  \<open>f_size (Ev g p) = f_size p + 2\<close> |
  \<open>f_size (Co g p) = f_size p + 1\<close>

primrec common_count where 
  \<open>common_count \<^bold>\<bottom> = 0\<close> |
  \<open>common_count (Pro x) = 0\<close> |
  \<open>common_count (p \<^bold>\<or> q) = common_count p + common_count q\<close> |
  \<open>common_count (p \<^bold>\<and> q) = common_count p + common_count q\<close> |
  \<open>common_count (p \<^bold>\<longrightarrow> q) = common_count p + common_count q\<close> |
  \<open>common_count (K i p) = common_count p\<close> |
  \<open>common_count (Ev g p) = common_count p\<close> |
  \<open>common_count (Co g p) = common_count p + 1\<close>

primrec Ev_n where
  \<open>Ev_n g p 0 = p\<close> |
  \<open>Ev_n g p (Suc n) = Ev g (Ev_n g p n)\<close>

lemma common_count_EV_n: \<open>common_count (Ev_n g p n) < Suc (common_count p)\<close>
  by (induct n) auto

function semantics :: \<open>('i, 'w) kripke \<Rightarrow> 'w \<Rightarrow> 'i fm \<Rightarrow> bool\<close> (\<open>_, _ \<Turnstile> _\<close> [50, 50, 50] 50) where
  \<open>M, w \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>M, w \<Turnstile> Pro x \<longleftrightarrow> \<pi> M w x\<close>
| \<open>M, w \<Turnstile> p \<^bold>\<or> q \<longleftrightarrow> M, w \<Turnstile> p \<or> M, w \<Turnstile> q\<close>
| \<open>M, w \<Turnstile> p \<^bold>\<and> q \<longleftrightarrow> M, w \<Turnstile> p \<and> M, w \<Turnstile> q\<close>
| \<open>M, w \<Turnstile> p \<^bold>\<longrightarrow> q \<longleftrightarrow> M, w \<Turnstile> p \<longrightarrow> M, w \<Turnstile> q\<close>
| \<open>M, w \<Turnstile> K i p \<longleftrightarrow> (\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p)\<close>
| \<open>M, w \<Turnstile> Ev g p \<longleftrightarrow> (\<forall> i \<in> set g. M, w \<Turnstile> K i p)\<close>
| \<open>M, w \<Turnstile> Co g p \<longleftrightarrow> (\<forall> n \<ge> 1. M, w \<Turnstile> Ev_n g p n)\<close>
  by pat_completeness auto
termination 
proof (relation \<open>measures [\<lambda> (_,_,p). common_count p, \<lambda> (_,_,p).f_size p]\<close>) 
  show \<open>\<And>M w is p x. ((M, w, Ev_n is p x), M, w, Co is p) \<in> measures [\<lambda>(_, _, p). common_count p, \<lambda>(_, _, p). f_size p]\<close>
    using common_count_EV_n by auto
qed auto

abbreviation validStar :: \<open>(('i, 'w) kripke \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  (\<open>_; _ \<TTurnstile>\<star> _\<close> [50, 50, 50] 50) where
  \<open>P; G \<TTurnstile>\<star> p \<equiv> \<forall>M. P M \<longrightarrow>
    (\<forall>w \<in> \<W> M. (\<forall>q \<in> G. M, w \<Turnstile> q) \<longrightarrow> M, w \<Turnstile> p)\<close>

section \<open>S5 Axioms\<close>

definition reflexive :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>i. \<forall>w \<in> \<W> M. w \<in> \<K> M i w\<close>
 
definition symmetric :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>i. \<forall>v \<in> \<W> M. \<forall>w \<in> \<W> M. v \<in> \<K> M i w \<longleftrightarrow> w \<in> \<K> M i v\<close>

definition transitive :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>i. \<forall>u \<in> \<W> M. \<forall>v \<in> \<W> M. \<forall>w \<in> \<W> M.
    w \<in> \<K> M i v \<and> u \<in> \<K> M i w \<longrightarrow> u \<in> \<K> M i v\<close>

abbreviation refltrans :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>refltrans M \<equiv> reflexive M \<and> transitive M\<close>

abbreviation equivalence :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>equivalence M \<equiv> reflexive M \<and> symmetric M \<and> transitive M\<close>

definition Euclidean :: \<open>('i, 'w, 'c) frame_scheme \<Rightarrow> bool\<close> where
  \<open>Euclidean M \<equiv> \<forall>i. \<forall>u \<in> \<W> M. \<forall>v \<in> \<W> M. \<forall>w \<in> \<W> M.
    v \<in> \<K> M i u \<longrightarrow> w \<in> \<K> M i u \<longrightarrow> w \<in> \<K> M i v\<close>

lemma Imp_intro [intro]: \<open>(M, w \<Turnstile> p \<Longrightarrow> M, w \<Turnstile> q) \<Longrightarrow> M, w \<Turnstile> p \<^bold>\<longrightarrow> q\<close>
  by simp

theorem distribution: \<open>M, w \<Turnstile> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q\<close>
proof
  assume \<open>M, w \<Turnstile> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q)\<close>
  then have \<open>M, w \<Turnstile> K i p\<close> \<open>M, w \<Turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close> \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p \<^bold>\<longrightarrow> q\<close>
    by simp_all
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> q\<close>
    by simp
  then show \<open>M, w \<Turnstile> K i q\<close>
    by simp
qed

theorem generalization:
  fixes M :: \<open>('i, 'w) kripke\<close>
  assumes \<open>\<forall>(M :: ('i, 'w) kripke). \<forall>w \<in> \<W> M. M, w \<Turnstile> p\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> K i p\<close>
proof -
  have \<open>\<forall>w' \<in> \<W> M \<inter> \<K> M i w. M, w' \<Turnstile> p\<close>
    using assms by blast
  then show \<open>M, w \<Turnstile> K i p\<close>
    by simp
qed

theorem truth:
  assumes \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> K i p \<^bold>\<longrightarrow> p\<close>
proof
  assume \<open>M, w \<Turnstile> K i p\<close>
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close>
    by simp
  moreover have \<open>w \<in> \<K> M i w\<close>
    using \<open>reflexive M\<close> \<open>w \<in> \<W> M\<close> unfolding reflexive_def by blast
  ultimately show \<open>M, w \<Turnstile> p\<close>
    using \<open>w \<in> \<W> M\<close> by simp
qed

theorem pos_introspection:
  assumes \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> K i p \<^bold>\<longrightarrow> K i (K i p)\<close>
proof
  assume \<open>M, w \<Turnstile> K i p\<close>
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. \<forall>u \<in> \<W> M \<inter> \<K> M i v. M, u \<Turnstile> p\<close>
    using \<open>transitive M\<close> \<open>w \<in> \<W> M\<close> unfolding transitive_def by blast
  then have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> K i p\<close>
    by simp
  then show \<open>M, w \<Turnstile> K i (K i p)\<close>
    by simp
qed

theorem neg_introspection:
  assumes \<open>symmetric M\<close> \<open>transitive M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>M, w \<Turnstile> \<^bold>\<not> K i p \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p)\<close>
proof
  assume \<open>M, w \<Turnstile> \<^bold>\<not> (K i p)\<close>
  then obtain u where \<open>u \<in> \<K> M i w\<close> \<open>\<not> (M, u \<Turnstile> p)\<close> \<open>u \<in> \<W> M\<close>
    by auto
  moreover have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. u \<in> \<W> M \<inter> \<K> M i v\<close>
    using \<open>u \<in> \<K> M i w\<close> \<open>symmetric M\<close> \<open>transitive M\<close> \<open>u \<in> \<W> M\<close> \<open>w \<in> \<W> M\<close>
    unfolding symmetric_def transitive_def by blast
  ultimately have \<open>\<forall>v \<in> \<W> M \<inter> \<K> M i w. M, v \<Turnstile> \<^bold>\<not> K i p\<close>
    by auto
  then show \<open>M, w \<Turnstile> K i (\<^bold>\<not> K i p)\<close>
    by simp
qed

section \<open>Normal Modal Logic\<close>

primrec eval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (Pro x) = g x\<close>
| \<open>eval g h (p \<^bold>\<or> q) = (eval g h p \<or> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<and> q) = (eval g h p \<and> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<longrightarrow> q) = (eval g h p \<longrightarrow> eval g h q)\<close>
| \<open>eval _ h (K i p) = h (K i p)\<close>
| \<open>eval _ h (Ev g p) = h (Ev g p)\<close>
| \<open>eval _ h (Co g p) = h (Co g p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

abbreviation \<open>unfold_Ev g p \<equiv> foldr (\<lambda> i. (\<^bold>\<and>) (K i p)) g \<^bold>\<top>\<close>

inductive AK :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _\<close> [50, 50] 50)
  for A :: \<open>'i fm \<Rightarrow> bool\<close> where
    A1: \<open>tautology p \<Longrightarrow> A \<turnstile> p\<close>
  | A2: \<open>A \<turnstile> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q\<close>
  | Ax: \<open>A p \<Longrightarrow> A \<turnstile> p\<close>
  | R1: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> q\<close>
  | R2: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> K i p\<close>
(*group operator axioms*)
  | C1a: \<open>A \<turnstile> Ev g p \<^bold>\<longrightarrow> unfold_Ev g p\<close>
  | C1b: \<open>A \<turnstile> unfold_Ev g p \<^bold>\<longrightarrow> Ev g p\<close>
  | C2: \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g p)\<close>
  | RC1: \<open>A \<turnstile> p \<^bold>\<longrightarrow> Ev g (q \<^bold>\<and> p) \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> Co g q\<close>

primrec imply :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

primrec disjunct (\<open>\<^bold>\<Or> _\<close> [59] 60) where
  \<open>\<^bold>\<Or>[] = \<^bold>\<bottom>\<close> |
  \<open>\<^bold>\<Or>x # xs = x \<^bold>\<or> \<^bold>\<Or>xs\<close>

primrec conjunct (\<open>\<^bold>\<And> _\<close> [64] 65) where
  \<open>\<^bold>\<And>[] = \<^bold>\<top>\<close> |
  \<open>\<^bold>\<And>x # xs = x \<^bold>\<and> \<^bold>\<And>xs\<close>

fun comp where
  \<open>comp (\<^bold>\<not>p) = p\<close> |
  \<open>comp p = \<^bold>\<not>p\<close>

abbreviation AK_assms (\<open>_; _ \<turnstile> _\<close> [50, 50, 50] 50) where
  \<open>A; G \<turnstile> p \<equiv> \<exists>qs. set qs \<subseteq> G \<and> (A \<turnstile> qs \<^bold>\<leadsto> p)\<close>

section \<open>Soundness\<close>

lemma eval_semantics:
  \<open>eval (pi w) (\<lambda>q. \<lparr>\<W> = W, \<K> = r, \<pi> = pi\<rparr>, w \<Turnstile> q) p = (\<lparr>\<W> = W, \<K> = r, \<pi> = pi\<rparr>, w \<Turnstile> p)\<close>
  by (induct p) simp_all

lemma tautology:
  assumes \<open>tautology p\<close>
  shows \<open>M, w \<Turnstile> p\<close>
proof -
  from assms have \<open>eval (g w) (\<lambda>q. \<lparr>\<W> = W, \<K> = r, \<pi> = g\<rparr>, w \<Turnstile> q) p\<close> for W g r
    by simp
  then have \<open>\<lparr>\<W> = W, \<K> = r, \<pi> = g\<rparr>, w \<Turnstile> p\<close> for W g r
    using eval_semantics by fast
  then show \<open>M, w \<Turnstile> p\<close>
    by (metis kripke.cases)
qed

lemma Ev_n_conE1: \<open>M, w \<Turnstile> Ev_n g (p \<^bold>\<and> q) n \<Longrightarrow> M, w \<Turnstile> Ev_n g p n\<close>
  by (induct n arbitrary: w) auto

theorem soundness:
  assumes \<open>\<And>M w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>A \<turnstile> p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
proof (induct p arbitrary: w rule: AK.induct)
  case (C1a g p)
  have \<open>M, w \<Turnstile> unfold_Ev g p\<close> if 1: \<open>M, w \<Turnstile> Ev g p\<close>
  proof -
    from 1 have \<open>\<forall>i \<in> set g. M, w \<Turnstile> K i p\<close> by auto 
    thus ?thesis
    proof (induct g)
      case (Cons a as)
      have \<open>M, w \<Turnstile> K a p\<close>
        by (meson Cons.prems list.set_intros(1))
      moreover have \<open>M, w \<Turnstile> foldr (\<lambda> i. (\<^bold>\<and>) (K i p)) as \<^bold>\<top>\<close>
        using Cons.hyps Cons.prems by auto
      ultimately show ?case by auto 
    qed simp
  qed
  thus ?case by simp
next
  case (C1b g p)
  have \<open>(M, w \<Turnstile> unfold_Ev g p) \<Longrightarrow> (M, w \<Turnstile> Ev g p)\<close>
  proof (induct g)
    case (Cons a as)
    have \<open>M, w \<Turnstile> K a p\<close>
      using Cons.prems by fastforce 
    thus ?case
      using Cons.hyps Cons.prems by auto 
  qed simp
  thus ?case by simp
next
  case (C2 g p)
  then show ?case
    by fastforce
next
  case (RC1 p g q)
  then have fix_point: \<open>\<forall> v. v \<in> \<W> M \<longrightarrow> M, v \<Turnstile> p \<longrightarrow> M, v \<Turnstile> Ev g (q \<^bold>\<and> p)\<close> 
    by (metis semantics.simps(5))
  have \<open>n \<ge> 1 \<Longrightarrow> w \<in> \<W> M \<Longrightarrow>  M, w \<Turnstile> p \<Longrightarrow> M, w \<Turnstile> Ev_n g (q \<^bold>\<and> p) n\<close> for n
  proof (induct n arbitrary: w)
    case (Suc n)
    consider (n_0) \<open>n = 0\<close> | (n_Suc) \<open>1 \<le> n\<close> 
      by linarith
    then show ?case 
      using Suc fix_point by cases auto
  qed simp
  then show ?case 
    using RC1(4) Ev_n_conE1 by fastforce
qed (auto simp: assms tautology) 


section \<open>Derived rules\<close>

lemma imp_chain: \<open>A \<turnstile> a \<^bold>\<longrightarrow> b \<Longrightarrow> A \<turnstile> b \<^bold>\<longrightarrow> c \<Longrightarrow> A \<turnstile> a \<^bold>\<longrightarrow> c\<close>
proof -
  assume \<open>A \<turnstile> a \<^bold>\<longrightarrow> b\<close>
  moreover assume \<open>A \<turnstile> b \<^bold>\<longrightarrow> c\<close>
  moreover have \<open>A \<turnstile> (a \<^bold>\<longrightarrow> b) \<^bold>\<longrightarrow> (b \<^bold>\<longrightarrow> c) \<^bold>\<longrightarrow> (a \<^bold>\<longrightarrow> c)\<close>
    using A1 by force
  ultimately show \<open>A \<turnstile> a \<^bold>\<longrightarrow> c\<close>
    using R1 by metis
qed

lemma con_imp: \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> a \<^bold>\<longrightarrow> b \<Longrightarrow> A \<turnstile> p \<^bold>\<and> a \<^bold>\<longrightarrow> q \<^bold>\<and> b\<close> 
proof-
  assume a1: \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  moreover assume a2: \<open>A \<turnstile> a \<^bold>\<longrightarrow> b\<close>
  moreover have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (a \<^bold>\<longrightarrow> b) \<^bold>\<longrightarrow> p \<^bold>\<and> a \<^bold>\<longrightarrow> q \<^bold>\<and> b\<close>
    using A1 by force 
  ultimately show ?thesis
    using R1 by blast
qed
  
lemma Ev_n_eval: \<open>i \<in> set g \<Longrightarrow> eval f h (unfold_Ev g p) \<Longrightarrow> eval f h (K i p)\<close>
  by (induct g) auto

lemma EvExt: \<open>set g \<subseteq> set g' \<Longrightarrow> A \<turnstile> Ev g' p \<^bold>\<longrightarrow> Ev g p\<close>
proof-
  assume a:\<open>set g \<subseteq> set g'\<close>
  have \<open>set g \<subseteq> set g' \<Longrightarrow> tautology (unfold_Ev g' p \<^bold>\<longrightarrow> unfold_Ev g p)\<close> 
  proof (rule allI, rule allI)
    fix f h
    assume \<open>set g \<subseteq> set g'\<close>
    moreover have \<open>set g \<subseteq> set g' \<Longrightarrow> eval f h (unfold_Ev g' p) \<Longrightarrow> eval f h (unfold_Ev g p)\<close>
    proof (induct g)
      case (Cons i g)
      then show ?case 
        using Cons Ev_n_eval by auto
    qed simp
    ultimately show \<open>eval f h (unfold_Ev g' p \<^bold>\<longrightarrow> unfold_Ev g p)\<close>
      by simp
  qed
  then show ?thesis
    by (metis a A1 C1a C1b imp_chain)
qed

lemma CoExt: \<open>A \<turnstile> Co g' p \<^bold>\<longrightarrow> Co g p\<close> if a: \<open>set g \<subseteq> set g'\<close>
proof-
  have \<open>A \<turnstile> Co g' p \<^bold>\<longrightarrow> Ev g' (p \<^bold>\<and> Co g' p)\<close> ..
  moreover have \<open>A \<turnstile> Ev g' (p \<^bold>\<and> Co g' p) \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g' p)\<close>
    using a EvExt by fast
  ultimately have \<open>A \<turnstile> Co g' p \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g' p)\<close>
    using imp_chain by auto
  then show ?thesis ..
qed

lemma empty_fold: \<open>foldr (\<lambda>i. (\<^bold>\<and>) (K i p)) [] \<^bold>\<top> = \<^bold>\<top>\<close> 
  by simp

lemma Ev_empty_group: \<open>A \<turnstile> Ev [] p\<close> 
proof-
  have \<open>A \<turnstile> \<^bold>\<top> \<^bold>\<longrightarrow> Ev [] p\<close>
    using C1b empty_fold by metis
  then show ?thesis
    using A1 R1 C1b eval.simps(5) by blast
qed

lemma con_rule: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> q \<Longrightarrow> A \<turnstile> p \<^bold>\<and> q\<close>
proof-
  assume \<open>A \<turnstile> p\<close>
  moreover assume \<open>A \<turnstile> q\<close>
  moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<and> q\<close>
    using A1 by force
  ultimately show ?thesis
    using R1 by blast
qed

lemma Ev_R2: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> Ev g p\<close>
proof (induct g)
  case Nil
  then show ?case 
    using Ev_empty_group by fast
next
  case (Cons i g)
  then have \<open>A \<turnstile> K i p\<close> 
    using R2 by simp
  moreover have \<open>A \<turnstile> unfold_Ev g p\<close>
    using Cons C1a R1 by blast
  ultimately have \<open>A \<turnstile> unfold_Ev (i # g) p\<close>
    using con_rule by auto
  then show ?case 
    using C1b R1 by blast
qed

lemma conE1: \<open>A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> p\<close>
  using A1 R1 by force

lemma conE2: \<open>A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> q\<close>
  using A1 R1 by force

lemma con_imp2: \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> r \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<and> r\<close>
  by (metis A1 con_imp eval.simps(4) eval.simps(5) imp_chain)

lemma Ev_A2: \<open>A \<turnstile> Ev g p \<^bold>\<and> Ev g (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> Ev g q\<close>
proof (induct g)
  case Nil
  then show ?case 
    using Ev_empty_group A1 R1 by force
next
  case (Cons i g)
  have 1: \<open>A \<turnstile> Ev (i # g) p \<^bold>\<and> Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> unfold_Ev (i # g) p \<^bold>\<and> unfold_Ev (i # g) (p \<^bold>\<longrightarrow> q)\<close>
    using C1a con_imp by blast
  moreover have \<open>A \<turnstile> unfold_Ev (i # g) p \<^bold>\<and> unfold_Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> unfold_Ev g p \<^bold>\<and> unfold_Ev g (p \<^bold>\<longrightarrow> q)\<close>
    using conE2 con_imp by fastforce
  moreover have \<open>A \<turnstile> unfold_Ev g p \<^bold>\<and> unfold_Ev g (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> Ev g p \<^bold>\<and> Ev g (p \<^bold>\<longrightarrow> q)\<close>
    using C1b con_imp by blast
  moreover have \<open>A \<turnstile> Ev g q \<^bold>\<longrightarrow> unfold_Ev g q\<close>
    using C1a .
  ultimately have 2: \<open>A \<turnstile> Ev (i # g) p \<^bold>\<and> Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> unfold_Ev g q\<close>
    using Cons imp_chain by blast
  have \<open>A \<turnstile> unfold_Ev (i # g) p \<^bold>\<and> unfold_Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q)\<close>
    using conE1 con_imp by fastforce
  moreover have \<open>A \<turnstile> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q\<close> 
    using A2 .
  ultimately have \<open>A \<turnstile> Ev (i # g) p \<^bold>\<and> Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q\<close>
    using 1 A2 imp_chain by blast
  from this 2 have \<open>A \<turnstile> Ev (i # g) p \<^bold>\<and> Ev (i # g) (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> unfold_Ev (i # g) q\<close> 
    using con_imp2 by auto
  then show ?case 
    using imp_chain C1b by blast
qed

lemma con_imp_antecedents: \<open>(A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> r) = (A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r)\<close>
proof (rule iffI)
  assume \<open>A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> r\<close>
  moreover have \<open>A \<turnstile> (p \<^bold>\<and> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r\<close>
    using A1 by force
  ultimately show \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r\<close>
    using R1 by auto
next
  assume \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r\<close>
  moreover have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<and> q \<^bold>\<longrightarrow> r\<close>
    using A1 by force
  ultimately show \<open>A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> r\<close>
    using R1 by auto
qed

lemma swap_antecedents: \<open>(A \<turnstile> p \<^bold>\<and> q \<^bold>\<longrightarrow> r) = (A \<turnstile> q \<^bold>\<and> p \<^bold>\<longrightarrow> r)\<close>
  using conE1 conE2 con_imp2 imp_chain by blast

lemma Ev_conE1: \<open>A \<turnstile> Ev g (p \<^bold>\<and> q) \<^bold>\<longrightarrow> Ev g p\<close> 
proof-
  have \<open>A \<turnstile> Ev g (p \<^bold>\<and> q \<^bold>\<longrightarrow> p)\<close>
    using conE1 Ev_R2 by fast
  moreover have \<open>A \<turnstile> Ev g (p \<^bold>\<and> q) \<^bold>\<and> Ev g (p \<^bold>\<and> q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> Ev g p\<close>
    using Ev_A2 by auto
  ultimately show ?thesis
    using con_imp_antecedents swap_antecedents R1 by fast
qed

lemma Ev_conE2: \<open>A \<turnstile> Ev g (p \<^bold>\<and> q) \<^bold>\<longrightarrow> Ev g q\<close> 
proof-
  have \<open>A \<turnstile> Ev g (p \<^bold>\<and> q \<^bold>\<longrightarrow> q)\<close>
    using conE2 Ev_R2 by fast
  moreover have \<open>A \<turnstile> Ev g (p \<^bold>\<and> q) \<^bold>\<and> Ev g (p \<^bold>\<and> q \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> Ev g q\<close>
    using Ev_A2 by auto
  ultimately show ?thesis
    using con_imp_antecedents swap_antecedents R1 by fast
qed

lemma Co_imp_Ev_n: \<open>n \<ge> 1 \<Longrightarrow> A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev_n g p n\<close> 
proof (induct n rule: less_induct)
  case (less n')
  then consider (n'_eq_1)\<open>n' = 1\<close> | (n'_geq_2)\<open>n' > 1\<close>
    by linarith
  then show ?case
  proof cases
    case n'_eq_1
    have \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g p)\<close>
      using C2 by auto
    moreover have \<open>A \<turnstile> Ev g (p \<^bold>\<and> Co g p) \<^bold>\<longrightarrow> Ev g p\<close>
      using Ev_conE1 by auto
    ultimately show ?thesis
      using n'_eq_1 imp_chain by auto
  next
    case n'_geq_2
    then have \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev_n g p (n' - 1)\<close> 
      using less by simp
    then have 1: \<open>A \<turnstile> Ev g (Co g p \<^bold>\<longrightarrow> Ev_n g p (n' - 1))\<close>
      by (simp add: Ev_R2)
    have \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g p)\<close> ..
    then have 2:\<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g (Co g p)\<close> 
      using imp_chain Ev_conE2 by blast
    have \<open>A \<turnstile> 
      Ev g (Co g p) \<^bold>\<and> Ev g (Co g p \<^bold>\<longrightarrow> Ev_n g p (n' - 1)) \<^bold>\<longrightarrow> Ev g (Ev_n g p (n' - 1))\<close>
      using Ev_A2 by auto
    then have \<open>A \<turnstile> Ev g (Co g p) \<^bold>\<longrightarrow> Ev g (Ev_n g p (n' - 1))\<close>
      using 1 R1 swap_antecedents con_imp_antecedents by blast
    moreover have \<open>Ev g (Ev_n g p (n' - 1)) = Ev_n g p n'\<close> 
      by (metis Ev_n.simps(2) Suc_eq_plus1 add.commute le_add_diff_inverse less.prems)
    ultimately show ?thesis 
      using 2 imp_chain by auto
  qed
qed

lemma K_A2': \<open>A \<turnstile> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q\<close>
proof -
  have \<open>A \<turnstile> K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q\<close>
    using A2 by fast
  moreover have \<open>A \<turnstile> (P \<^bold>\<and> Q \<^bold>\<longrightarrow> R) \<^bold>\<longrightarrow> (Q \<^bold>\<longrightarrow> P \<^bold>\<longrightarrow> R)\<close> for P Q R
    by (simp add: A1)
  ultimately show ?thesis
    using R1 by fast
qed

lemma K_map:
  assumes \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  shows \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> K i q\<close>
proof -
  note \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  then have \<open>A \<turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    using R2 by fast
  moreover have \<open>A \<turnstile> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i p \<^bold>\<longrightarrow> K i q\<close>
    using K_A2' by fast
  ultimately show ?thesis
    using R1 by fast
qed

lemma K_LK: \<open>A \<turnstile> (L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<not> K i p)\<close>
proof -
  have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  moreover have \<open>A \<turnstile> ((P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> (\<^bold>\<not> Q \<^bold>\<longrightarrow> \<^bold>\<not> P))\<close> for P Q
    using A1 by force
  ultimately show ?thesis
    using K_map R1 by fast
qed

lemma K_imply_head: \<open>A \<turnstile> (p # ps \<^bold>\<leadsto> p)\<close>
proof -
  have \<open>tautology (p # ps \<^bold>\<leadsto> p)\<close>
    by (induct ps) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>A \<turnstile> ps \<^bold>\<leadsto> q\<close>
  shows \<open>A \<turnstile> p # ps \<^bold>\<leadsto> q\<close>
proof -
  have \<open>A \<turnstile> (ps \<^bold>\<leadsto> q \<^bold>\<longrightarrow> p # ps \<^bold>\<leadsto> q)\<close>
    by (simp add: A1)
  with R1 assms show ?thesis .
qed

lemma K_right_mp:
  assumes \<open>A \<turnstile> ps \<^bold>\<leadsto> p\<close> \<open>A \<turnstile> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>A \<turnstile> ps \<^bold>\<leadsto> q\<close>
proof -
  have \<open>tautology (ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>
    by (induct ps) simp_all
  with A1 have \<open>A \<turnstile> ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close> .
  then show ?thesis
    using assms R1 by blast
qed

lemma tautology_imply_superset:
  assumes \<open>set ps \<subseteq> set qs\<close>
  shows \<open>tautology (ps \<^bold>\<leadsto> r \<^bold>\<longrightarrow> qs \<^bold>\<leadsto> r)\<close>
proof (rule ccontr)
  assume \<open>\<not> tautology (ps \<^bold>\<leadsto> r \<^bold>\<longrightarrow> qs \<^bold>\<leadsto> r)\<close>
  then obtain g h where \<open>\<not> eval g h (ps \<^bold>\<leadsto> r \<^bold>\<longrightarrow> qs \<^bold>\<leadsto> r)\<close>
    by blast
  then have \<open>eval g h (ps \<^bold>\<leadsto> r)\<close> \<open>\<not> eval g h (qs \<^bold>\<leadsto> r)\<close>
    by simp_all
  then consider (np) \<open>\<exists>p \<in> set ps. \<not> eval g h p\<close> | (r) \<open>\<forall>p \<in> set ps. eval g h p\<close> \<open>eval g h r\<close>
    by (induct ps) auto
  then show False
  proof cases
    case np
    then have \<open>\<exists>p \<in> set qs. \<not> eval g h p\<close>
      using \<open>set ps \<subseteq> set qs\<close> by blast
    then have \<open>eval g h (qs \<^bold>\<leadsto> r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (qs \<^bold>\<leadsto> r)\<close> by blast
  next
    case r
    then have \<open>eval g h (qs \<^bold>\<leadsto> r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (qs \<^bold>\<leadsto> r)\<close> by blast
  qed
qed

lemma K_imply_weaken:
  assumes \<open>A \<turnstile> ps \<^bold>\<leadsto> q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>A \<turnstile> ps' \<^bold>\<leadsto> q\<close>
proof -
  have \<open>tautology (ps \<^bold>\<leadsto> q \<^bold>\<longrightarrow> ps' \<^bold>\<leadsto> q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close> tautology_imply_superset by blast
  then have \<open>A \<turnstile> ps \<^bold>\<leadsto> q \<^bold>\<longrightarrow> ps' \<^bold>\<leadsto> q\<close>
    using A1 by blast
  then show ?thesis
    using \<open>A \<turnstile> ps \<^bold>\<leadsto> q\<close> R1 by blast
qed

lemma imply_append: \<open>(ps @ ps' \<^bold>\<leadsto> q) = (ps \<^bold>\<leadsto> ps' \<^bold>\<leadsto> q)\<close>
  by (induct ps) simp_all

lemma K_ImpI:
  assumes \<open>A \<turnstile> p # G \<^bold>\<leadsto> q\<close>
  shows \<open>A \<turnstile> G \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>A \<turnstile> G @ [p] \<^bold>\<leadsto> q\<close>
    using assms K_imply_weaken by blast
  then have \<open>A \<turnstile> G \<^bold>\<leadsto> [p] \<^bold>\<leadsto> q\<close>
    using imply_append by metis
  then show ?thesis
    by simp
qed

lemma K_Boole:
  assumes \<open>A \<turnstile> (\<^bold>\<not> p) # G \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
  shows \<open>A \<turnstile> G \<^bold>\<leadsto> p\<close>
proof -
  have \<open>A \<turnstile> G \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p\<close>
    using assms K_ImpI by blast
  moreover have \<open>tautology (G \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> G \<^bold>\<leadsto> p)\<close>
    by (induct G) simp_all
  then have \<open>A \<turnstile> (G \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> G \<^bold>\<leadsto> p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_DisE:
  assumes \<open>A \<turnstile> p # G \<^bold>\<leadsto> r\<close> \<open>A \<turnstile> q # G \<^bold>\<leadsto> r\<close> \<open>A \<turnstile> G \<^bold>\<leadsto> p \<^bold>\<or> q\<close>
  shows \<open>A \<turnstile> G \<^bold>\<leadsto> r\<close>
proof -
  have \<open>tautology (p # G \<^bold>\<leadsto> r \<^bold>\<longrightarrow> q # G \<^bold>\<leadsto> r \<^bold>\<longrightarrow> G \<^bold>\<leadsto> p \<^bold>\<or> q \<^bold>\<longrightarrow> G \<^bold>\<leadsto> r)\<close>
    by (induct G) auto
  then have \<open>A \<turnstile> p # G \<^bold>\<leadsto> r \<^bold>\<longrightarrow> q # G \<^bold>\<leadsto> r \<^bold>\<longrightarrow> G \<^bold>\<leadsto> p \<^bold>\<or> q \<^bold>\<longrightarrow> G \<^bold>\<leadsto> r\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_mp: \<open>A \<turnstile> p # (p \<^bold>\<longrightarrow> q) # G \<^bold>\<leadsto> q\<close>
  by (meson K_imply_head K_imply_weaken K_right_mp set_subset_Cons)

lemma K_swap:
  assumes \<open>A \<turnstile> p # q # G \<^bold>\<leadsto> r\<close>
  shows \<open>A \<turnstile> q # p # G \<^bold>\<leadsto> r\<close>
  using assms K_ImpI by (metis imply.simps(1-2))

lemma K_DisL:
  assumes \<open>A \<turnstile> p # ps \<^bold>\<leadsto> q\<close> \<open>A \<turnstile> p' # ps \<^bold>\<leadsto> q\<close>
  shows \<open>A \<turnstile> (p \<^bold>\<or> p') # ps \<^bold>\<leadsto> q\<close>
proof -
  have \<open>A \<turnstile> p # (p \<^bold>\<or> p') # ps \<^bold>\<leadsto> q\<close> \<open>A \<turnstile> p' # (p \<^bold>\<or> p') # ps \<^bold>\<leadsto> q\<close>
    using assms K_swap K_imply_Cons by blast+
  moreover have \<open>A \<turnstile> (p \<^bold>\<or> p') # ps \<^bold>\<leadsto> p \<^bold>\<or> p'\<close>
    using K_imply_head by blast
  ultimately show ?thesis
    using K_DisE by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>A \<turnstile> K i (G \<^bold>\<leadsto> q)\<close>
  shows \<open>A \<turnstile> map (K i) G \<^bold>\<leadsto> K i q\<close>
proof -
  have \<open>A \<turnstile> (K i (G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q)\<close>
  proof (induct G)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a G)
    have \<open>A \<turnstile> K i a \<^bold>\<and> K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> K i (G \<^bold>\<leadsto> q)\<close>
      by (simp add: A2)
    moreover have
      \<open>A \<turnstile> ((K i a \<^bold>\<and> K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> K i (G \<^bold>\<leadsto> q)) \<^bold>\<longrightarrow>
        (K i (G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q) \<^bold>\<longrightarrow>
        (K i a \<^bold>\<and> K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q))\<close>
      by (simp add: A1)
    ultimately have \<open>A \<turnstile> K i a \<^bold>\<and> K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q\<close>
      using Cons R1 by blast
    moreover have
      \<open>A \<turnstile> ((K i a \<^bold>\<and> K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q) \<^bold>\<longrightarrow>
        (K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q))\<close>
      by (simp add: A1)
    ultimately have \<open>A \<turnstile> (K i (a # G \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> map (K i) G \<^bold>\<leadsto> K i q)\<close>
      using R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

lemma K_trans: \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (auto intro: A1)

lemma K_L_comp: \<open>A \<turnstile> \<^bold>\<not> L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i p\<close>
proof -
  have \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> K i p\<close> \<open>A \<turnstile> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p\<close>
    by (auto intro: A1)
  then have \<open>A \<turnstile> K i (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> K i p\<close>
    by (auto intro: K_map)
  moreover have \<open>A \<turnstile> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> (\<^bold>\<not> \<^bold>\<not> P \<^bold>\<longrightarrow> Q)\<close> for P Q
    by (auto intro: A1)
  ultimately show \<open>A \<turnstile> \<^bold>\<not> \<^bold>\<not> K i (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> K i p\<close>
    by (auto intro: R1)
qed

lemma con_to_imp_assm: \<open>A \<turnstile> (p \<^bold>\<and> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r)\<close> 
  by (simp add: A1)

lemma imp_to_con_assm: \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<and> q \<^bold>\<longrightarrow> r)\<close> 
  by (simp add: A1)

lemma imply_chain: \<open>A \<turnstile> ps \<^bold>\<leadsto> q \<Longrightarrow> A \<turnstile> q \<^bold>\<longrightarrow> r \<Longrightarrow> A \<turnstile> ps \<^bold>\<leadsto> r\<close>
proof (induct ps)
  case Nil
  then show ?case 
    using R1 by auto
next
  case (Cons a ps)
  then show ?case
    by (metis K_imply_head K_right_mp R1 imply.simps(2))
qed

lemma Ev_add_i: \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> Ev g p \<^bold>\<longrightarrow> Ev (i # g) p\<close> 
proof-
  have \<open>A \<turnstile> Ev g p \<^bold>\<longrightarrow> unfold_Ev g p\<close>
    by (simp add: C1a)
  then have \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> Ev g p \<^bold>\<longrightarrow> unfold_Ev g p\<close>
    by (meson R1 conE1 con_imp_antecedents imp_chain)
  then have 1:\<open>A \<turnstile> [K i p, Ev g p] \<^bold>\<leadsto> unfold_Ev g p\<close>
    by simp
  then have \<open>A \<turnstile> [K i p, Ev g p] \<^bold>\<leadsto> (K i p \<^bold>\<and> unfold_Ev g p)\<close>
    by (metis C1a K_imply_head con_imp con_imp_antecedents imply.simps(1) imply.simps(2))
  then have \<open>A \<turnstile> [K i p, Ev g p] \<^bold>\<leadsto> (unfold_Ev (i # g) p)\<close> 
    by simp
  moreover have \<open>A \<turnstile> unfold_Ev (i # g) p \<^bold>\<longrightarrow> Ev (i # g) p\<close> 
    using C1b by blast
  ultimately have \<open>A \<turnstile> [K i p, Ev g p] \<^bold>\<leadsto> Ev (i # g) p\<close> 
    using imply_chain by blast
  then show ?thesis 
    by simp
qed

lemma elem_implies_disjunct: \<open>p \<in> set ps \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> \<^bold>\<Or>ps\<close>
proof (induct ps)
  case (Cons a ps)
  then show ?case
    by (metis A1 disjunct.simps(2) eval.simps(3) eval.simps(5) imp_chain set_ConsD)
qed simp


lemma conjunct_implies_imply: \<open>A \<turnstile> (\<^bold>\<And> ps \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (ps \<^bold>\<leadsto> q)\<close> 
proof (induct ps)
  case Nil
  then show ?case 
    by (simp add: A1)
next
  case (Cons a ps)
  then show ?case
    using con_to_imp_assm imp_chain 
    by (metis con_imp_antecedents conjunct.simps(2) imply.simps(2))
qed 

lemma imply_implies_conjunct: \<open>A \<turnstile> (ps \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> (\<^bold>\<And>ps \<^bold>\<longrightarrow> q)\<close>
proof (induct ps)
  case Nil
  then show ?case 
    by (simp add: A1)
next
  case (Cons p ps)
  then have \<open>A \<turnstile> (p # ps \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> (\<^bold>\<And> ps \<^bold>\<longrightarrow> q))\<close>
    by (metis (mono_tags, opaque_lifting) K_imply_head con_imp_antecedents imp_chain imply.simps(1) imply.simps(2))
  moreover have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> (\<^bold>\<And> ps \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> (\<^bold>\<And> p # ps \<^bold>\<longrightarrow> q)\<close>
    by (simp add: imp_to_con_assm)
  ultimately show ?case 
    using imp_chain by auto
qed

lemma imply_implies_itself: \<open>A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<And>ps\<close>
proof (induct ps)
  case Nil
  then show ?case 
    by (simp add: A1)
next
  case (Cons a ps)
  then show ?case
    by (metis K_Boole conjunct_implies_imply imply.simps(2))
qed

lemma unfold_Ev_implies_K: \<open>i \<in> set g \<Longrightarrow> A \<turnstile> unfold_Ev g p \<^bold>\<longrightarrow> K i p\<close>
proof (induct g)
  case (Cons a g)
  then show ?case 
  by (smt (verit, del_insts) A1 Ev_n_eval eval.simps(5) foldr_cong)
qed simp

lemma Ev_implies_K: \<open>i \<in> set g \<Longrightarrow> A \<turnstile> Ev g p \<^bold>\<longrightarrow> K i p\<close>
  using unfold_Ev_implies_K by (metis C1a imp_chain)

lemma K_implies_combine: \<open>A \<turnstile> ps \<^bold>\<leadsto> q \<Longrightarrow> A \<turnstile> ps \<^bold>\<leadsto> r \<Longrightarrow> A \<turnstile> ps \<^bold>\<leadsto> (q \<^bold>\<and> r)\<close>
  by (metis K_ImpI K_imply_head K_right_mp con_imp_antecedents imply.simps(2))

lemma comp_imp1: \<open>A \<turnstile> p \<^bold>\<longrightarrow> \<^bold>\<not>(comp p)\<close> 
proof (cases \<open>\<exists> p'. p = \<^bold>\<not> p'\<close>)
  case True
  then obtain p' where \<open>p = \<^bold>\<not>p'\<close> ..
  then have \<open>comp p = p'\<close>
    by simp
  then show ?thesis
    by (simp add: A1 \<open>p = \<^bold>\<not> p'\<close>)
next
  case False
  then have \<open>comp p = \<^bold>\<not>p\<close>
  proof (cases p)
    case (Imp p q)
    then show ?thesis 
      using False by (cases q) auto
  qed auto
  then show ?thesis 
    by (simp add: A1)
qed

lemma comp_imp2: \<open>A \<turnstile> \<^bold>\<not>(comp p) \<^bold>\<longrightarrow> p\<close> 
proof (cases \<open>\<exists> p'. p = \<^bold>\<not> p'\<close>)
  case True
  then obtain p' where \<open>p = \<^bold>\<not>p'\<close> ..
  then have \<open>comp p = p'\<close>
    by simp
  then show ?thesis
    by (metis \<open>p = \<^bold>\<not> p'\<close> comp_imp1)
next
  case False
  then have \<open>comp p = \<^bold>\<not>p\<close>
  proof (cases p)
    case (Imp p q)
    then show ?thesis 
      using False by (cases q) auto
  qed auto
  then show ?thesis 
    by (simp add: A1)
qed

lemma conjunct_implies_elem: \<open>p \<in> set ps \<Longrightarrow> A \<turnstile> \<^bold>\<And> ps \<^bold>\<longrightarrow> p\<close> 
  by (metis K_imply_head R1 imply.simps(2) imply_append imply_implies_conjunct split_list)

lemma conjunction_in_K: \<open>A \<turnstile> p \<^bold>\<longrightarrow> K i q \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> K i r \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> K i (q \<^bold>\<and> r)\<close> 
proof-
  have \<open>A \<turnstile> K i q \<^bold>\<longrightarrow> K i r \<^bold>\<longrightarrow> K i (q \<^bold>\<and> r)\<close> 
    by (metis K_A2' K_imply_head K_map con_imp_antecedents imp_chain imply.simps(1) imply.simps(2))
  then show \<open>A \<turnstile> p \<^bold>\<longrightarrow> K i q \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> K i r \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> K i (q \<^bold>\<and> r)\<close>  
    using con_imp2 con_imp_antecedents imp_chain by blast
qed

lemma dis_to_imp: \<open>A \<turnstile> p \<^bold>\<or> q \<Longrightarrow> A \<turnstile> \<^bold>\<not>q \<^bold>\<longrightarrow> p\<close>
proof-
  assume \<open>A \<turnstile> p \<^bold>\<or> q\<close>
  moreover have \<open>A \<turnstile> (p \<^bold>\<or> q) \<^bold>\<longrightarrow> \<^bold>\<not>q \<^bold>\<longrightarrow> p\<close>
    using A1 by force
  ultimately show ?thesis 
    using R1 by auto
qed

lemma extract_neg_conjunct: \<open>A \<turnstile> (\<^bold>\<And> (map (Neg) ps)) \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<Or> ps)\<close>
proof (induct ps)
  case Nil
  then show ?case 
    by (metis comp.simps(1) comp_imp2 conjunct.simps(1) disjunct.simps(1) list.simps(8))
next
  case (Cons p ps)
  then have \<open>A \<turnstile> \<^bold>\<not>p \<^bold>\<and> \<^bold>\<And> map Neg ps \<^bold>\<longrightarrow> \<^bold>\<not>p \<^bold>\<and> \<^bold>\<not> (\<^bold>\<Or> ps)\<close>
    by (metis comp.simps(1) comp_imp2 con_imp)
  moreover have \<open>A \<turnstile> \<^bold>\<not>p \<^bold>\<and> \<^bold>\<not> (\<^bold>\<Or> ps) \<^bold>\<longrightarrow> \<^bold>\<not> (p \<^bold>\<or> \<^bold>\<Or> ps)\<close>
    by (simp add: A1)
  ultimately show ?case 
    using imp_chain by auto
qed

lemma disjunct_split: \<open>A \<turnstile> \<^bold>\<Or> (ps @ qs) \<^bold>\<longrightarrow> (\<^bold>\<Or> (ps)) \<^bold>\<or> (\<^bold>\<Or> (qs))\<close>
proof (induct ps)
  case Nil
  then show ?case 
    by (simp add: A1)
next
  case (Cons p ps)
  moreover have \<open>A \<turnstile> (\<^bold>\<Or> ps @ qs \<^bold>\<longrightarrow> (\<^bold>\<Or> ps) \<^bold>\<or> \<^bold>\<Or> qs) \<^bold>\<longrightarrow> p \<^bold>\<or> \<^bold>\<Or> ps @ qs \<^bold>\<longrightarrow> p \<^bold>\<or> ((\<^bold>\<Or> ps) \<^bold>\<or> \<^bold>\<Or> qs)\<close>
    using A1 by force
  ultimately have \<open>A \<turnstile> p \<^bold>\<or> \<^bold>\<Or> ps @ qs \<^bold>\<longrightarrow> p \<^bold>\<or> ((\<^bold>\<Or> ps) \<^bold>\<or> \<^bold>\<Or> qs)\<close>
    using R1 by auto
  then show ?case 
    by (smt (z3) A1 append_Cons disjunct.simps(2) eval.simps(3) eval.simps(5) imp_chain)
qed

lemma add_assm_and_concl: \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<And>qs \<Longrightarrow> A \<turnstile> (p # ps) \<^bold>\<leadsto> \<^bold>\<And>(q # qs)\<close>
proof-
  assume 1:\<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  assume 2:\<open>A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<And>qs\<close>
  from 1 have \<open>A \<turnstile> \<^bold>\<And>qs \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q \<^bold>\<and> \<^bold>\<And>qs\<close> 
    by (meson conE1 conE2 con_imp2 con_imp_antecedents imp_chain)
  then have \<open>A \<turnstile> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q \<^bold>\<and> \<^bold>\<And>qs)\<close>
    using 2 imply_chain by auto
  then show ?thesis 
    by (metis K_imply_Cons K_imply_head K_right_mp conjunct.simps(2))
qed

lemma de_morgan_conjunct: \<open>A \<turnstile> \<^bold>\<not>(\<^bold>\<Or>ps) \<^bold>\<longrightarrow> \<^bold>\<And> map Neg ps\<close> 
proof (induct ps)
  case Nil
  then show ?case 
    by (metis conjunct.simps(1) disjunct.simps(1) extract_neg_conjunct list.simps(8))
next
  case (Cons p ps)
  moreover have \<open>A \<turnstile> (\<^bold>\<not> (\<^bold>\<Or> ps) \<^bold>\<longrightarrow> \<^bold>\<And> map Neg ps) \<^bold>\<longrightarrow> (\<^bold>\<not> (p \<^bold>\<or> \<^bold>\<Or> ps) \<^bold>\<longrightarrow> (\<^bold>\<not>p \<^bold>\<and> \<^bold>\<And> map Neg ps))\<close>
    using A1 by force
  ultimately show ?case 
    using R1 by auto
qed 

lemma R1_leads_to: \<open>\<forall> p \<in> set ps. A \<turnstile> p \<Longrightarrow> A \<turnstile> ps \<^bold>\<leadsto> q \<Longrightarrow> A \<turnstile> q\<close> 
  using R1 by (induct ps) auto

lemma leads_to_evalI: \<open>((\<forall> p \<in> set ps. eval g h p) \<Longrightarrow> eval g h w) \<Longrightarrow> eval g h (ps \<^bold>\<leadsto> w)\<close> 
  by (induct ps) auto

lemma disjunct_evalI: \<open>\<exists> p \<in> set ps. eval g h p \<Longrightarrow> eval g h (\<^bold>\<Or>ps)\<close>
  by (induct ps) auto

lemma disjunct_evalE: \<open>eval g h (\<^bold>\<Or>ps) \<Longrightarrow> \<exists> p \<in> set ps. eval g h p\<close>
  by (induct ps) auto

lemma conjunct_evalI: \<open>\<forall> p \<in> set ps. eval g h p \<Longrightarrow> eval g h (\<^bold>\<And>ps)\<close>
  by (induct ps) auto

lemma conjunct_evalE: \<open>eval g h (\<^bold>\<And>ps) \<Longrightarrow> \<forall> p \<in> set ps. eval g h p\<close>
  by (induct ps) auto

lemma combine_disjunct: 
  assumes \<open>\<forall> w'. (\<forall> w \<in> set W. \<exists> p \<in> set w. p \<in> set w') \<longrightarrow> A \<turnstile> \<^bold>\<Or>w'\<close> 
  shows \<open>A \<turnstile> \<^bold>\<Or> (map conjunct W)\<close> 
proof-
  let ?U = \<open>\<Union> (set (map set W))\<close>
  let \<open>?P\<close> = \<open>\<lambda> w'. (\<forall> w \<in> set W. \<exists> p \<in> set w. p \<in> w')\<close>
  have \<open>finite {w'. ?P w' \<and> w' \<subseteq> ?U}\<close> \<open>\<forall> w' \<in> {w'. ?P w' \<and> w' \<subseteq> ?U}. finite w'\<close>
    using finite_subset by fastforce+
  then obtain W' where W'_def: \<open>set (map set W') = {w'. ?P w' \<and> w' \<subseteq> ?U}\<close>
    by (meson list_of_lists_if_finite_set_of_sets)
  have \<open>\<forall> p \<in> set W'. A \<turnstile> \<^bold>\<Or>p\<close>
  proof
    fix p
    assume \<open>p \<in> set W'\<close>
    then have \<open>?P (set p)\<close>
      using W'_def by auto
    then show \<open>A \<turnstile> \<^bold>\<Or>p\<close>
      using assms by simp
  qed
  then have \<open>\<forall> p \<in> set (map disjunct W'). A \<turnstile> p\<close> 
    by simp
  moreover have \<open>A \<turnstile> map disjunct W' \<^bold>\<leadsto> \<^bold>\<Or> (map conjunct W)\<close>
  proof (rule A1,rule,rule,rule leads_to_evalI, rule ccontr)
    fix g h
    assume a1:\<open>\<forall>p\<in>set (map disjunct W'). eval g h p\<close>
    assume \<open>\<not>eval g h (\<^bold>\<Or> map conjunct W)\<close>
    then have \<open>\<forall> p \<in> set (map conjunct W). \<not>eval g h p\<close>
      using disjunct_evalI by blast
    then have \<open>\<forall> w \<in> set W. \<exists> p \<in> set w. \<not>eval g h p\<close>
      using conjunct_evalI by fastforce
    then have \<open>\<exists> w'. (\<forall> p \<in> set w'. \<not>eval g h p) \<and> ?P (set w') \<and> set w' \<subseteq> ?U\<close>
    proof (induct W)
      case Nil
      then show ?case
        by simp
    next
      case (Cons w W)
      then obtain w' where 
        \<open>(\<forall>p\<in>set w'. \<not> eval g h p) \<and> (\<forall>w\<in>set W. \<exists>p\<in>set w. p \<in> set w') \<and> set w' \<subseteq> \<Union> (set (map set W))\<close> 
        by auto
      moreover obtain p where \<open>p \<in> set w \<and> \<not>eval g h p\<close>
        using Cons by auto
      ultimately have \<open>
        (\<forall>p\<in>set (p # w'). \<not> eval g h p) \<and> 
        (\<forall>w\<in>set (w # W). \<exists> p'\<in>set w. p' \<in> set (p # w')) \<and> 
        set (p # w') \<subseteq> \<Union> (set (map set (w # W)))\<close> 
        by auto 
      then show ?case 
        by fast
    qed
    then obtain w' where w'_def: \<open>(\<forall> p \<in> set w'. \<not>eval g h p)\<close> \<open>?P (set w') \<and> set w' \<subseteq> ?U\<close>
      by auto
    then have \<open>set w' \<in> {w'. ?P w' \<and> w' \<subseteq> ?U}\<close> 
      by simp
    then have \<open>\<exists> w'' \<in> set W'. set w' = set w''\<close>
      using W'_def image_iff list.set_map by fastforce
    then have \<open>\<exists> w'' \<in> set W'. \<not>eval g h (\<^bold>\<Or>w'')\<close> 
      by (metis disjunct_evalE w'_def(1))
    then show \<open>False\<close> 
      using a1 by simp
  qed
  ultimately show ?thesis 
    using R1_leads_to by fast
qed

section \<open>Strong Soundness\<close>

corollary soundness_imply:
  assumes \<open>\<And>M w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>A \<turnstile> ps \<^bold>\<leadsto> p \<Longrightarrow> P; set ps \<TTurnstile>\<star> p\<close>
proof (induct ps arbitrary: p)
  case Nil
  then show ?case
    using soundness[of A P p] assms by simp
next
  case (Cons a ps)
  then show ?case
    using K_ImpI by fastforce
qed

theorem strong_soundness:
  assumes \<open>\<And>M w p. A p \<Longrightarrow> P M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  shows \<open>A; G \<turnstile> p \<Longrightarrow> P; G \<TTurnstile>\<star> p\<close>
proof safe
  fix qs w and M :: \<open>('a, 'b) kripke\<close>
  assume \<open>A \<turnstile> qs \<^bold>\<leadsto> p\<close>
  moreover assume \<open>set qs \<subseteq> G\<close> \<open>\<forall>q \<in> G. M, w \<Turnstile> q\<close>
  then have \<open>\<forall>q \<in> set qs. M, w \<Turnstile> q\<close>
    using \<open>set qs \<subseteq> G\<close> by blast
  moreover assume \<open>P M\<close> \<open>w \<in> \<W> M\<close>
  ultimately show \<open>M, w \<Turnstile> p\<close>
    using soundness_imply[of A P qs p] assms by blast
qed

section \<open>Completeness\<close>

subsection \<open>Consistent sets\<close>

definition consistent :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> bool\<close> where
  \<open>consistent A S \<equiv> \<not> (A; S \<turnstile> \<^bold>\<bottom>)\<close>

lemma inconsistent_subset:
  assumes \<open>consistent A V\<close> \<open>\<not> consistent A ({p} \<union> V)\<close>
  obtains V' where \<open>set V' \<subseteq> V\<close> \<open>A \<turnstile> p # V' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
proof -
  obtain V' where V': \<open>set V' \<subseteq> ({p} \<union> V)\<close> \<open>p \<in> set V'\<close> \<open>A \<turnstile> V' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then have *: \<open>A \<turnstile> p # V' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using K_imply_Cons by blast

  let ?S = \<open>removeAll p V'\<close>
  have \<open>set (p # V') \<subseteq> set (p # ?S)\<close>
    by auto
  then have \<open>A \<turnstile> p # ?S \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using * K_imply_weaken by blast
  moreover have \<open>set ?S \<subseteq> V\<close>
    using V'(1) by (metis Diff_subset_conv set_removeAll)
  ultimately show ?thesis
    using that by blast
qed

lemma consistent_consequent:
  assumes \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  shows \<open>consistent A ({q} \<union> V)\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> p # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using \<open>consistent A V\<close> \<open>p \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> q # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q)\<close> K_imply_head K_right_mp by (metis imply.simps(1-2))
  then show ?thesis
    using \<open>consistent A V\<close> inconsistent_subset by metis
qed

lemma consistent_consequent':
  assumes \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>tautology (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>consistent A ({q} \<union> V)\<close>
  using assms consistent_consequent A1 by blast

lemma consistent_disjuncts:
  assumes \<open>consistent A V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close>
  shows \<open>consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have \<open>\<not> consistent A ({p} \<union> V)\<close> \<open>\<not> consistent A ({q} \<union> V)\<close>
    by blast+

  then obtain S' T' where
    S': \<open>set S' \<subseteq> V\<close> \<open>A \<turnstile> p # S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> and
    T': \<open>set T' \<subseteq> V\<close> \<open>A \<turnstile> q # T' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using \<open>consistent A V\<close> inconsistent_subset by metis

  from S' have p: \<open>A \<turnstile> p # S' @ T' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by (metis K_imply_weaken Un_upper1 append_Cons set_append)
  moreover from T' have q: \<open>A \<turnstile> q # S' @ T' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by (metis K_imply_head K_right_mp R1 imply.simps(2) imply_append)
  ultimately have \<open>A \<turnstile> (p \<^bold>\<or> q) # S' @ T' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using K_DisL by blast
  then have \<open>A \<turnstile> S' @ T' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using S'(1) T'(1) p q \<open>consistent A V\<close> \<open>(p \<^bold>\<or> q) \<in> V\<close> unfolding consistent_def
    by (metis Un_subset_iff insert_subset list.simps(15) set_append)
  moreover have \<open>set (S' @ T') \<subseteq> V\<close>
    by (simp add: S'(1) T'(1))
  ultimately show False
    using \<open>consistent A V\<close> unfolding consistent_def by blast
qed

lemma exists_finite_inconsistent:
  assumes \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> V)\<close>
  obtains W where \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> W)\<close>
proof -
  obtain W' where W': \<open>set W' \<subseteq> {\<^bold>\<not> p} \<union> V\<close> \<open>A \<turnstile> W' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  let ?S = \<open>removeAll (\<^bold>\<not> p) W'\<close>
  have \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> set ?S)\<close>
    unfolding consistent_def using W'(2) by auto
  moreover have \<open>finite (set ?S)\<close>
    by blast
  moreover have \<open>{\<^bold>\<not> p} \<union> set ?S \<subseteq> {\<^bold>\<not> p} \<union> V\<close>
    using W'(1) by auto
  moreover have \<open>(\<^bold>\<not> p) \<notin> set ?S\<close>
    by simp
  ultimately show ?thesis
    by (meson that)
qed

lemma inconsistent_imply:
  assumes \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> set G)\<close>
  shows \<open>A \<turnstile> G \<^bold>\<leadsto> p\<close>
  using assms K_Boole K_imply_weaken unfolding consistent_def
  by (metis insert_is_Un list.simps(15))

subsection \<open>Maximal consistent sets\<close>

primrec sub_C where
  \<open>sub_C \<^bold>\<bottom> = {\<^bold>\<bottom>}\<close> |
  \<open>sub_C (Pro a) = {Pro a}\<close> |
  \<open>sub_C (p \<^bold>\<or> q) = insert (p \<^bold>\<or> q) (sub_C p \<union> sub_C q)\<close> |
  \<open>sub_C (p \<^bold>\<and> q) = insert (p \<^bold>\<and> q) (sub_C p \<union> sub_C q)\<close> |
  \<open>sub_C (p \<^bold>\<longrightarrow> q) = insert (p \<^bold>\<longrightarrow> q) (sub_C p \<union> sub_C q)\<close> |
  \<open>sub_C (K i p) = insert (K i p) (sub_C p)\<close> |
  \<open>sub_C (Ev g p) = {K i p | i. i \<in> set g} \<union> insert (Ev g p) (sub_C p)\<close> |
  \<open>sub_C (Co g p) = 
    {K i p | i. i \<in> set g} \<union>
    {K i (p \<^bold>\<and> Co g p) | i. i \<in> set g} \<union> 
    {Ev g (p \<^bold>\<and> Co g p), p \<^bold>\<and> Co g p, Co g p} \<union> sub_C p\<close>

lemma sub_C_finite: \<open>finite (sub_C p)\<close>
  by (induct p) auto

lemma p_in_sub_C_p: \<open>p \<in> sub_C p\<close>
  by (induct p) auto

abbreviation sub_C' where \<open>sub_C' p \<equiv> sub_C p \<union> (image Neg (sub_C p))\<close>

lemma sub_C'_finite: \<open>finite (sub_C' p)\<close> 
  by (simp add: sub_C_finite)

definition maximal' where
  \<open>maximal' A \<phi> S \<equiv> \<forall> p \<in> sub_C' \<phi>. p \<notin> S \<longrightarrow> \<not> consistent A ({p} \<union> S)\<close>

lemma extract_from_list: \<open>x \<in> set xs \<Longrightarrow> \<exists> ys. set (x # ys) = set xs \<and> x \<notin> set ys\<close>
  by (metis Diff_insert_absorb list.simps(15) mk_disjoint_insert set_removeAll)

lemma consistent_extend_by_p: \<open>consistent A V \<Longrightarrow> consistent A ({p} \<union> V) \<or> consistent A ({\<^bold>\<not>p} \<union> V)\<close>
proof (rule ccontr)
  assume \<open>consistent A V\<close>
  assume \<open>\<not> ?thesis\<close>
  then have \<open>A; ({p} \<union> V) \<turnstile> \<^bold>\<bottom>\<close> \<open>A; ({\<^bold>\<not>p} \<union> V) \<turnstile> \<^bold>\<bottom>\<close>
    unfolding consistent_def by simp_all
  then obtain qs rs where qs_rs_def:
    \<open>set qs \<subseteq> {p} \<union> V\<close> \<open>set rs \<subseteq> {\<^bold>\<not>p} \<union> V\<close> \<open>A \<turnstile> qs \<^bold>\<leadsto> \<^bold>\<bottom>\<close> \<open>A \<turnstile> rs \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by auto
  then consider \<open>set qs \<subseteq> V \<or> set rs \<subseteq> V\<close> | \<open>p \<in> set qs \<and> \<^bold>\<not>p \<in> set rs\<close> 
    by auto
  then show False
  proof cases
    case 1
    then have \<open>\<not> consistent A V\<close>
      using qs_rs_def consistent_def by blast
    then show ?thesis 
      using \<open>consistent A V\<close> ..
  next
    case 2
    then obtain qs' rs' where 
      \<open>set (p # qs') = set qs\<close> \<open>set (\<^bold>\<not>p # rs') = set rs\<close> \<open>p \<notin> set qs'\<close> \<open>\<^bold>\<not>p \<notin> set rs'\<close>
      using extract_from_list by meson
    then have \<open>set qs' \<subseteq> V \<and> set rs' \<subseteq> V\<close> 
      using qs_rs_def by auto
    have \<open>A \<turnstile> p # qs' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> \<open>A \<turnstile> \<^bold>\<not>p # rs' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
      using \<open>set (p # qs') = set qs\<close> \<open>set (\<^bold>\<not>p # rs') = set rs\<close> qs_rs_def(3,4)
      by (metis K_imply_weaken order_refl)+
    then have \<open>A \<turnstile> qs' @ rs' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
      by (metis K_ImpI K_imply_head K_right_mp R1 imply.simps(2) imply_append)
    then have \<open>\<not> consistent A V\<close>
      using \<open>set qs' \<subseteq> V \<and> set rs' \<subseteq> V\<close> consistent_def
      by (metis Un_subset_iff set_append)
    then show ?thesis 
      using \<open>consistent A V\<close> ..
  qed
qed

lemma comp_in_sub_C: \<open>comp p \<in> sub_C' \<phi>\<close> if \<open>p \<in> sub_C' \<phi>\<close>
proof (cases \<open>\<exists> p'. p = \<^bold>\<not> p'\<close>)
  case True
  then obtain p' where \<open>p = \<^bold>\<not>p'\<close> ..
  then have \<open>comp p = p'\<close>
    by simp
  have \<open>p' \<in> sub_C' \<phi>\<close>
  proof (cases \<open>p \<in> sub_C \<phi>\<close>)
    case True
    from this \<open>p = \<^bold>\<not>p'\<close> have \<open>p' \<in> sub_C \<phi>\<close>
    proof (induct \<phi>)
      case (Imp \<phi>1 \<phi>2)
      then show ?case 
        using p_in_sub_C_p by (cases \<open>\<phi>2 = \<^bold>\<bottom>\<close>,force,auto)
    qed auto
    then show ?thesis 
      by simp
  next
    case False
    then show ?thesis
      using \<open>comp p = p'\<close> \<open>p \<in> sub_C' \<phi>\<close> by fastforce
  qed
  then show ?thesis 
    by (simp add: \<open>comp p = p'\<close>)
next
  case False
  then have \<open>comp p = \<^bold>\<not>p\<close>
  proof (cases p)
    case (Imp p q)
    then show ?thesis 
      using False by (cases q) auto
  qed auto
  then show ?thesis 
    using False that by auto
qed


lemma deriv_in_maximal': 
  assumes \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>p \<in> sub_C' \<phi>\<close> \<open>A \<turnstile> p\<close>
  shows \<open>p \<in> V\<close>
  using assms R1 inconsistent_subset unfolding consistent_def maximal'_def
  by (metis imply.simps(2))

lemma consequent_in_maximal':
  assumes \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>set ps \<subseteq> sub_C' \<phi>\<close> \<open>q \<in> sub_C' \<phi>\<close> \<open>set ps \<subseteq> V\<close>
    \<open>A \<turnstile> ps \<^bold>\<leadsto> q\<close>
  shows \<open>q \<in> V\<close>
proof-
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> ps @ V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using \<open>consistent A V\<close> \<open>set ps \<subseteq> V\<close> unfolding consistent_def 
    by simp
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> ps @ (ps \<^bold>\<leadsto> q) # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (metis K_imply_weaken K_right_mp \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> ps @ V' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> assms(6) imply.simps(2) imply_append inf_sup_ord(4) set_append)
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> q # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close> 
    by (metis K_imply_head K_right_mp R1 \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> A \<turnstile> ps @ V' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> assms(6) imply.simps(2) imply_append)
  then have \<open>consistent A ({q} \<union> V)\<close>
    using \<open>consistent A V\<close> inconsistent_subset by metis
  then show ?thesis
    using \<open>maximal' A \<phi> V\<close> \<open>q \<in> sub_C' \<phi>\<close> maximal'_def by blast
qed

lemma exactly_one_in_maximal': 
  assumes \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>p \<in> sub_C' \<phi>\<close> \<open>V \<subseteq> sub_C' \<phi>\<close>
  shows \<open>p \<in> V \<longleftrightarrow> comp p \<notin> V\<close> 
proof
  assume \<open>p \<in> V\<close>
  have \<open>A \<turnstile> p \<^bold>\<longrightarrow> \<^bold>\<not>(comp p)\<close>
    by (simp add: comp_imp1)
  then have \<open>A \<turnstile> [comp p,p] \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by (metis K_swap imply.simps(1) imply.simps(2))
  then show \<open>comp p \<notin> V\<close>
    using \<open>consistent A V\<close> \<open>p \<in> sub_C' \<phi>\<close> \<open>p \<in> V\<close> 
    by (metis Un_insert_right consistent_def empty_set inf_sup_ord(4) insert_absorb list.simps(15) sup_bot.right_neutral)
next
  assume \<open>comp p \<notin> V\<close>
  then have \<open>\<not> consistent A ({comp p} \<union> V)\<close>
    using comp_in_sub_C assms unfolding maximal'_def by auto
  then obtain qs where qs_def: \<open>set qs \<subseteq> V\<close> \<open>A \<turnstile> (comp p) # qs \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by (meson assms(1) inconsistent_subset)
  then have \<open>A \<turnstile> qs \<^bold>\<leadsto> \<^bold>\<not>(comp p)\<close>
    by (simp add: K_ImpI)
  then have \<open>A \<turnstile> qs \<^bold>\<leadsto> p\<close> 
    by (simp add: comp_imp2 imply_chain)
  then show \<open>p \<in> V\<close>
    using assms \<open>set qs \<subseteq> V\<close> deriv_in_maximal' comp_in_sub_C 
    by (smt (verit) consequent_in_maximal' dual_order.trans)
qed

subsection \<open>Lindenbaum extension\<close>

instantiation fm :: (countable) countable begin
instance by countable_datatype
end

lemma UN_finite_bound:
  assumes \<open>finite A\<close> \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

primrec extend' :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> nat \<Rightarrow> 'i fm set\<close> where
  \<open>extend' A \<phi> S f 0 = S\<close>
| \<open>extend' A \<phi> S f (Suc n) =
    (if f n \<in> sub_C' \<phi> \<and> consistent A ({f n} \<union> extend' A \<phi> S f n)
     then {f n} \<union> extend' A \<phi> S f n
     else extend' A \<phi> S f n)\<close>

definition Extend' :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> 'i fm set\<close> where
  \<open>Extend' A \<phi> S f \<equiv> \<Union>n. extend' A \<phi> S f n\<close>

lemma extend'_subset_sub_C: \<open>S \<subseteq> sub_C' \<phi> \<Longrightarrow> extend' A \<phi> S f n \<subseteq> sub_C' \<phi>\<close>
  by (induct n) auto

lemma Extend'_subset_sub_C: \<open>S \<subseteq> sub_C' \<phi> \<Longrightarrow> Extend' A \<phi> S f \<subseteq> sub_C' \<phi>\<close>
  using extend'_subset_sub_C unfolding Extend'_def by blast

lemma Extend'_subset: \<open>S \<subseteq> Extend' A \<phi> S f\<close>
  unfolding Extend'_def using Union_upper extend'.simps(1) range_eqI
  by metis

lemma extend'_bound: \<open>(\<Union>n \<le> m. extend' A \<phi> S f n) = extend' A \<phi> S f m\<close>
  by (induct m) (simp_all add: atMost_Suc)

lemma consistent_extend': \<open>consistent A S \<Longrightarrow> consistent A (extend' A \<phi> S f n)\<close>
  by (induct n) simp_all

lemma consistent_Extend':
  assumes \<open>consistent A S\<close>
  shows \<open>consistent A (Extend' A \<phi> S f)\<close>
  unfolding Extend'_def
proof (rule ccontr)
  assume \<open>\<not> consistent A (\<Union>n. extend' A \<phi> S f n)\<close>
  then obtain S' where \<open>A \<turnstile> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> (\<Union>n. extend' A \<phi> S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend' A \<phi> S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend' A \<phi> S f m\<close>
    using extend'_bound by blast
  moreover have \<open>consistent A (extend' A \<phi> S f m)\<close>
    using assms consistent_extend' by blast
  ultimately show False
    unfolding consistent_def using \<open>A \<turnstile> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> by blast
qed

lemma maximal_Extend':
  assumes \<open>surj f\<close>
  shows \<open>maximal' A \<phi> (Extend' A \<phi> S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal' A \<phi> (Extend' A \<phi> S f)\<close>
  then obtain p where \<open>p \<in> sub_C' \<phi>\<close> \<open>p \<notin> Extend' A \<phi> S f\<close> \<open>consistent A ({p} \<union> Extend' A \<phi> S f)\<close>
    unfolding maximal'_def using assms by blast
  obtain k where n: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend' A \<phi> S f (Suc k)\<close>
    using \<open>p \<notin> Extend' A \<phi> S f\<close> unfolding Extend'_def by blast
  then have \<open>\<not> consistent A ({p} \<union> extend' A \<phi> S f k)\<close>
    using n \<open>p \<in> sub_C' \<phi>\<close> by auto
  moreover have \<open>{p} \<union> extend' A \<phi> S f k \<subseteq> {p} \<union> Extend' A \<phi> S f\<close>
    unfolding Extend'_def by blast
  ultimately have \<open>\<not> consistent A ({p} \<union> Extend' A \<phi> S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent A ({p} \<union> Extend' A \<phi> S f)\<close> by blast
qed

lemma maximal_extension':
  fixes V :: \<open>('i :: countable) fm set\<close>
  assumes \<open>V \<subseteq> sub_C' \<phi>\<close> \<open>consistent A V\<close>
  obtains W where \<open>V \<subseteq> W\<close> \<open>W \<subseteq> sub_C' \<phi>\<close> \<open>consistent A W\<close> \<open>maximal' A \<phi> W\<close>
proof -
  let ?W = \<open>Extend' A \<phi> V from_nat\<close>
  have \<open>V \<subseteq> ?W\<close>
    using Extend'_subset by blast
  moreover have \<open>consistent A ?W\<close>
    using assms consistent_Extend' by blast
  moreover have \<open>maximal' A \<phi> ?W\<close>
    using assms maximal_Extend' surj_from_nat by blast
  moreover have \<open>?W \<subseteq> sub_C' \<phi>\<close> 
    using assms Extend'_subset_sub_C by blast
  ultimately show ?thesis
    using that by blast
qed

subsection \<open>Canonical model\<close>

abbreviation pi :: \<open>'i fm set \<Rightarrow> id \<Rightarrow> bool\<close> where
  \<open>pi V x \<equiv> Pro x \<in> V\<close>

abbreviation known :: \<open>'i fm set \<Rightarrow> 'i \<Rightarrow> 'i fm set\<close> where
  \<open>known V i \<equiv> {p. K i p \<in> V}\<close>

abbreviation reach :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i \<Rightarrow> 'i fm set \<Rightarrow> 'i fm set set\<close> where
  \<open>reach A i V \<equiv> {W. known V i \<subseteq> W}\<close> 

abbreviation mcss :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> 'i fm set set\<close> where
  \<open>mcss A \<phi> \<equiv> {W. W \<subseteq> sub_C' \<phi> \<and> consistent A W \<and> maximal' A \<phi> W}\<close>

abbreviation canonical :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> ('i, 'i fm set) kripke\<close> where
  \<open>canonical A \<phi> \<equiv> \<lparr>\<W> = mcss A \<phi>, \<K> = reach A, \<pi> = pi\<rparr>\<close>

lemma sub_C_transitive: \<open>p \<in> sub_C q \<Longrightarrow> q \<in> sub_C r \<Longrightarrow> p \<in> sub_C r\<close>
  by (induct r, induct q, auto)

lemma sub_sub_C': \<open>p \<in> sub_C' \<phi> \<Longrightarrow> q \<in> sub_C p \<Longrightarrow> q = \<^bold>\<bottom> \<or> q \<in> sub_C' \<phi>\<close>
proof-
  assume \<open>q \<in> sub_C p\<close>
  assume \<open>p \<in> sub_C' \<phi>\<close>
  then consider \<open>p \<in> sub_C \<phi>\<close> | \<open>p \<in> image Neg (sub_C \<phi>)\<close>
    by auto
  then show ?thesis
  proof cases
    case 1
    from this \<open>q \<in> sub_C p\<close> have \<open>q \<in> sub_C \<phi>\<close>
      using sub_C_transitive by auto
    then show ?thesis
      by simp
  next
    case 2
    then obtain p' where \<open>p = \<^bold>\<not>p'\<close> \<open>p' \<in> sub_C \<phi>\<close>
      by auto
    moreover have \<open>q \<in> sub_C p \<longrightarrow> p = \<^bold>\<not>p' \<longrightarrow> q \<in> sub_C p' \<or> q = p \<or> q = \<^bold>\<bottom>\<close> 
      by (cases p) auto
    ultimately show ?thesis 
      by (metis UnI1 \<open>p \<in> sub_C' \<phi>\<close> \<open>q \<in> sub_C p\<close> sub_C_transitive)
  qed 
qed


lemma truth_lemma_Ka: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prems: \<open>V \<in> mcss A \<phi>\<close> \<open>K i p \<in> sub_C' \<phi>\<close>
  assumes hyp: \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
  assumes \<open>canonical A \<phi>, V \<Turnstile> K i p\<close> 
  shows \<open>K i p \<in> V\<close>
proof-
  from \<open>K i p \<in> sub_C' \<phi>\<close> have \<open>p \<in> sub_C \<phi>\<close>  
    by (metis (no_types, lifting) Un_iff fm.distinct(45) image_iff insert_iff p_in_sub_C_p sub_C.simps(6) sub_C_transitive)
  then have \<open>\<^bold>\<not> p \<in> sub_C' \<phi>\<close> 
    by simp
  moreover have \<open>\<forall> p. K i p \<in> V \<longrightarrow> p \<in> sub_C' \<phi>\<close>
    using \<open>V \<in> mcss A \<phi>\<close>
    by (smt (verit, ccfv_SIG) Un_iff fm.distinct(45) image_iff insertCI insert_absorb insert_subset mem_Collect_eq p_in_sub_C_p sub_C.simps(6) sub_C_transitive)
  ultimately have \<open>{\<^bold>\<not> p} \<union> known V i \<subseteq> sub_C' \<phi>\<close>
    by auto

  have \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
  proof
    assume \<open>consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
    then obtain W where W: \<open>{\<^bold>\<not> p} \<union> known V i \<subseteq> W\<close> \<open>W \<subseteq> sub_C' \<phi>\<close> \<open>consistent A W\<close> \<open>maximal' A \<phi> W\<close>
      using \<open>{\<^bold>\<not> p} \<union> known V i \<subseteq> sub_C' \<phi>\<close> \<open>V \<in> mcss A \<phi>\<close> maximal_extension' by (smt (verit, best))
    then have \<open>canonical A \<phi>, W \<Turnstile> \<^bold>\<not> p\<close>
      using \<open>V \<in> mcss A \<phi>\<close> exactly_one_in_maximal' 
      by (smt (verit) Imp_intro comp.simps(1) hyp insertCI mem_Collect_eq subset_iff sup.boundedE)
    moreover have \<open>W \<in> reach A i V\<close> \<open>W \<in> mcss A \<phi>\<close>
      using W by simp_all
    ultimately have \<open>canonical A \<phi>, V \<Turnstile> \<^bold>\<not> K i p\<close>
      by auto
    then show False
      using \<open>canonical A \<phi>, V \<Turnstile> K i p\<close> by auto
  qed

  then obtain W where W:
    \<open>{\<^bold>\<not> p} \<union> W \<subseteq> {\<^bold>\<not> p} \<union> known V i\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> W)\<close>
    using exists_finite_inconsistent by metis

  obtain L where L: \<open>set L = W\<close>
    using \<open>finite W\<close> finite_list by blast

  then have \<open>A \<turnstile> L \<^bold>\<leadsto> p\<close>
    using W(4) inconsistent_imply by blast
  then have \<open>A \<turnstile> K i (L \<^bold>\<leadsto> p)\<close>
    using R2 by fast
  then have \<open>A \<turnstile> map (K i) L \<^bold>\<leadsto> K i p\<close>
    using K_distrib_K_imp by fast
  moreover have \<open>set (map (K i) L) \<subseteq> V\<close> 
    using L W(1,2) by auto
  moreover have \<open>set (map (K i) L) \<subseteq> sub_C' \<phi>\<close> 
    using calculation(2) prems(1) by blast
  ultimately show \<open>K i p \<in> V\<close>
    using \<open>K i p \<in> sub_C' \<phi>\<close> consequent_in_maximal' prems(1) by blast
qed

lemma consistent_implies: \<open>\<forall> q \<in> w'. \<exists> p \<in> w.  A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> consistent A w \<Longrightarrow> consistent A w'\<close> 
proof (rule ccontr)
  assume 1: \<open>\<forall> q \<in> w'. \<exists> p \<in> w.  A \<turnstile> p \<^bold>\<longrightarrow> q \<close>
  assume 2: \<open>consistent A w\<close>
  assume \<open>\<not> consistent A w'\<close>
  then obtain qs where ps_def: \<open>A \<turnstile> qs \<^bold>\<leadsto> \<^bold>\<bottom>\<close> \<open>set qs \<subseteq> w'\<close> 
    unfolding consistent_def by fastforce
  then have \<open>\<forall> q \<in> set qs. \<exists> p \<in> w. A \<turnstile> p \<^bold>\<longrightarrow> q\<close> 
    using 1 by auto
  then have \<open>\<exists> ps. (\<forall> q \<in> set qs. \<exists> p \<in> set ps. A \<turnstile> p \<^bold>\<longrightarrow> q) \<and> set ps \<subseteq> w\<close>
  proof (induct qs)
    case Nil
    then show ?case 
      by fastforce
  next
    case (Cons q qs)
    then obtain ps where \<open>(\<forall>q\<in>set qs. \<exists>p\<in>set ps. A \<turnstile> p \<^bold>\<longrightarrow> q) \<and> set ps \<subseteq> w\<close>
      by auto
    moreover obtain p where \<open>p \<in> w \<and> A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
      using Cons by auto
    ultimately have \<open>(\<forall>q\<in>set (q # qs). \<exists>p\<in>set (p # ps). A \<turnstile> p \<^bold>\<longrightarrow> q) \<and> set (p # ps) \<subseteq> w\<close> 
      by simp
    then show ?case 
      by fast
  qed  
  then obtain ps where \<open>\<forall> q \<in> set qs. \<exists> p \<in> set ps. A \<turnstile> p \<^bold>\<longrightarrow> q\<close> \<open>set ps \<subseteq> w\<close>
    by auto
  then have \<open>A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<And>qs\<close> 
  proof (induct qs)
    case Nil
    then show ?case 
      using K_ImpI K_imply_head by fastforce
  next
    case (Cons q qs)
    then obtain p where \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close> \<open>p \<in> set ps\<close>
      by auto
    moreover have \<open>A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<And> qs\<close> 
      using Cons by simp
    ultimately have \<open>A \<turnstile> p # ps \<^bold>\<leadsto>  \<^bold>\<And>q # qs\<close> 
      using add_assm_and_concl by fastforce
    then show ?case
      using \<open>p \<in> set ps\<close> K_ImpI K_right_mp conjunct_implies_elem imply_chain imply_implies_itself by blast
  qed
  from ps_def(1) this have \<open>A \<turnstile> ps \<^bold>\<leadsto> \<^bold>\<bottom>\<close> 
    by (meson R1 imply_chain imply_implies_conjunct)
  then show False
    using \<open>consistent A w\<close> \<open>set ps \<subseteq> w\<close> consistent_def by blast
qed


(*exercise 3.28*)
lemma Co_lemma:
  fixes A \<phi> g 
  fixes p :: \<open>('i :: countable) fm\<close>
  defines \<open>WCo \<equiv> {W. W \<in> mcss A \<phi> \<and> canonical A \<phi>, W \<Turnstile> Co g p}\<close>
  assumes \<open>Co g p \<in> sub_C' \<phi>\<close>
  assumes \<open>set (map set \<w>) = WCo\<close>
  assumes \<open>\<phi>\<^sub>\<w> = disjunct (map conjunct \<w>)\<close>
  assumes \<open>V \<in> mcss A \<phi>\<close>
  assumes hyp: \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
  shows \<open>A \<turnstile> \<phi>\<^sub>\<w> \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>
proof -
  (*formulas named after the tasks in the exercise*)
  have \<open>Co g p \<in> sub_C \<phi>\<close> 
    using assms(2) by auto
  have a: \<open>i \<in> set g \<Longrightarrow> w \<in> set \<w> \<Longrightarrow> A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i p\<close> for w i
  proof-
    assume \<open>i \<in> set g\<close>
    assume \<open>w \<in> set \<w>\<close>
    then have \<open>set w \<in> WCo\<close>
      using \<open>set (map set \<w>) = WCo\<close> by auto
    then have \<open>set w \<in> mcss A \<phi>\<close> \<open>canonical A \<phi>, set w \<Turnstile> Co g p\<close>
      unfolding WCo_def by simp_all
    then have \<open>canonical A \<phi>, set w \<Turnstile> K i p\<close> 
      using \<open>i \<in> set g\<close> by auto
    moreover have \<open>K i p \<in> sub_C \<phi>\<close> 
      using \<open>Co g p \<in> sub_C \<phi>\<close> \<open>i \<in> set g\<close> 
      by (induct \<phi>) auto
    ultimately have \<open>K i p \<in> set w\<close>
      using hyp \<open>set w \<in> mcss A \<phi>\<close>  truth_lemma_Ka by blast
    then show ?thesis 
    proof (induct w)
      case Nil
      then show ?case 
        by auto
    next
      case (Cons a w)
      then show ?case 
        by (metis K_imply_Cons K_imply_head R1 conjunct_implies_imply imply_implies_conjunct set_ConsD)
    qed 
  qed
  define WNCo where \<open>WNCo \<equiv> {W \<in> mcss A \<phi>. \<not> canonical A \<phi>, W \<Turnstile> Co g p}\<close>
  have b: \<open>i \<in> set g \<Longrightarrow> w \<in> set \<w> \<Longrightarrow> set w' \<in> WNCo \<Longrightarrow> A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<not> (\<^bold>\<And> w'))\<close> for w' w i
  proof-
    assume \<open>i \<in> set g\<close> \<open>w \<in> set \<w>\<close> \<open>set w' \<in> WNCo\<close>
    then have \<open>set w \<in> WCo\<close>
      using \<open>set (map set \<w>) = WCo\<close> by auto
    then have E: \<open>set w \<in> mcss A \<phi>\<close> \<open>set w' \<in> mcss A \<phi>\<close> \<open>canonical A \<phi>, set w \<Turnstile> Co g p\<close>  \<open>\<not> canonical A \<phi>, set w' \<Turnstile> Co g p\<close>
      using \<open>set w' \<in> WNCo\<close> unfolding WNCo_def WCo_def by simp_all
    have \<open>set w' \<notin> reach A i (set w)\<close> 
    proof (rule ccontr)
      assume \<open>\<not> set w' \<notin> reach A i (set w)\<close>
      then have 1: \<open>set w' \<in> \<K> (canonical A \<phi>) i (set w)\<close>
        by simp
      from E(4) obtain k where 2: \<open>\<not> canonical A \<phi>, set w' \<Turnstile> Ev_n g p k\<close> 
        by auto
      have \<open>canonical A \<phi>, set w \<Turnstile> Ev_n g p (k + 1)\<close> 
        using E(3) by fastforce
      then have \<open>canonical A \<phi>, set w \<Turnstile> K i (Ev_n g p k)\<close>
        using \<open>i \<in> set g\<close> by simp
      then have \<open>canonical A \<phi>, set w' \<Turnstile> Ev_n g p k\<close>
        using 1 \<open>set w' \<in> mcss A \<phi>\<close> by simp
      then show False 
        using 2 by simp
    qed
    then obtain q where q_def: \<open>K i q \<in> set w \<and> q \<notin> set w'\<close> 
      by auto
    then have \<open>K i q \<in> sub_C' \<phi>\<close> 
      using E(1) by blast
    then have \<open>K i q \<in> sub_C \<phi>\<close> 
      by blast
    then have \<open>q \<in> sub_C \<phi>\<close>
      by (metis insertI2 p_in_sub_C_p sub_C.simps(6) sub_C_transitive)
    then have \<open>\<not> consistent A (insert q (set w'))\<close>
      using E(2) insert_is_Un maximal'_def mem_Collect_eq q_def by fastforce
    then have \<open>A \<turnstile> q # w' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> 
      by (metis K_imply_weaken consistent_def list.simps(15))
    then have \<open>A \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<And>w')\<close>
      by (metis imp_chain imply.simps(2) imply_implies_conjunct)
    then have \<open>A \<turnstile> K i q \<^bold>\<longrightarrow> K i (\<^bold>\<not>(\<^bold>\<And>w'))\<close>
      by (simp add: K_map)
    then show ?thesis 
      using q_def conjunct_implies_elem imp_chain by blast
  qed
  obtain \<w>' where \<open>set (map set \<w>') = WNCo\<close> 
  proof-
    have \<open>finite (mcss A \<phi>)\<close>
      using sub_C'_finite by fast
    then have \<open>finite WNCo\<close> 
      unfolding WNCo_def by fastforce
    moreover have \<open>\<forall> w' \<in> WNCo. finite w'\<close> 
      unfolding WNCo_def 
      by (smt (verit) mem_Collect_eq rev_finite_subset sub_C'_finite)
    ultimately show \<open>(\<And>\<w>'. set (map set \<w>') = WNCo \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      using list_of_lists_if_finite_set_of_sets by blast
  qed
  have c: \<open>i \<in> set g \<Longrightarrow> w \<in> set \<w> \<Longrightarrow> A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (p \<^bold>\<and> (\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>'))\<close> for w i 
  proof-
    assume \<open>i \<in> set g\<close> \<open>w \<in> set \<w>\<close>
    then have \<open>\<forall> w' \<in> set \<w>'. A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<not>(\<^bold>\<And> w'))\<close>
      using b \<open>set (map set \<w>') = WNCo\<close> by auto
    then have \<open>A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>')\<close>
    proof (induct \<w>')
      case Nil
      then show ?case 
        by (metis R1 R2 conE1 conE2 con_imp_antecedents conjunct.simps(1) list.simps(8))
    next
      case (Cons w' \<w>')
      then have \<open>A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<And> map (\<lambda>w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>')\<close> 
        by simp
      moreover have \<open>A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<not> (\<^bold>\<And> w'))\<close>
        using Cons.prems by simp
      ultimately have \<open>A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (\<^bold>\<not> (\<^bold>\<And> w') \<^bold>\<and> (\<^bold>\<And> map (\<lambda>w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>'))\<close> 
        using conjunction_in_K by fast
      then show ?case
        by simp
    qed
    then show ?thesis
      using a \<open>i \<in> set g\<close> \<open>w \<in> set \<w>\<close> conjunction_in_K by fast
  qed
  have d_hint: \<open>A \<turnstile> (\<^bold>\<Or> (map conjunct \<w>)) \<^bold>\<or> (\<^bold>\<Or> (map conjunct \<w>'))\<close>
  proof-
    have \<open>(set (map set \<w>) \<union> set (map set \<w>')) = mcss A \<phi>\<close>
      using \<open>set (map set \<w>) = WCo\<close> \<open>set (map set \<w>') = WNCo\<close> unfolding WCo_def WNCo_def 
      using Collect_cong Collect_disj_eq mem_Collect_eq by auto
    then have \<open>set (map set (\<w> @ \<w>')) = mcss A \<phi>\<close> 
      by simp
    moreover have \<open>set (map set W) = mcss A \<phi> \<Longrightarrow> A \<turnstile> \<^bold>\<Or> map conjunct W\<close> for W 
    proof (rule ccontr)
      assume a: \<open>set (map set W) = mcss A \<phi>\<close> \<open>\<not>A \<turnstile> \<^bold>\<Or> map conjunct W\<close> 
      {
        from a(2) have \<open>\<exists> w'. (\<forall> w \<in> set W. \<exists> p \<in> set w. p \<in> set w') \<and> \<not>A \<turnstile> \<^bold>\<Or> w'\<close> 
          using combine_disjunct by blast
        then obtain w' where w'_def: \<open>(\<forall> w \<in> set W. \<exists> p \<in> set w. p \<in> set w')\<close> \<open>\<not>A \<turnstile> \<^bold>\<Or> w'\<close>
          by auto
        then have \<open>\<not>A \<turnstile> \<^bold>\<not>(\<^bold>\<And> map Neg w')\<close>
          by (metis K_Boole de_morgan_conjunct imp_chain imply.simps(1) imply.simps(2))
        have \<open>consistent A {\<^bold>\<And> map Neg w'}\<close> 
        proof (rule ccontr)
          assume \<open>\<not>consistent A {\<^bold>\<And> map Neg w'}\<close>
          then have \<open>A \<turnstile> [\<^bold>\<And> map Neg w'] \<^bold>\<leadsto> \<^bold>\<bottom>\<close> 
            unfolding consistent_def 
            by (metis (mono_tags, lifting) K_imply_weaken empty_set list.simps(15))
          then have \<open>A \<turnstile> \<^bold>\<not>(\<^bold>\<And> map Neg w')\<close>
            by simp
          from \<open>\<not>A \<turnstile> \<^bold>\<not>(\<^bold>\<And> map Neg w')\<close> this show False ..
        qed
        moreover have \<open>\<forall> w \<in> set W. \<exists> p \<in> set w. \<^bold>\<not>p \<in> set (map Neg w')\<close>
          using w'_def(1) by fastforce
        ultimately have \<open>\<exists> w'. consistent A {\<^bold>\<And>w'} \<and> (\<forall> w \<in> set W. \<exists> p \<in> set w. \<^bold>\<not>p \<in> set w')\<close> 
          by fast
      }
      then have \<open>\<exists> w'. consistent A (set w') \<and> (\<forall> w \<in> set W. \<exists> p \<in> set w. \<^bold>\<not>p \<in> set w')\<close>
        by (metis conjunct_implies_elem consistent_implies insertI1)
      then have \<open>\<exists> w'. consistent A w' \<and> (\<forall> w \<in> set W. \<exists> p \<in> set w. comp p \<in> w') \<and> w' \<subseteq> sub_C' \<phi>\<close> 
      proof
        fix w'
        assume a': \<open>consistent A w' \<and> (\<forall> w \<in> set W. \<exists> p \<in> set w. \<^bold>\<not>p \<in> w')\<close>
        define wp where \<open>wp \<equiv> {p. (\<exists> w \<in> set W. p \<in> set w) \<and> (\<^bold>\<not>p \<in> w')}\<close>
        then have \<open>\<forall> p \<in> wp. p \<in> sub_C' \<phi>\<close>
          using a(1) by auto
        then have 1:\<open>\<forall> p \<in> wp. comp p \<in> sub_C' \<phi>\<close> 
          by (metis comp_in_sub_C)
        have \<open>finite (mcss A \<phi>)\<close>
          by (metis List.finite_set a(1))
        moreover have \<open>\<forall> w \<in> mcss A \<phi>. finite w\<close> 
          by (metis List.finite_set a(1) ex_map_conv)
        ultimately have f: \<open>finite wp\<close> 
          unfolding wp_def using a by simp
        have 2: \<open>\<forall> w \<in> set W. \<exists> p \<in> set w. comp p \<in> image comp wp\<close>
          using wp_def a' by blast
        have \<open>image Neg wp \<subseteq> w'\<close>
          using wp_def by auto
        then have \<open>consistent A (image Neg wp)\<close>
          using a'(1) unfolding consistent_def by simp
        moreover have \<open>\<forall> p. A \<turnstile> \<^bold>\<not>p \<^bold>\<longrightarrow> comp p\<close> 
          by (metis K_trans R1 comp_imp1 comp_imp2 con_imp_antecedents swap_antecedents)
        ultimately have \<open>consistent A (image comp wp)\<close>
          using consistent_implies by (smt (verit, ccfv_SIG) imageE image_eqI)
        from 1 2 this show ?thesis
          by blast
      qed
      then obtain w' where w'_def: 
        \<open>consistent A w'\<close> \<open>\<forall> w \<in> set W. \<exists> p \<in> set w. comp p \<in> w'\<close> \<open>w' \<subseteq> sub_C' \<phi>\<close>
        by auto
      then obtain mw' where mw'_def: \<open>consistent A mw'\<close> \<open>maximal' A \<phi> mw'\<close> \<open>w' \<subseteq> mw'\<close> \<open>mw' \<subseteq> sub_C' \<phi>\<close>
        using maximal_extension' by metis
      moreover have \<open>mw' \<notin> mcss A \<phi>\<close> 
      proof-
        have \<open>\<forall> w. w \<in> mcss A \<phi> \<longrightarrow> w \<in> set (map set W)\<close>
          using a(1) by simp
        then have \<open>\<forall> w \<in> mcss A \<phi>. \<exists> ps \<in> set W. set ps = w\<close> 
          by (metis (no_types, lifting) image_iff list.set_map)
        then have \<open>\<forall> w \<in> mcss A \<phi>. \<exists> p \<in> w. comp p \<in> mw'\<close> 
          using \<open>w' \<subseteq> mw'\<close> w'_def(2) by (metis a(1) subset_iff)
        moreover have \<open>\<forall> p. A \<turnstile> [p,comp p] \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
          by (simp add: comp_imp1)
        ultimately have \<open>\<forall> w \<in> mcss A \<phi>. w \<noteq> mw'\<close>
          unfolding consistent_def 
          by (smt (verit, best) exactly_one_in_maximal' mw'_def(1) mw'_def(2) mw'_def(4) subset_iff)
        then show ?thesis 
          by blast
      qed
      ultimately show False
        by simp
    qed
    ultimately have \<open>A \<turnstile> \<^bold>\<Or> map conjunct (\<w> @ \<w>')\<close> 
      by presburger
    then show ?thesis 
        by (metis R1 disjunct_split map_append)
  qed
  have d: \<open>A \<turnstile> (\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>') \<^bold>\<longrightarrow> \<phi>\<^sub>\<w>\<close>
  proof-
    have \<open>A \<turnstile> (\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>') \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<Or> (map conjunct \<w>'))\<close>
    proof-
      have \<open>(\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>') = (\<^bold>\<And> map Neg (map conjunct \<w>'))\<close>
        by (induct \<w>') auto
      then show ?thesis
        using extract_neg_conjunct by metis
    qed
    moreover have \<open>A \<turnstile> \<^bold>\<not>(\<^bold>\<Or> (map conjunct \<w>')) \<^bold>\<longrightarrow> (\<^bold>\<Or> (map conjunct \<w>))\<close>
      using d_hint dis_to_imp by auto
    ultimately show ?thesis
      using imp_chain assms(4) by auto
    qed
  have e: \<open>i \<in> set g \<Longrightarrow> w \<in> set \<w> \<Longrightarrow> A \<turnstile> \<^bold>\<And> w \<^bold>\<longrightarrow> K i (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close> for w i 
  proof- 
    assume \<open>i \<in> set g\<close>
    moreover assume \<open>w \<in> set \<w>\<close>
    ultimately have \<open>A \<turnstile>  K i (p \<^bold>\<and> (\<^bold>\<And> map (\<lambda> w'. \<^bold>\<not> (\<^bold>\<And> w')) \<w>')) \<^bold>\<longrightarrow> K i (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>
      using d R1 by (metis K_map conE1 con_imp2 con_imp_antecedents)
    then show ?thesis
      using \<open>i \<in> set g\<close> \<open>w \<in> set \<w>\<close> c d imp_chain by fast
  qed
  then show f: ?thesis 
  proof -
    have *:\<open>\<forall> p \<in> set ps. A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> \<^bold>\<Or> ps \<^bold>\<longrightarrow> q\<close> for ps q
    proof (induct ps)
      case Nil
      then show ?case 
        by (simp add: A1)
    next
      case (Cons p ps)
      then have \<open>A \<turnstile> \<^bold>\<Or> ps \<^bold>\<longrightarrow> q\<close>
        by simp
      moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close> 
        using Cons by simp
      moreover have \<open>A \<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (\<^bold>\<Or> ps \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<or> (\<^bold>\<Or> ps) \<^bold>\<longrightarrow> q\<close>
        using A1 by force
      ultimately have \<open>A \<turnstile> p \<^bold>\<or> (\<^bold>\<Or> ps) \<^bold>\<longrightarrow> q\<close> 
        using R1 by blast
      then show ?case 
        by simp
    qed
    have \<open>i \<in> set g \<Longrightarrow> \<forall> \<phi>\<^sub>w \<in> set (map conjunct \<w>). A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> K i (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close> for i
      using e by simp
    then have \<open>\<forall> \<phi>\<^sub>w \<in> set (map conjunct \<w>). A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> unfold_Ev g (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close> 
    proof (induct g)
      case Nil
      then show ?case 
        by (metis conE2 con_imp_antecedents empty_fold)
    next
      case (Cons i g)
      show ?case 
      proof
        fix \<phi>\<^sub>w 
        assume \<open>\<phi>\<^sub>w\<in>set (map conjunct \<w>)\<close>
        then have \<open>A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> unfold_Ev g (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>
          using Cons by auto
        moreover have \<open>A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> K i (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>
          using Cons.prems \<open>\<phi>\<^sub>w \<in> set (map conjunct \<w>)\<close> by auto
        ultimately  show \<open>A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> unfold_Ev (i # g) (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>  
          by (simp add: con_imp2)
      qed
    qed
    then have \<open>\<forall> \<phi>\<^sub>w \<in> set (map conjunct \<w>). A \<turnstile> \<phi>\<^sub>w \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close> 
      using C1b imp_chain by blast
    then show ?thesis
      using assms(4) * by simp
  qed
qed


lemma truth_lemma_K: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prems: \<open>V \<in> mcss A \<phi>\<close> \<open>K i p \<in> sub_C' \<phi>\<close>
  assumes hyp: \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
  shows \<open>K i p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> K i p\<close>
proof-
  from \<open>K i p \<in> sub_C' \<phi>\<close> have \<open>K i p \<in> sub_C \<phi>\<close>
    by (simp add: image_iff)
  hence \<open>p \<in> sub_C \<phi>\<close>
    by (metis insertI2 p_in_sub_C_p sub_C.simps(6) sub_C_transitive)
  hence \<open>p \<in> sub_C' \<phi>\<close>
    by simp
  show ?thesis
  proof (safe)
    assume \<open>K i p \<in> V\<close>
    then have \<open>W \<in> reach A i V \<Longrightarrow> W \<in> mcss A \<phi> \<Longrightarrow> canonical A \<phi>, W \<Turnstile> p\<close> for W
      using hyp by auto
    then show \<open>canonical A \<phi>, V \<Turnstile> K i p\<close> 
      by simp
  next 
    assume \<open>canonical A \<phi>, V \<Turnstile> K i p\<close> 
    then show \<open>K i p \<in> V\<close>
      using truth_lemma_Ka prems hyp by blast
  qed
qed

lemma truth_lemma_Ev: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prems: \<open>V \<in> mcss A \<phi>\<close> \<open>Ev g p \<in> sub_C' \<phi>\<close>
  assumes hyp: \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
  shows \<open>Ev g p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> Ev g p\<close>
proof-
  from \<open>Ev g p \<in> sub_C' \<phi> \<close> have \<open>Ev g p \<in> sub_C \<phi>\<close>
    by (simp add: image_iff)
  then have \<open>\<forall> i \<in> set g. K i p \<in> sub_C \<phi>\<close>
    by (induct \<phi>) auto
  then have \<open>\<forall> i \<in> set g. K i p \<in> sub_C' \<phi>\<close>
    by simp
  then have \<open>(Ev g p \<in> V) = (\<forall> i \<in> set g. K i p \<in> V)\<close> 
  proof (safe)
    fix i
    assume \<open>Ev g p \<in> V\<close> \<open>i \<in> set g\<close>
    moreover have \<open>A \<turnstile> Ev g p \<^bold>\<longrightarrow> K i p\<close>
      using \<open>i \<in> set g\<close> by (simp add: Ev_implies_K)
    ultimately show \<open>K i p \<in> V\<close>
      using \<open>\<forall> i \<in> set g. K i p \<in> sub_C' \<phi>\<close> consistent_consequent maximal'_def prems(1) by blast
  next
    assume \<open>\<forall> i \<in> set g. K i p \<in> V\<close>
    then have *: \<open>set (map (\<lambda> i. K i p) g) \<subseteq> V\<close>
      by (simp add: image_subset_iff)
    have \<open>A \<turnstile> map (\<lambda> i. K i p) g \<^bold>\<leadsto> unfold_Ev g p\<close>
    proof (induct g)
      case Nil
      then show ?case 
        by (metis conjunct.simps(1) empty_fold imply_implies_itself list.simps(8))
    next
      case (Cons i g)
      then have \<open>A \<turnstile> map (\<lambda>i. K i p) (i # g) \<^bold>\<leadsto> unfold_Ev g p\<close>
        using K_imply_Cons by auto
      moreover have \<open>A \<turnstile> map (\<lambda>i. K i p) (i # g) \<^bold>\<leadsto> K i p\<close>
        using K_imply_head by auto
      ultimately have \<open>A \<turnstile> map (\<lambda>i. K i p) (i # g) \<^bold>\<leadsto> (K i p \<^bold>\<and> unfold_Ev (g) p)\<close>
        using K_implies_combine by fast
      then show ?case
        by simp
    qed
    then have \<open>A \<turnstile> map (\<lambda> i. K i p) g \<^bold>\<leadsto> Ev g p\<close> 
      by (metis C1b K_imply_head K_right_mp R1 imply.simps(2))
    then show \<open>Ev g p \<in> V\<close> 
      using consequent_in_maximal' \<open>\<forall> i \<in> set g. K i p \<in> sub_C' \<phi>\<close> prems * by blast
  qed
  moreover have \<open>(\<forall> i \<in> set g. (K i p \<in> V) = (canonical A \<phi>, V \<Turnstile> K i p))\<close> 
  proof
    fix i
    assume \<open>i \<in> set g\<close>
    then show \<open>(K i p \<in> V) = (canonical A \<phi>, V \<Turnstile> K i p)\<close> 
      using truth_lemma_K \<open>\<forall>i\<in>set g. K i p \<in> sub_C' \<phi>\<close> hyp prems(1) by blast
  qed
  moreover have \<open>(\<forall> i \<in> set g. canonical A \<phi>, V \<Turnstile> K i p) = (canonical A \<phi>, V \<Turnstile> Ev g p)\<close> 
    by simp
  ultimately show ?thesis 
    by simp
qed


lemma truth_lemma:
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes \<open>p \<in> sub_C' \<phi>\<close> and \<open>V \<in> mcss A \<phi>\<close>
  shows \<open>p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
  using assms
proof (induct p arbitrary: V)
  case FF
  have \<open>V \<subseteq> sub_C' \<phi>\<close> \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close>
    using \<open>V \<in> mcss A \<phi>\<close> by simp_all
  show ?case
  proof safe
    assume \<open>\<^bold>\<bottom> \<in> V\<close>
    then have False
      using \<open>consistent A V\<close> K_imply_head unfolding consistent_def 
      by (metis bot.extremum insert_subset list.set(1) list.simps(15))
    then show \<open>canonical A \<phi>, V \<Turnstile> \<^bold>\<bottom>\<close> ..
  next
    assume \<open>canonical A \<phi>, V \<Turnstile> \<^bold>\<bottom>\<close>
    then show \<open>\<^bold>\<bottom> \<in> V\<close>
      by simp
  qed
next
  case (Pro x)
  then show ?case
    by simp
next
  case (Dis p q)
  have \<open>V \<subseteq> sub_C' \<phi>\<close> \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close>
    using \<open>V \<in> mcss A \<phi>\<close> by simp_all
  from Dis have \<open>p \<^bold>\<or> q \<in> sub_C \<phi>\<close> 
    by auto
  moreover have \<open>p \<in> sub_C (p \<^bold>\<or> q) \<and> q \<in> sub_C (p \<^bold>\<or> q)\<close> 
    by (simp add: p_in_sub_C_p)
  ultimately have \<open>p \<in> sub_C \<phi> \<and> q \<in> sub_C \<phi>\<close>
    using sub_C_transitive by blast
  then have p_q_in_phi: \<open>p \<in> sub_C' \<phi> \<and> q \<in> sub_C' \<phi>\<close>
    by simp
  from Dis show ?case
  proof safe
    assume \<open>p \<^bold>\<or> q \<in> V\<close>
    then have p_or_q_cons: \<open>consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_disjuncts by blast
    have \<open>p \<in> V \<or> q \<in> V\<close>
    proof (rule ccontr)
      assume \<open>\<not> (p \<in> V \<or> q \<in> V)\<close>
      from \<open>\<not> (p \<in> V \<or> q \<in> V)\<close> p_q_in_phi have \<open>\<not>(consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V))\<close>
        using \<open>maximal' A \<phi> V\<close> unfolding maximal'_def by meson
      then show False
        using p_or_q_cons ..
    qed
    then have \<open>p \<in> sub_C' \<phi> \<or> q \<in> sub_C' \<phi>\<close> 
      using Dis.prems by blast
    then show \<open>canonical A \<phi>, V \<Turnstile> (p \<^bold>\<or> q)\<close> 
      using Dis by (smt (verit, best) \<open>p \<in> V \<or> q \<in> V\<close> p_q_in_phi semantics.simps(3))
  next
    assume a: \<open>canonical A \<phi>, V \<Turnstile> (p \<^bold>\<or> q)\<close> 
    consider \<open>canonical A \<phi>, V \<Turnstile> p\<close> | \<open>canonical A \<phi>, V \<Turnstile> q\<close>
      using a by auto
    then have \<open>p \<in> V \<or> q \<in> V\<close>
      using p_q_in_phi Dis by meson
    moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close> \<open>A \<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close>
      by (auto simp: A1)
    ultimately show \<open>(p \<^bold>\<or> q) \<in> V\<close>
      using Dis.prems consistent_consequent maximal'_def by fast
  qed
next
  case (Con p q)
  have \<open>V \<subseteq> sub_C' \<phi>\<close> \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close>
    using \<open>V \<in> mcss A \<phi>\<close> by simp_all
  from Con have \<open>p \<^bold>\<and> q \<in> sub_C \<phi>\<close> 
    by auto
  moreover have \<open>p \<in> sub_C (p \<^bold>\<and> q) \<and> q \<in> sub_C (p \<^bold>\<and> q)\<close> 
    by (simp add: p_in_sub_C_p)
  ultimately have \<open>p \<in> sub_C \<phi> \<and> q \<in> sub_C \<phi>\<close>
    using sub_C_transitive by blast
  then have p_q_in_phi: \<open>p \<in> sub_C' \<phi> \<and> q \<in> sub_C' \<phi>\<close>
    by simp
  from Con show ?case
  proof safe
    assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V)\<close> \<open>consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using p_q_in_phi \<open>maximal' A \<phi> V\<close> unfolding maximal'_def by fast+
    then show \<open>canonical A \<phi>, V \<Turnstile> (p \<^bold>\<and> q)\<close>
      using Con p_q_in_phi by fastforce
  next
    assume \<open>canonical A  \<phi>, V \<Turnstile> (p \<^bold>\<and> q)\<close>
    then have \<open>canonical A \<phi>, V \<Turnstile> p\<close> \<open>canonical A \<phi>, V \<Turnstile> q\<close>
      by auto
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using Con p_q_in_phi by blast+
    then have \<open>set [p, q] \<subseteq> V\<close> 
      by simp
    moreover have \<open>A \<turnstile> [p, q] \<^bold>\<leadsto> p \<^bold>\<and> q\<close>
      by (auto simp: A1)
    moreover have \<open>set [p, q] \<subseteq> sub_C' \<phi>\<close>
      using \<open>p \<in> sub_C \<phi> \<and> q \<in> sub_C \<phi>\<close> by auto
    ultimately show \<open>(p \<^bold>\<and> q) \<in> V\<close>
      using Con.prems consequent_in_maximal' by blast
  qed
next
  case (Imp p q)
  have \<open>V \<subseteq> sub_C' \<phi>\<close> \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close>
    using \<open>V \<in> mcss A \<phi>\<close> by simp_all
  from Imp have \<open>p \<^bold>\<longrightarrow> q \<in> sub_C \<phi> \<or> q = \<^bold>\<bottom>\<close> 
    by auto
  moreover have \<open>p \<in> sub_C (p \<^bold>\<longrightarrow> q) \<and> q \<in> sub_C (p \<^bold>\<longrightarrow> q)\<close> 
    by (simp add: p_in_sub_C_p)
  ultimately have \<open>p \<in> sub_C \<phi> \<and> (q \<in> sub_C \<phi> \<or> q = \<^bold>\<bottom>)\<close>
    using sub_C_transitive Imp.prems(1) by blast
  then have p_q_in_phi: \<open>p \<in> sub_C' \<phi> \<and> (q \<in> sub_C' \<phi> \<or> q = \<^bold>\<bottom>)\<close>
    by auto
  show ?case
  proof (rule iffI)
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
    from p_q_in_phi have \<open>p \<in> V \<or> \<^bold>\<not>p \<in> V\<close>
      using \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> p_q_in_phi
      by (metis UnI2 \<open>p \<in> sub_C \<phi> \<and> (q \<in> sub_C \<phi> \<or> q = \<^bold>\<bottom>)\<close> consistent_extend_by_p maximal'_def rev_image_eqI)
    then consider \<open>p \<in> V\<close> | \<open>\<^bold>\<not>p \<in> V\<close> 
      by fast
    then show \<open>canonical A \<phi>, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    proof cases
      case 1
      then have \<open>q \<in> V \<or> \<^bold>\<not>q \<in> V \<or> q = \<^bold>\<bottom>\<close> 
        using \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> p_q_in_phi 
        by (metis UnI2 \<open>p \<in> sub_C \<phi> \<and> (q \<in> sub_C \<phi> \<or> q = \<^bold>\<bottom>)\<close> consistent_extend_by_p maximal'_def rev_image_eqI)
      then consider (a)\<open>q \<in> V\<close> | (b)\<open>\<^bold>\<not>q \<in> V \<or> q = \<^bold>\<bottom>\<close>
        by fast
      then show ?thesis 
      proof cases
        case a
        then show ?thesis
          using Imp p_q_in_phi by blast
      next
        case b
        then consider (x)\<open>\<^bold>\<not> q \<in> V\<close> | (y)\<open>q = \<^bold>\<bottom>\<close>
          by auto
        then have \<open>\<not> consistent A V\<close>
        proof cases
          case x
          moreover have \<open>A \<turnstile> [p,p \<^bold>\<longrightarrow> q,\<^bold>\<not>q] \<^bold>\<leadsto> \<^bold>\<bottom>\<close> 
            using A1 by force
          ultimately show ?thesis 
            using 1 \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> unfolding consistent_def
            by (metis Un_Diff_cancel empty_set insert_Diff insert_is_Un insert_subsetI le_iff_sup list.simps(15))
        next
          case y
          then have \<open>A \<turnstile> [p,p \<^bold>\<longrightarrow> q] \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
            using A1 by force
          then show ?thesis 
            using 1 \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> unfolding consistent_def 
            by (metis bot.extremum empty_set insert_subsetI list.simps(15))
        qed
        then show ?thesis 
          by (simp add: \<open>consistent A V\<close>)
      qed
    next
      case 2
      then have \<open>p \<notin> V\<close> 
        using Imp.prems exactly_one_in_maximal' p_q_in_phi comp.simps(1)
        by (smt (verit, del_insts) mem_Collect_eq subset_iff)
      then show ?thesis 
        using Imp p_q_in_phi by blast
    qed
  next
    assume \<open>canonical A \<phi>, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    then consider \<open>\<not> canonical A \<phi>, V \<Turnstile> p\<close> | \<open>canonical A \<phi>, V \<Turnstile> q\<close>
      by auto
    then have \<open>p \<notin> V \<or> q \<in> V\<close>
      using Imp by (metis (mono_tags, lifting) p_q_in_phi semantics.simps(1))
    moreover have \<open>p \<in> sub_C' \<phi>\<close> 
      using p_q_in_phi by auto
    ultimately have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close>
      using \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>p \<in> sub_C \<phi> \<and> (q \<in> sub_C \<phi> \<or> q = \<^bold>\<bottom>)\<close> consistent_extend_by_p imageI maximal'_def 
      by (smt (verit) Un_iff)
    moreover have \<open>A \<turnstile> \<^bold>\<not> p \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close> \<open>A \<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
      by (auto simp: A1)             
    ultimately show \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
      using Imp.prems consistent_consequent maximal'_def by fast
  qed
next
  case (K i p)
  have \<open>K i p \<in> sub_C \<phi>\<close>
    using K.prems(1) Un_iff fm.distinct(53) image_iff by auto
  then have \<open>p \<in> sub_C' \<phi>\<close> 
    by (metis UnI1 insertI2 p_in_sub_C_p sub_C.simps(6) sub_C_transitive)
  then have \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
    using K.hyps by blast
  moreover have \<open>V \<in> mcss A \<phi>\<close> 
    using K by simp
  ultimately show ?case 
    using truth_lemma_K \<open>K i p \<in> sub_C' \<phi>\<close> by blast
next
  case (Ev g p)
  have \<open>p \<in> sub_C' \<phi>\<close> 
    using \<open>Ev g p \<in> sub_C' \<phi>\<close> p_in_sub_C_p sub_C.simps(7) sub_C_transitive 
    by (smt (verit, ccfv_threshold) Un_iff Un_insert_right fm.distinct(47) image_iff sup_commute)
  then have \<open>\<And> V. V \<in> mcss A \<phi> \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A \<phi>, V \<Turnstile> p\<close>
    using Ev.hyps by blast
  moreover have \<open>V \<in> mcss A \<phi>\<close>
    using Ev by simp
  ultimately show ?case 
    using truth_lemma_Ev \<open>Ev g p \<in> sub_C' \<phi>\<close> by blast
next
  case (Co g p) 
  from \<open>Co g p \<in> sub_C' \<phi>\<close> have \<open>Co g p \<in> sub_C \<phi>\<close> 
    by (simp add: image_iff)
  then have \<open>p \<in> sub_C \<phi>\<close>
  proof (induct \<phi>)
    case (Co g \<phi>)
    then show ?case
      using p_in_sub_C_p by fastforce
  qed auto 
  then have \<open>p \<in> sub_C' \<phi>\<close> 
    by simp
  have \<open>Co g p \<in> sub_C \<phi>\<close> 
    using Co.prems(1) by auto
  then have \<open>Ev g (p \<^bold>\<and> Co g p) \<in> sub_C \<phi>\<close> \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> sub_C \<phi>\<close>
    by (induct \<phi>) auto
  then have \<open>Ev g (p \<^bold>\<and> Co g p) \<in> sub_C' \<phi>\<close> \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> sub_C' \<phi>\<close>
    by simp_all
  show ?case 
  proof safe
    assume \<open>Co g p \<in> V\<close>
    moreover have \<open>\<And> W. n \<ge> 1 \<Longrightarrow> W \<in> mcss A \<phi> \<Longrightarrow> Co g p \<in> W \<Longrightarrow> canonical A \<phi>, W \<Turnstile> Ev_n g p n\<close> for n
    proof (induct n rule: less_induct)
      case (less n)
      moreover have \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> Co g p)\<close> 
        by (simp add: C2)
      ultimately have \<open>Ev g (p \<^bold>\<and> Co g p) \<in> W\<close>
        using Co.prems consistent_consequent maximal'_def \<open>Ev g (p \<^bold>\<and> Co g p) \<in> sub_C' \<phi>\<close> by blast
      then have \<open>set [Ev g (p \<^bold>\<and> Co g p)] \<subseteq> W\<close>
        by simp
      moreover have \<open>set [Ev g (p \<^bold>\<and> Co g p)] \<subseteq> sub_C' \<phi>\<close>
        using \<open>Ev g (p \<^bold>\<and> Co g p) \<in> sub_C' \<phi>\<close> by auto
      moreover have \<open>\<forall> i \<in> set g. A \<turnstile> [Ev g (p \<^bold>\<and> Co g p)] \<^bold>\<leadsto> K i (p \<^bold>\<and> Co g p)\<close>
        by (simp add: Ev_implies_K)
      moreover have \<open>maximal' A \<phi> W\<close> \<open>consistent A W\<close>
        using \<open>W \<in> mcss A \<phi>\<close> by simp_all
      ultimately have \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> W\<close>
        using \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> sub_C' \<phi>\<close> consequent_in_maximal' by blast 
      consider \<open>n = 1\<close> | \<open>n > 1\<close>
        using less by linarith
      then show ?case 
      proof cases
        case 1
        have \<open>i \<in> set g \<Longrightarrow> W' \<in> reach A i W \<Longrightarrow> W' \<in> mcss A \<phi> \<Longrightarrow> canonical A \<phi>, W' \<Turnstile> p\<close> for i W'
        proof-
          assume \<open>i \<in> set g\<close> \<open>W' \<in> reach A i W\<close> \<open>W' \<in> mcss A \<phi>\<close>
          have \<open>K i (p \<^bold>\<and> Co g p) \<in> W\<close> 
            using \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> W\<close> \<open>i \<in> set g\<close>  by simp
          then have \<open>p \<^bold>\<and> Co g p \<in> W'\<close> 
            using \<open>W' \<in> reach A i W\<close> by auto
          moreover have \<open>A \<turnstile> p \<^bold>\<and> Co g p \<^bold>\<longrightarrow> p\<close>
            by (simp add: conE1)
          ultimately have \<open>p \<in> W'\<close> 
            using \<open>p \<in> sub_C' \<phi>\<close> \<open>W' \<in> mcss A \<phi>\<close> consistent_consequent maximal'_def by blast
          moreover have \<open>consistent A W'\<close> \<open>maximal' A \<phi> W'\<close> \<open>W' \<subseteq> sub_C' \<phi>\<close>
            using \<open>W' \<in> mcss A \<phi>\<close> by simp_all
          ultimately show ?thesis 
            using Co.hyps by blast
        qed
        then show ?thesis 
          using 1 by simp
      next
        case 2
        then have *: \<open>\<And> W'. W' \<in> mcss A \<phi> \<Longrightarrow> Co g p \<in> W' \<Longrightarrow> canonical A \<phi>, W' \<Turnstile> Ev_n g p (n - 1)\<close>
          using less by simp
        then have \<open>i \<in> set g \<Longrightarrow> W' \<in> reach A i W \<Longrightarrow> W' \<in> mcss A \<phi> \<Longrightarrow> canonical A \<phi>, W' \<Turnstile> Ev_n g p (n - 1)\<close> for i W' 
        proof-
          assume \<open>i \<in> set g\<close> \<open>W' \<in> reach A i W\<close> \<open>W' \<in> mcss A \<phi>\<close>
          have \<open>K i (p \<^bold>\<and> Co g p) \<in> W\<close> 
            using \<open>\<forall> i \<in> set g. K i (p \<^bold>\<and> Co g p) \<in> W\<close> \<open>i \<in> set g\<close>  by simp
          then have \<open>p \<^bold>\<and> Co g p \<in> W'\<close> 
            using \<open>W' \<in> reach A i W\<close> by auto
          moreover have \<open>A \<turnstile> p \<^bold>\<and> Co g p \<^bold>\<longrightarrow> Co g p\<close>
            by (simp add: conE2)
          ultimately have \<open>Co g p \<in> W'\<close> 
            using \<open>Co g p \<in> sub_C' \<phi>\<close> \<open>W' \<in> mcss A \<phi>\<close> consistent_consequent maximal'_def by blast
          then show ?thesis 
            using  \<open>W' \<in> mcss A \<phi>\<close> * by simp
        qed
        moreover have \<open>Ev_n g p n = Ev g (Ev_n g p (n - 1))\<close> 
          by (metis Ev_n.simps(2) Suc_diff_le diff_Suc_1 less.prems(1))
        ultimately show ?thesis 
          by simp
      qed
    qed
    ultimately show \<open>canonical A \<phi>, V \<Turnstile> Co g p\<close>
      using Co.prems(2) by auto
  next
    have \<open>finite (mcss A \<phi>)\<close> 
      using finite_Collect_subsets sub_C'_finite by fastforce
    then have \<open>finite {W. W \<in> mcss A \<phi> \<and> canonical A \<phi>, W \<Turnstile> Co g p}\<close> 
      by (simp add: Collect_mono_iff rev_finite_subset)
    moreover have \<open>\<forall> W \<in> {W. W \<in> mcss A \<phi> \<and> canonical A \<phi>, W \<Turnstile> Co g p}. finite W\<close>
      by (smt (verit, del_insts) mem_Collect_eq rev_finite_subset sub_C'_finite) 
    ultimately obtain \<w> where \<w>_def:
      \<open>set (map set \<w>) = {W. W \<in> mcss A \<phi> \<and> canonical A \<phi>, W \<Turnstile> Co g p}\<close> 
      using list_of_lists_if_finite_set_of_sets by meson
    moreover obtain \<phi>\<^sub>\<w> where \<phi>\<^sub>\<w>_def:
      \<open>\<phi>\<^sub>\<w> = disjunct (map conjunct \<w>)\<close>
      by simp
    moreover have \<open>\<And>V. V \<in> mcss A \<phi> \<Longrightarrow> (p \<in> V) = (\<lparr>\<W> = mcss A \<phi>, \<K> = \<lambda>i V. {W. known V i \<subseteq> W}, \<pi> = pi\<rparr>, V \<Turnstile> p)\<close>
      using Co.hyps \<open>p \<in> sub_C' \<phi>\<close> by blast
    moreover have \<open>Co g p \<in> sub_C' \<phi>\<close> 
      using Co.prems(1) by auto
    moreover have \<open>V \<in> mcss A \<phi>\<close> 
      using Co.prems(2) by auto
    ultimately have \<open>A \<turnstile> \<phi>\<^sub>\<w> \<^bold>\<longrightarrow> Ev g (p \<^bold>\<and> \<phi>\<^sub>\<w>)\<close>
      using Co_lemma[where g = g and p = p and \<phi> = \<phi> and \<w> = \<w> and \<phi>\<^sub>\<w> = \<phi>\<^sub>\<w> and V = V and A = A] by blast
    then have *:\<open>A \<turnstile> \<phi>\<^sub>\<w> \<^bold>\<longrightarrow> Co g p\<close>
      by (simp add: RC1)

    from Co have \<open>V \<in> mcss A \<phi>\<close> 
      by blast
    moreover assume \<open>canonical A \<phi>, V \<Turnstile> Co g p\<close>
    ultimately have \<open>V \<in> {W. W \<in> mcss A \<phi> \<and> canonical A \<phi>, W \<Turnstile> Co g p}\<close> 
      by simp
    then have \<open>\<exists> \<v>. set \<v> = V \<and> \<v> \<in> set \<w>\<close>
      using \<w>_def by (metis (no_types, lifting) image_iff list.set_map)
    then obtain \<v> where \<v>_def: \<open>set \<v> = V \<and> \<v> \<in> set \<w>\<close> ..
    then obtain \<phi>\<^sub>\<v> where \<phi>\<^sub>\<v>_def: \<open>\<phi>\<^sub>\<v> = \<^bold>\<And>\<v>\<close> 
      by simp
    have \<open>A \<turnstile> \<phi>\<^sub>\<v> \<^bold>\<longrightarrow> \<phi>\<^sub>\<w>\<close> 
      using \<v>_def \<phi>\<^sub>\<v>_def \<phi>\<^sub>\<w>_def elem_implies_disjunct by (metis imageI image_set)
    then have \<open>A \<turnstile> \<phi>\<^sub>\<v> \<^bold>\<longrightarrow> Co g p\<close>
      using * imp_chain by auto
    then have **:\<open>A \<turnstile> \<^bold>\<not>Co g p \<^bold>\<longrightarrow> \<^bold>\<not>\<phi>\<^sub>\<v>\<close> 
      using K_trans R1 by blast
    show \<open>Co g p \<in> V\<close> 
    proof (rule ccontr)
      assume \<open>Co g p \<notin> V\<close>
      then have \<open>\<^bold>\<not>Co g p \<in> V\<close>
        using Co.prems comp.simps(15) exactly_one_in_maximal' 
        by (smt (verit, best) mem_Collect_eq)
      then have \<open>A; V \<turnstile> \<^bold>\<not>Co g p\<close>
        by (metis K_imply_head \<v>_def extract_from_list subset_refl)
      from this ** have \<open>A; V \<turnstile> \<^bold>\<not>\<phi>\<^sub>\<v>\<close>
        by (metis K_ImpI K_mp \<open>\<^bold>\<not> Co g p \<in> V\<close> imp_chain imply.simps(2) insert_subsetI list.simps(15))
      moreover have \<open>A; V \<turnstile> \<phi>\<^sub>\<v>\<close> 
        using imply_implies_itself \<v>_def \<phi>\<^sub>\<v>_def by auto
      ultimately have \<open>A; V \<turnstile> \<^bold>\<bottom>\<close> 
        by (metis K_imply_weaken K_right_mp \<v>_def order_refl)
      then show False
        using Co consistent_def by blast
      qed
  qed
qed

lemma canonical_model:
  fixes \<phi> :: \<open>('i :: countable) fm\<close>
  assumes \<open>consistent A S\<close> and \<open>p \<in> S\<close> and \<open>S \<subseteq> sub_C' \<phi>\<close>
  defines \<open>V \<equiv> Extend' A \<phi> S from_nat\<close> and \<open>M \<equiv> canonical A \<phi>\<close>
  shows \<open>M, V \<Turnstile> p\<close> and \<open>consistent A V\<close> and \<open>maximal' A \<phi> V\<close>
proof -
  have \<open>consistent A V\<close>
    using \<open>consistent A S\<close> unfolding V_def using consistent_Extend' by blast
  have \<open>maximal' A \<phi> V\<close>
    unfolding V_def using maximal_Extend' surj_from_nat by blast
  { fix x :: \<open>('i :: countable) fm\<close>
    assume \<open>x \<in> S\<close> \<open>x \<in> sub_C' \<phi>\<close>
    then have \<open>x \<in> V\<close>
      unfolding V_def using Extend'_subset by blast
    moreover have \<open>V \<subseteq> sub_C' \<phi>\<close> 
      unfolding V_def using \<open>S \<subseteq> sub_C' \<phi>\<close> by (simp add: Extend'_subset_sub_C)
    ultimately have \<open>M, V \<Turnstile> x\<close>
      unfolding M_def using truth_lemma \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>x \<in> sub_C' \<phi>\<close> by blast }
  then show \<open>M, V \<Turnstile> p\<close>
    using \<open>p \<in> S\<close> \<open>S \<subseteq> sub_C' \<phi>\<close> by blast+
  show \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close>
    by fact+
qed

subsection \<open>Completeness\<close>

abbreviation valid :: \<open>(('i :: countable, 'i fm set) kripke \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  (\<open>_; _ \<TTurnstile> _\<close> [50, 50, 50] 50)
  where \<open>P; G \<TTurnstile> p \<equiv> P; G \<TTurnstile>\<star> p\<close>

abbreviation P_canonical where
  \<open>P_canonical P A qs p \<equiv> P (canonical A ((\<^bold>\<not> p) # qs \<^bold>\<leadsto> \<^bold>\<bottom>))\<close>

theorem strong_completeness:
  assumes \<open>finite G\<close> and \<open>P; G \<TTurnstile> (p :: ('i :: countable) fm)\<close> and 
    \<open>\<forall> qs. set qs = G \<longrightarrow> P_canonical P A qs p\<close>
  shows \<open>A; G \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>qs. set qs \<subseteq> G \<and> (A \<turnstile> qs \<^bold>\<leadsto> p)\<close>
  then have *: \<open>\<forall>qs. set qs \<subseteq> G \<longrightarrow> \<not> (A \<turnstile> (\<^bold>\<not> p) # qs \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using K_Boole by blast

  obtain qs where \<open>set qs = G\<close>
    using assms(1) finite_list by auto
  let ?\<phi> = \<open>(\<^bold>\<not> p) # qs \<^bold>\<leadsto> \<^bold>\<bottom>\<close> 
  let ?S = \<open>set (\<^bold>\<not>p # qs)\<close>
  let ?V = \<open>Extend' A ?\<phi> ?S from_nat\<close>
  let ?M = \<open>canonical A ?\<phi>\<close>

  have  \<open>set (xs :: 'i fm list) \<subseteq> sub_C (xs \<^bold>\<leadsto> \<^bold>\<bottom>)\<close> for xs 
  proof (induct xs)
    case (Cons a xs)
    then show ?case 
      using Un_insert_right insert_subsetI list.simps(15) p_in_sub_C_p sub_C.simps(5) verit_comp_simplify1(2) by fastforce
  qed auto
  then have 1:\<open>?S \<subseteq> sub_C' ?\<phi>\<close> 
    by (meson sup.coboundedI1)
  moreover have \<open>consistent A ?S\<close>
    using * \<open>set qs = G\<close> consistent_def K_imply_weaken by blast
  ultimately have \<open>\<forall>q \<in> set (\<^bold>\<not>p # qs). ?M, ?V \<Turnstile> q\<close>
    using canonical_model by blast
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> set qs. ?M, ?V \<Turnstile> q\<close>
    by auto
  moreover have \<open>?V \<in> mcss A ?\<phi>\<close>
    using \<open>consistent A ?S\<close> consistent_Extend' maximal_Extend' surj_from_nat Extend'_subset_sub_C mem_Collect_eq 1 
    by (smt (verit))
  ultimately have \<open>?M, ?V \<Turnstile> p\<close> 
    using \<open>set qs = G\<close> assms(2) assms(3) frame.select_convs(1) by auto
  then show False 
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

corollary completeness:
  assumes \<open>P; {} \<TTurnstile> p\<close> and \<open>P_canonical P A [] p\<close>
  shows \<open>A \<turnstile> p\<close>
proof-
  have \<open>A; {} \<turnstile> p\<close>
    using assms strong_completeness[where G=\<open>{}\<close>] by blast
  then show \<open>A \<turnstile> p\<close> 
    by simp
qed

corollary completeness\<^sub>A:
  assumes \<open>(\<lambda>_. True); {} \<TTurnstile> p\<close>
  shows \<open>A \<turnstile> p\<close>
  using assms completeness by blast

section \<open>System K\<close>

abbreviation SystemK (\<open>_ \<turnstile>\<^sub>K _\<close> [50] 50) where
  \<open>G \<turnstile>\<^sub>K p \<equiv> (\<lambda>_. False); G \<turnstile> p\<close>

lemma strong_soundness\<^sub>K: \<open>G \<turnstile>\<^sub>K p \<Longrightarrow> P; G \<TTurnstile>\<star> p\<close>
  using strong_soundness[of \<open>\<lambda>_. False\<close> \<open>\<lambda>_. True\<close>] by fast

abbreviation validK (\<open>_ \<TTurnstile>\<^sub>K _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>K p \<equiv> (\<lambda>_. True); G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>K: \<open>G \<TTurnstile>\<^sub>K p \<Longrightarrow> G \<turnstile>\<^sub>K p\<close> if \<open>finite G\<close>
  using strong_completeness[of G \<open>\<lambda>_. True\<close>] that by auto

theorem main\<^sub>K: \<open>G \<TTurnstile>\<^sub>K p \<longleftrightarrow> G \<turnstile>\<^sub>K p\<close> if \<open>finite G\<close>
  using strong_soundness\<^sub>K[of G p] strong_completeness\<^sub>K[of G p] that by fast

corollary \<open>G \<TTurnstile>\<^sub>K p \<Longrightarrow> (\<lambda>_. True); G \<TTurnstile>\<star> p\<close> if \<open>finite G\<close>
  using strong_soundness\<^sub>K[of G p] strong_completeness\<^sub>K[of G p] that by fast

section \<open>System T\<close>

text \<open>Also known as System M\<close>

inductive AxT :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxT (K i p \<^bold>\<longrightarrow> p)\<close>

abbreviation SystemT (\<open>_ \<turnstile>\<^sub>T _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>T p \<equiv> AxT; G \<turnstile> p\<close>

lemma soundness_AxT: \<open>AxT p \<Longrightarrow> reflexive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: AxT.induct) (meson truth)

lemma strong_soundness\<^sub>T: \<open>G \<turnstile>\<^sub>T p \<Longrightarrow> reflexive; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_AxT .
lemma AxT_reflexive:
  assumes \<open>AxT \<le> A\<close> and \<open>consistent A V\<close> and \<open>maximal' A \<phi> V\<close> and \<open>V \<subseteq> sub_C' \<phi>\<close>
  shows \<open>V \<in> reach A i V\<close>
proof (safe)
  fix p
  assume \<open>K i p \<in> V\<close>
  moreover have \<open>p \<in> sub_C (K i p)\<close> 
    by (simp add: p_in_sub_C_p)
  ultimately have \<open>p \<in> sub_C' \<phi>\<close> 
    using \<open>V \<subseteq> sub_C' \<phi>\<close>  
    by (smt (verit, del_insts) Un_iff fm.distinct(45) image_iff in_mono sub_C_transitive) 
  moreover have \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> p\<close>
    by (metis Ax AxT.simps assms(1) rev_predicate1D)
  ultimately show \<open>p \<in> V\<close> 
    using \<open>maximal' A \<phi> V\<close> \<open>K i p \<in> V\<close> assms(2) consistent_consequent maximal'_def by blast
qed

lemma reflexive\<^sub>T:
  assumes \<open>AxT \<le> A\<close>
  shows \<open>\<forall> (\<phi> :: ('i :: countable) fm). reflexive (canonical A \<phi>)\<close>
  unfolding reflexive_def
proof safe
  fix i V \<phi>
  assume \<open>V \<in> \<W> (canonical A \<phi>)\<close>
  then have \<open>consistent A V\<close> \<open>maximal' A \<phi> V\<close> \<open>V \<subseteq> sub_C' \<phi>\<close>
    by simp_all
  with AxT_reflexive assms have \<open>V \<in> reach A i V\<close> .
  then show \<open>V \<in> \<K> (canonical A \<phi>) i V\<close>
    by simp
qed

abbreviation validT (\<open>_ \<TTurnstile>\<^sub>T _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>T p \<equiv> reflexive; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>T: \<open>G \<TTurnstile>\<^sub>T p \<Longrightarrow> G \<turnstile>\<^sub>T p\<close> if \<open>finite G\<close>
proof-
  have \<open>\<forall>(\<phi> :: ('i :: countable) fm). reflexive (canonical AxT \<phi>)\<close> 
    using reflexive\<^sub>T by auto
  then have \<open>\<forall> qs. set qs \<subseteq> G \<longrightarrow> P_canonical reflexive AxT qs p\<close> 
    by fast
  moreover assume \<open>G \<TTurnstile>\<^sub>T p\<close>
  ultimately show ?thesis
    using strong_completeness \<open>finite G\<close> by blast
qed

theorem main\<^sub>T: \<open>G \<TTurnstile>\<^sub>T p \<longleftrightarrow> G \<turnstile>\<^sub>T p\<close> if \<open>finite G\<close>
  using strong_soundness\<^sub>T[of G p] strong_completeness\<^sub>T[of G p] that by fast

corollary \<open>G \<TTurnstile>\<^sub>T p \<longrightarrow> reflexive; G \<TTurnstile>\<star> p\<close> if \<open>finite G\<close>
  using strong_soundness\<^sub>T[of G p] strong_completeness\<^sub>T[of G p] that by fast

section \<open>Acknowledgements\<close>

text \<open>
The formalization is inspired by Berghofer's formalization of Henkin-style completeness.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end

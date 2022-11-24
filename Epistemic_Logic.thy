(*
  File:      Epistemic_Logic.thy
  Author:    Asta Halkjær From

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).
  The extensions of system K (T, KB, K4, S4, S5) and their completeness proofs
  are based on the textbook "Modal Logic" by Blackburn, de Rijke and Venema
  (Cambridge University Press 2001).
*)

theory Epistemic_Logic imports "HOL-Library.Countable" begin

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
  | Di \<open>'i list\<close> \<open>'i fm\<close>

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
  \<open>f_size (Co g p) = f_size p + 1\<close> |
  \<open>f_size (Di g p) = f_size p + 2\<close> 

primrec common_count where 
  \<open>common_count \<^bold>\<bottom> = 0\<close> |
  \<open>common_count (Pro x) = 0\<close> |
  \<open>common_count (p \<^bold>\<or> q) = common_count p + common_count q\<close> |
  \<open>common_count (p \<^bold>\<and> q) = common_count p + common_count q\<close> |
  \<open>common_count (p \<^bold>\<longrightarrow> q) = common_count p + common_count q\<close> |
  \<open>common_count (K i p) = common_count p\<close> |
  \<open>common_count (Ev g p) = common_count p\<close> |
  \<open>common_count (Co g p) = common_count p + 1\<close> |
  \<open>common_count (Di g p) = common_count p\<close> 

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
| \<open>M, w \<Turnstile> Di g p \<longleftrightarrow> (\<forall>v \<in> \<W> M \<inter> (\<Inter> i \<in> set g. \<K> M i w). M, v \<Turnstile> p)\<close>
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
| \<open>eval _ h (Di g p) = h (Di g p)\<close>

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
  | D1a: \<open>A \<turnstile> Di [i] p \<^bold>\<longrightarrow> K i p\<close>
  | D1b: \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> Di [i] p\<close>
  | D2: \<open>set g \<subseteq> set g' \<Longrightarrow> A \<turnstile> Di g p \<^bold>\<longrightarrow> Di g' p\<close>
  | Dmp: \<open>A \<turnstile> Di g p \<^bold>\<longrightarrow> Di g (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> Di g q\<close>
  | RC1: \<open>A \<turnstile> p \<^bold>\<longrightarrow> Ev g (q \<^bold>\<and> p) \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> Co g q\<close>

primrec imply :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

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

lemma Ev_conE1: \<open>A \<turnstile> Ev g (p \<^bold>\<and> q) \<^bold>\<longrightarrow> Ev g p\<close> sorry

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

lemma K_L_dual: \<open>A \<turnstile> \<^bold>\<not> L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i p\<close>
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

definition maximal :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> bool\<close> where
  \<open>maximal A S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent A ({p} \<union> S)\<close>

theorem deriv_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>A \<turnstile> p\<close>
  shows \<open>p \<in> V\<close>
  using assms R1 inconsistent_subset unfolding consistent_def maximal_def
  by (metis imply.simps(2))

theorem exactly_one_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close>
  shows \<open>p \<in> V \<longleftrightarrow> (\<^bold>\<not> p) \<notin> V\<close>
proof
  assume \<open>p \<in> V\<close>
  then show \<open>(\<^bold>\<not> p) \<notin> V\<close>
    using assms K_mp unfolding consistent_def maximal_def
    by (metis empty_subsetI insert_subset list.set(1) list.simps(15))
next
  assume \<open>(\<^bold>\<not> p) \<notin> V\<close>
  have \<open>A \<turnstile> (p \<^bold>\<or> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  then have \<open>(p \<^bold>\<or> \<^bold>\<not> p) \<in> V\<close>
    using assms deriv_in_maximal by blast
  then have \<open>consistent A ({p} \<union> V) \<or> consistent A ({\<^bold>\<not> p} \<union> V)\<close>
    using assms consistent_disjuncts by blast
  then show \<open>p \<in> V\<close>
    using \<open>maximal A V\<close> \<open>(\<^bold>\<not> p) \<notin> V\<close> unfolding maximal_def by blast
qed

theorem consequent_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
  shows \<open>q \<in> V\<close>
proof -
  have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> p # (p \<^bold>\<longrightarrow> q) # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using \<open>consistent A V\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> unfolding consistent_def
    by (metis insert_subset list.simps(15))
  then have \<open>\<forall>V'. set V' \<subseteq> V \<longrightarrow> \<not> (A \<turnstile> q # V' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (meson K_mp K_ImpI K_imply_weaken K_right_mp set_subset_Cons)
  then have \<open>consistent A ({q} \<union> V)\<close>
    using \<open>consistent A V\<close> inconsistent_subset by metis
  then show ?thesis
    using \<open>maximal A V\<close> unfolding maximal_def by fast
qed

theorem ax_in_maximal:
  assumes \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>A p\<close>
  shows \<open>p \<in> V\<close>
  using assms deriv_in_maximal Ax by blast

theorem mcs_properties:
  assumes \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>A \<turnstile> p \<Longrightarrow> p \<in> V\<close>
    and \<open>p \<in> V \<longleftrightarrow> (\<^bold>\<not> p) \<notin> V\<close>
    and \<open>p \<in> V \<Longrightarrow> (p \<^bold>\<longrightarrow> q) \<in> V \<Longrightarrow> q \<in> V\<close>
  using assms deriv_in_maximal exactly_one_in_maximal consequent_in_maximal by blast+

subsection \<open>Lindenbaum extension\<close>

instantiation fm :: (countable) countable begin
instance by countable_datatype
end

primrec extend :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> nat \<Rightarrow> 'i fm set\<close> where
  \<open>extend A S f 0 = S\<close>
| \<open>extend A S f (Suc n) =
    (if consistent A ({f n} \<union> extend A S f n)
     then {f n} \<union> extend A S f n
     else extend A S f n)\<close>

definition Extend :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> 'i fm set\<close> where
  \<open>Extend A S f \<equiv> \<Union>n. extend A S f n\<close>

lemma Extend_subset: \<open>S \<subseteq> Extend A S f\<close>
  unfolding Extend_def using Union_upper extend.simps(1) range_eqI
  by metis

lemma extend_bound: \<open>(\<Union>n \<le> m. extend A S f n) = extend A S f m\<close>
  by (induct m) (simp_all add: atMost_Suc)

lemma consistent_extend: \<open>consistent A S \<Longrightarrow> consistent A (extend A S f n)\<close>
  by (induct n) simp_all

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

lemma consistent_Extend:
  assumes \<open>consistent A S\<close>
  shows \<open>consistent A (Extend A S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent A (\<Union>n. extend A S f n)\<close>
  then obtain S' where \<open>A \<turnstile> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> \<open>set S' \<subseteq> (\<Union>n. extend A S f n)\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend A S f n)\<close>
    using UN_finite_bound by (metis List.finite_set)
  then have \<open>set S' \<subseteq> extend A S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent A (extend A S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>A \<turnstile> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close> by blast
qed

lemma maximal_Extend:
  assumes \<open>surj f\<close>
  shows \<open>maximal A (Extend A S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal A (Extend A S f)\<close>
  then obtain p where \<open>p \<notin> Extend A S f\<close> \<open>consistent A ({p} \<union> Extend A S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain k where n: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend A S f (Suc k)\<close>
    using \<open>p \<notin> Extend A S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent A ({p} \<union> extend A S f k)\<close>
    using n by fastforce
  moreover have \<open>{p} \<union> extend A S f k \<subseteq> {p} \<union> Extend A S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent A ({p} \<union> Extend A S f)\<close>
    unfolding consistent_def by fastforce
  then show False
    using \<open>consistent A ({p} \<union> Extend A S f)\<close> by blast
qed

lemma maximal_extension:
  fixes V :: \<open>('i :: countable) fm set\<close>
  assumes \<open>consistent A V\<close>
  obtains W where \<open>V \<subseteq> W\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
proof -
  let ?W = \<open>Extend A V from_nat\<close>
  have \<open>V \<subseteq> ?W\<close>
    using Extend_subset by blast
  moreover have \<open>consistent A ?W\<close>
    using assms consistent_Extend by blast
  moreover have \<open>maximal A ?W\<close>
    using assms maximal_Extend surj_from_nat by blast
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

abbreviation mcss :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm set set\<close> where
  \<open>mcss A \<equiv> {W. consistent A W \<and> maximal A W}\<close>

abbreviation canonical :: \<open>('i fm \<Rightarrow> bool) \<Rightarrow> ('i, 'i fm set) kripke\<close> where
  \<open>canonical A \<equiv> \<lparr>\<W> = mcss A, \<K> = reach A, \<pi> = pi\<rparr>\<close>

lemma truth_lemma_K: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prem1: \<open>consistent A V\<close> and prem2: \<open>maximal A V\<close>
  assumes hyp:\<open>\<And> V. consistent A V \<Longrightarrow> maximal A V \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> p\<close>
  shows \<open>K i p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> K i p\<close>
proof safe
  assume \<open>K i p \<in> V\<close>
  then show \<open>canonical A, V \<Turnstile> K i p\<close>
    using hyp by auto
next
  assume \<open>canonical A, V \<Turnstile> K i p\<close>

  have \<open>\<not> consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
  proof
    assume \<open>consistent A ({\<^bold>\<not> p} \<union> known V i)\<close>
    then obtain W where W: \<open>{\<^bold>\<not> p} \<union> known V i \<subseteq> W\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
      using \<open>consistent A V\<close> maximal_extension by blast
    then have \<open>canonical A, W \<Turnstile> \<^bold>\<not> p\<close>
      using hyp \<open>consistent A V\<close> exactly_one_in_maximal by auto
    moreover have \<open>W \<in> reach A i V\<close> \<open>W \<in> mcss A\<close>
      using W by simp_all
    ultimately have \<open>canonical A, V \<Turnstile> \<^bold>\<not> K i p\<close>
      by auto
    then show False
      using \<open>canonical A, V \<Turnstile> K i p\<close> by auto
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
  then have \<open>(map (K i) L \<^bold>\<leadsto> K i p) \<in> V\<close>
    using deriv_in_maximal prem1 prem2 by blast
  then show \<open>K i p \<in> V\<close>
    using L W(1-2)
  proof (induct L arbitrary: W)
    case (Cons a L)
    then have \<open>K i a \<in> V\<close>
      by auto
    then have \<open>(map (K i) L \<^bold>\<leadsto> K i p) \<in> V\<close>
      using Cons(2) \<open>consistent A V\<close> \<open>maximal A V\<close> consequent_in_maximal by auto
    then show ?case
      using Cons by auto
  qed simp
qed

lemma truth_lemma_Ev: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prem1: \<open>consistent A V\<close> and prem2: \<open>maximal A V\<close>
  assumes hyp:\<open>\<And> V. consistent A V \<Longrightarrow> maximal A V \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> p\<close>
  shows \<open>Ev g p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> Ev g p\<close>
proof (induct g)
  case Nil
  then show ?case sorry
next
  case (Cons a g)
  then show ?case sorry
qed

lemma truth_lemma_Ev_n: 
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes prem1: \<open>consistent A V\<close> and prem2: \<open>maximal A V\<close>
  assumes hyp:\<open>\<And> V. consistent A V \<Longrightarrow> maximal A V \<Longrightarrow> p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> p\<close>
  shows \<open>n \<ge> 1 \<Longrightarrow> Ev_n g p n \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> Ev_n g p n\<close>(*might need to strengthen the claim like I did for soundness*)
proof (induct n rule: less_induct) 
  case less
  then show ?case sorry
qed

lemma truth_lemma:
  fixes p :: \<open>('i :: countable) fm\<close>
  assumes \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>p \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> p\<close>
  using assms
proof (induct p arbitrary: V)
  case FF
  then show ?case
  proof safe
    assume \<open>\<^bold>\<bottom> \<in> V\<close>
    then have False
      using \<open>consistent A V\<close> K_imply_head unfolding consistent_def 
      by (metis bot.extremum insert_subset list.set(1) list.simps(15))
    then show \<open>canonical A, V \<Turnstile> \<^bold>\<bottom>\<close> ..
  next
    assume \<open>canonical A, V \<Turnstile> \<^bold>\<bottom>\<close>
    then show \<open>\<^bold>\<bottom> \<in> V\<close>
      by simp
  qed
next
  case (Pro x)
  then show ?case
    by simp
next
  case (Dis p q)
  then show ?case
  proof safe
    assume \<open>(p \<^bold>\<or> q) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_disjuncts by blast
    then have \<open>p \<in> V \<or> q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<or> q)\<close>
      using Dis by simp
  next
    assume \<open>canonical A, V \<Turnstile> (p \<^bold>\<or> q)\<close>
    then consider \<open>canonical A, V \<Turnstile> p\<close> | \<open>canonical A, V \<Turnstile> q\<close>
      by auto
    then have \<open>p \<in> V \<or> q \<in> V\<close>
      using Dis by auto
    moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close> \<open>A \<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<or> q\<close>
      by (auto simp: A1)
    ultimately show \<open>(p \<^bold>\<or> q) \<in> V\<close>
      using Dis.prems deriv_in_maximal consequent_in_maximal by blast
  qed
next
  case (Con p q)
  then show ?case
  proof safe
    assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
    then have \<open>consistent A ({p} \<union> V)\<close> \<open>consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce+
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast+
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<and> q)\<close>
      using Con by simp
  next
    assume \<open>canonical A, V \<Turnstile> (p \<^bold>\<and> q)\<close>
    then have \<open>canonical A, V \<Turnstile> p\<close> \<open>canonical A, V \<Turnstile> q\<close>
      by auto
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
      using Con by auto
    moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<and> q\<close>
      by (auto simp: A1)
    ultimately show \<open>(p \<^bold>\<and> q) \<in> V\<close>
      using Con.prems deriv_in_maximal consequent_in_maximal by blast
  qed
next
  case (Imp p q)
  then show ?case
  proof safe
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
    then have \<open>consistent A ({\<^bold>\<not> p \<^bold>\<or> q} \<union> V)\<close>
      using \<open>consistent A V\<close> consistent_consequent' by fastforce
    then have \<open>consistent A ({\<^bold>\<not> p} \<union> V) \<or> consistent A ({q} \<union> V)\<close>
      using \<open>consistent A V\<close> \<open>maximal A V\<close> consistent_disjuncts unfolding maximal_def by blast
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close>
      using \<open>maximal A V\<close> unfolding maximal_def by fast
    then have \<open>p \<notin> V \<or> q \<in> V\<close>
      using Imp.prems exactly_one_in_maximal by blast
    then show \<open>canonical A, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
      using Imp by simp
  next
    assume \<open>canonical A, V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    then consider \<open>\<not> canonical A, V \<Turnstile> p\<close> | \<open>canonical A, V \<Turnstile> q\<close>
      by auto
    then have \<open>p \<notin> V \<or> q \<in> V\<close>
      using Imp by auto
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close>
      using Imp.prems exactly_one_in_maximal by blast
    moreover have \<open>A \<turnstile> \<^bold>\<not> p \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close> \<open>A \<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
      by (auto simp: A1)             
    ultimately show \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
      using Imp.prems deriv_in_maximal consequent_in_maximal by blast
  qed
next
  case (K i p)
  then show ?case
    using truth_lemma_K by blast
next
  case (Ev g p)
  then show ?case 
    using truth_lemma_Ev by blast
next
  case (Co g p)
  then have 1: \<open>\<forall> n \<ge> 1. Ev_n g p n \<in> V \<longleftrightarrow> canonical A, V \<Turnstile> Ev_n g p n\<close>
    using truth_lemma_Ev_n by blast
  show ?case
  proof (rule iffI)
    assume a: \<open>Co g p \<in> V\<close>
    have \<open>n \<ge> 1 \<Longrightarrow> Ev_n g p n \<in> V\<close> for n
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
        ultimately have \<open>A \<turnstile> Co g p \<^bold>\<longrightarrow> Ev g p\<close>
          using imp_chain by auto
        then have \<open>Co g p \<^bold>\<longrightarrow> Ev g p \<in> V\<close>
          using Co.prems deriv_in_maximal by blast
        then have \<open>Ev g p \<in> V\<close>
          using a Co.prems consequent_in_maximal by blast
        then show ?thesis  
          by (simp add: n'_eq_1) 
      next
        case n'_geq_2
        then show ?thesis sorry
      qed
    qed
    then have \<open>\<forall> n \<ge> 1. canonical A, V \<Turnstile> Ev_n g p n\<close> 
      using 1 by simp
    then show \<open>canonical A, V \<Turnstile> Co g p\<close>
      by simp
  next
    assume \<open>canonical A, V \<Turnstile> Co g p\<close> 
    show \<open>Co g p \<in> V\<close>sorry
  qed
next
  case (Di g p)
  then show ?case sorry
qed

lemma canonical_model:
  assumes \<open>consistent A S\<close> and \<open>p \<in> S\<close>
  defines \<open>V \<equiv> Extend A S from_nat\<close> and \<open>M \<equiv> canonical A\<close>
  shows \<open>M, V \<Turnstile> p\<close> and \<open>consistent A V\<close> and \<open>maximal A V\<close>
proof -
  have \<open>consistent A V\<close>
    using \<open>consistent A S\<close> unfolding V_def using consistent_Extend by blast
  have \<open>maximal A V\<close>
    unfolding V_def using maximal_Extend surj_from_nat by blast
  { fix x
    assume \<open>x \<in> S\<close>
    then have \<open>x \<in> V\<close>
      unfolding V_def using Extend_subset by blast
    then have \<open>M, V \<Turnstile> x\<close>
      unfolding M_def using truth_lemma \<open>consistent A V\<close> \<open>maximal A V\<close> by blast }
  then show \<open>M, V \<Turnstile> p\<close>
    using \<open>p \<in> S\<close> by blast+
  show \<open>consistent A V\<close> \<open>maximal A V\<close>
    by fact+
qed

subsection \<open>Completeness\<close>

abbreviation valid :: \<open>(('i :: countable, 'i fm set) kripke \<Rightarrow> bool) \<Rightarrow> 'i fm set \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  (\<open>_; _ \<TTurnstile> _\<close> [50, 50, 50] 50)
  where \<open>P; G \<TTurnstile> p \<equiv> P; G \<TTurnstile>\<star> p\<close>

theorem strong_completeness:
  assumes \<open>P; G \<TTurnstile> p\<close> and \<open>P (canonical A)\<close>
  shows \<open>A; G \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>qs. set qs \<subseteq> G \<and> (A \<turnstile> qs \<^bold>\<leadsto> p)\<close>
  then have *: \<open>\<forall>qs. set qs \<subseteq> G \<longrightarrow> \<not> (A \<turnstile> (\<^bold>\<not> p) # qs \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    using K_Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> G\<close>
  let ?V = \<open>Extend A ?S from_nat\<close>
  let ?M = \<open>canonical A\<close>

  have \<open>consistent A ?S\<close>
    using * by (metis K_imply_Cons consistent_def inconsistent_subset)
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> G. ?M, ?V \<Turnstile> q\<close>
    using canonical_model by fastforce+
  moreover have \<open>?V \<in> mcss A\<close>
    using \<open>consistent A ?S\<close> consistent_Extend maximal_Extend surj_from_nat by blast
  ultimately have \<open>?M, ?V \<Turnstile> p\<close>
    using assms by simp
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

corollary completeness:
  assumes \<open>P; {} \<TTurnstile> p\<close> and \<open>P (canonical A)\<close>
  shows \<open>A \<turnstile> p\<close>
  using assms strong_completeness[where G=\<open>{}\<close>] by simp

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

lemma strong_completeness\<^sub>K: \<open>G \<TTurnstile>\<^sub>K p \<Longrightarrow> G \<turnstile>\<^sub>K p\<close>
  using strong_completeness[of \<open>\<lambda>_. True\<close>] by blast

theorem main\<^sub>K: \<open>G \<TTurnstile>\<^sub>K p \<longleftrightarrow> G \<turnstile>\<^sub>K p\<close>
  using strong_soundness\<^sub>K[of G p] strong_completeness\<^sub>K[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>K p \<Longrightarrow> (\<lambda>_. True); G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>K[of G p] strong_completeness\<^sub>K[of G p] by fast

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
  assumes \<open>AxT \<le> A\<close> and \<open>consistent A V\<close> and \<open>maximal A V\<close>
  shows \<open>V \<in> reach A i V\<close>
proof -
  have \<open>(K i p \<^bold>\<longrightarrow> p) \<in> V\<close> for p
    using assms ax_in_maximal AxT.intros by fast
  then have \<open>p \<in> V\<close> if \<open>K i p \<in> V\<close> for p
    using that assms consequent_in_maximal by blast
  then show ?thesis
    using assms by blast
qed

lemma reflexive\<^sub>T:
  assumes \<open>AxT \<le> A\<close>
  shows \<open>reflexive (canonical A)\<close>
  unfolding reflexive_def
proof safe
  fix i V
  assume \<open>V \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close>
    by simp_all
  with AxT_reflexive assms have \<open>V \<in> reach A i V\<close> .
  then show \<open>V \<in> \<K> (canonical A) i V\<close>
    by simp
qed

abbreviation validT (\<open>_ \<TTurnstile>\<^sub>T _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>T p \<equiv> reflexive; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>T: \<open>G \<TTurnstile>\<^sub>T p \<Longrightarrow> G \<turnstile>\<^sub>T p\<close>
  using strong_completeness reflexive\<^sub>T by blast

theorem main\<^sub>T: \<open>G \<TTurnstile>\<^sub>T p \<longleftrightarrow> G \<turnstile>\<^sub>T p\<close>
  using strong_soundness\<^sub>T[of G p] strong_completeness\<^sub>T[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>T p \<longrightarrow> reflexive; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>T[of G p] strong_completeness\<^sub>T[of G p] by fast


section \<open>System KB\<close>

inductive AxB :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxB (p \<^bold>\<longrightarrow> K i (L i p))\<close>

abbreviation SystemKB (\<open>_ \<turnstile>\<^sub>K\<^sub>B _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>K\<^sub>B p \<equiv> AxB; G \<turnstile> p\<close>

lemma soundness_AxB: \<open>AxB p \<Longrightarrow> symmetric M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  unfolding symmetric_def by (induct p rule: AxB.induct) auto

lemma strong_soundness\<^sub>K\<^sub>B: \<open>G \<turnstile>\<^sub>K\<^sub>B p \<Longrightarrow> symmetric; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_AxB .

lemma AxB_symmetric':
  assumes \<open>AxB \<le> A\<close> \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
    and \<open>W \<in> reach A i V\<close>
  shows \<open>V \<in> reach A i W\<close>
proof -
  have \<open>\<forall>p. K i p \<in> W \<longrightarrow> p \<in> V\<close>
  proof (safe, rule ccontr)
    fix p
    assume \<open>K i p \<in> W\<close> \<open>p \<notin> V\<close>
    then have \<open>(\<^bold>\<not> p) \<in> V\<close>
      using assms(2-3) exactly_one_in_maximal by fast
    then have \<open>K i (L i (\<^bold>\<not> p)) \<in> V\<close>
      using assms(1-3) ax_in_maximal AxB.intros consequent_in_maximal by fast
    then have \<open>L i (\<^bold>\<not> p) \<in> W\<close>
      using \<open>W \<in> reach A i V\<close> by fast
    then have \<open>(\<^bold>\<not> K i p) \<in> W\<close>
      using assms(4-5) by (meson K_LK consistent_consequent maximal_def)
    then show False
      using \<open>K i p \<in> W\<close> assms(4-5) exactly_one_in_maximal by fast
  qed
  then have \<open>known W i \<subseteq> V\<close>
    by blast
  then show ?thesis
    using assms(2-3) by simp
qed

lemma symmetric\<^sub>K\<^sub>B:
  assumes \<open>AxB \<le> A\<close>
  shows \<open>symmetric (canonical A)\<close>
  unfolding symmetric_def
proof (intro allI ballI)
  fix i V W
  assume \<open>V \<in> \<W> (canonical A)\<close> \<open>W \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close> \<open>consistent A W\<close> \<open>maximal A W\<close>
    by simp_all
  with AxB_symmetric' assms have \<open>W \<in> reach A i V \<longleftrightarrow> V \<in> reach A i W\<close>
    by metis
  then show \<open>(W \<in> \<K> (canonical A) i V) = (V \<in> \<K> (canonical A) i W)\<close>
    by simp
qed

abbreviation validKB (\<open>_ \<TTurnstile>\<^sub>K\<^sub>B _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>K\<^sub>B p \<equiv> symmetric; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>K\<^sub>B: \<open>G \<TTurnstile>\<^sub>K\<^sub>B p \<Longrightarrow> G \<turnstile>\<^sub>K\<^sub>B p\<close>
  using strong_completeness symmetric\<^sub>K\<^sub>B by blast

theorem main\<^sub>K\<^sub>B: \<open>G \<TTurnstile>\<^sub>K\<^sub>B p \<longleftrightarrow> G \<turnstile>\<^sub>K\<^sub>B p\<close>
  using strong_soundness\<^sub>K\<^sub>B[of G p] strong_completeness\<^sub>K\<^sub>B[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>K\<^sub>B p \<longrightarrow> symmetric; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>K\<^sub>B[of G p] strong_completeness\<^sub>K\<^sub>B[of G p] by fast

section \<open>System K4\<close>

inductive Ax4 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>Ax4 (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>

abbreviation SystemK4 (\<open>_ \<turnstile>\<^sub>K\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>K\<^sub>4 p \<equiv> Ax4; G \<turnstile> p\<close>

lemma soundness_Ax4: \<open>Ax4 p \<Longrightarrow> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: Ax4.induct) (meson pos_introspection)

lemma strong_soundness\<^sub>K\<^sub>4: \<open>G \<turnstile>\<^sub>K\<^sub>4 p \<Longrightarrow> transitive; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_Ax4 .

lemma Ax4_transitive:
  assumes \<open>Ax4 \<le> A\<close> \<open>consistent A V\<close> \<open>maximal A V\<close>
    and \<open>W \<in> reach A i V\<close> \<open>U \<in> reach A i W\<close>
  shows \<open>U \<in> reach A i V\<close>
proof -
  have \<open>(K i p \<^bold>\<longrightarrow> K i (K i p)) \<in> V\<close> for p
    using assms(1-3) ax_in_maximal Ax4.intros by fast
  then have \<open>K i (K i p) \<in> V\<close> if \<open>K i p \<in> V\<close> for p
    using that assms(2-3) consequent_in_maximal by blast
  then show ?thesis
    using assms(4-5) by blast
qed

lemma transitive\<^sub>K\<^sub>4:
  assumes \<open>Ax4 \<le> A\<close>
  shows \<open>transitive (canonical A)\<close>
  unfolding transitive_def
proof safe
  fix i U V W
  assume \<open>V \<in> \<W> (canonical A)\<close>
  then have \<open>consistent A V\<close> \<open>maximal A V\<close>
    by simp_all
  moreover assume
    \<open>W \<in> \<K> (canonical A) i V\<close>
    \<open>U \<in> \<K> (canonical A) i W\<close>
  ultimately have \<open>U \<in> reach A i V\<close>
    using Ax4_transitive assms by simp
  then show \<open>U \<in> \<K> (canonical A) i V\<close>
    by simp
qed

abbreviation validK4 (\<open>_ \<TTurnstile>\<^sub>K\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>K\<^sub>4 p \<equiv> transitive; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>K\<^sub>4: \<open>G \<TTurnstile>\<^sub>K\<^sub>4 p \<Longrightarrow> G \<turnstile>\<^sub>K\<^sub>4 p\<close>
  using strong_completeness transitive\<^sub>K\<^sub>4 by blast

theorem main\<^sub>K\<^sub>4: \<open>G \<TTurnstile>\<^sub>K\<^sub>4 p \<longleftrightarrow> G \<turnstile>\<^sub>K\<^sub>4 p\<close>
  using strong_soundness\<^sub>K\<^sub>4[of G p] strong_completeness\<^sub>K\<^sub>4[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>K\<^sub>4 p \<longrightarrow> transitive; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>K\<^sub>4[of G p] strong_completeness\<^sub>K\<^sub>4[of G p] by fast

section \<open>System K5\<close>

inductive Ax5 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>Ax5 (L i p \<^bold>\<longrightarrow> K i (L i p))\<close>

abbreviation SystemK5 (\<open>_ \<turnstile>\<^sub>K\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>K\<^sub>5 p \<equiv> Ax5; G \<turnstile> p\<close>

lemma soundness_Ax5: \<open>Ax5 p \<Longrightarrow> Euclidean M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  by (induct p rule: Ax5.induct) (unfold Euclidean_def semantics.simps, blast)

lemma strong_soundness\<^sub>K\<^sub>5: \<open>G \<turnstile>\<^sub>K\<^sub>5 p \<Longrightarrow> Euclidean; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_Ax5 .

lemma Ax5_Euclidean:
  assumes \<open>Ax5 \<le> A\<close>
    \<open>consistent A U\<close> \<open>maximal A U\<close>
    \<open>consistent A V\<close> \<open>maximal A V\<close>
    \<open>consistent A W\<close> \<open>maximal A W\<close>
    and \<open>V \<in> reach A i U\<close> \<open>W \<in> reach A i U\<close>
  shows \<open>W \<in> reach A i V\<close>
  using assms
proof -
  { fix p
    assume \<open>K i p \<in> V\<close> \<open>p \<notin> W\<close>
    then have \<open>(\<^bold>\<not> p) \<in> W\<close>
      using assms(6-7) exactly_one_in_maximal by fast
    then have \<open>L i (\<^bold>\<not> p) \<in> U\<close>
      using assms(2-3, 6-7, 9) exactly_one_in_maximal by blast
    then have \<open>K i (L i (\<^bold>\<not> p)) \<in> U\<close>
      using assms(1-3) ax_in_maximal Ax5.intros consequent_in_maximal by fast
    then have \<open>L i (\<^bold>\<not> p) \<in> V\<close>
      using assms(8) by blast
    then have \<open>\<^bold>\<not> K i p \<in> V\<close>
      using assms(4-5) K_LK consequent_in_maximal deriv_in_maximal by fast
    then have False
      using assms(4-5) \<open>K i p \<in> V\<close> exactly_one_in_maximal by fast
  }
  then show ?thesis
    by blast
qed

lemma Euclidean\<^sub>K\<^sub>5:
  assumes \<open>Ax5 \<le> A\<close>
  shows \<open>Euclidean (canonical A)\<close>
  unfolding Euclidean_def
proof safe
  fix i U V W
  assume \<open>U \<in> \<W> (canonical A)\<close> \<open>V \<in> \<W> (canonical A)\<close> \<open>W \<in> \<W> (canonical A)\<close>
  then have
    \<open>consistent A U\<close> \<open>maximal A U\<close>
    \<open>consistent A V\<close> \<open>maximal A V\<close>
    \<open>consistent A W\<close> \<open>maximal A W\<close>
    by simp_all
  moreover assume
    \<open>V \<in> \<K> (canonical A) i U\<close>
    \<open>W \<in> \<K> (canonical A) i U\<close>
  ultimately have \<open>W \<in> reach A i V\<close>
    using Ax5_Euclidean assms by simp
  then show \<open>W \<in> \<K> (canonical A) i V\<close>
    by simp
qed

abbreviation validK5 (\<open>_ \<TTurnstile>\<^sub>K\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>K\<^sub>5 p \<equiv> Euclidean; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>K\<^sub>5: \<open>G \<TTurnstile>\<^sub>K\<^sub>5 p \<Longrightarrow> G \<turnstile>\<^sub>K\<^sub>5 p\<close>
  using strong_completeness Euclidean\<^sub>K\<^sub>5 by blast

theorem main\<^sub>K\<^sub>5: \<open>G \<TTurnstile>\<^sub>K\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>K\<^sub>5 p\<close>
  using strong_soundness\<^sub>K\<^sub>5[of G p] strong_completeness\<^sub>K\<^sub>5[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>K\<^sub>5 p \<longrightarrow> Euclidean; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>K\<^sub>5[of G p] strong_completeness\<^sub>K\<^sub>5[of G p] by fast

section \<open>System S4\<close>

abbreviation Or :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<oplus>\<close> 65) where
  \<open>(A \<oplus> A') p \<equiv> A p \<or> A' p\<close>

abbreviation SystemS4 (\<open>_ \<turnstile>\<^sub>S\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>S\<^sub>4 p \<equiv> AxT \<oplus> Ax4; G \<turnstile> p\<close>

lemma soundness_AxT4: \<open>(AxT \<oplus> Ax4) p \<Longrightarrow> reflexive M \<and> transitive M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT soundness_Ax4 by fast

lemma strong_soundness\<^sub>S\<^sub>4: \<open>G \<turnstile>\<^sub>S\<^sub>4 p \<Longrightarrow> refltrans; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_AxT4 .

abbreviation validS4 (\<open>_ \<TTurnstile>\<^sub>S\<^sub>4 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>S\<^sub>4 p \<equiv> refltrans; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>S\<^sub>4: \<open>G \<TTurnstile>\<^sub>S\<^sub>4 p \<Longrightarrow> G \<turnstile>\<^sub>S\<^sub>4 p\<close>
  using strong_completeness[of refltrans] reflexive\<^sub>T[of \<open>AxT \<oplus> Ax4\<close>] transitive\<^sub>K\<^sub>4[of \<open>AxT \<oplus> Ax4\<close>]
  by blast

theorem main\<^sub>S\<^sub>4: \<open>G \<TTurnstile>\<^sub>S\<^sub>4 p \<longleftrightarrow> G \<turnstile>\<^sub>S\<^sub>4 p\<close>
  using strong_soundness\<^sub>S\<^sub>4[of G p] strong_completeness\<^sub>S\<^sub>4[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>S\<^sub>4 p \<longrightarrow> refltrans; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>S\<^sub>4[of G p] strong_completeness\<^sub>S\<^sub>4[of G p] by fast

section \<open>System S5\<close>

subsection \<open>T + B + 4\<close>

abbreviation SystemS5 (\<open>_ \<turnstile>\<^sub>S\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>S\<^sub>5 p \<equiv> AxT \<oplus> AxB \<oplus> Ax4; G \<turnstile> p\<close>

abbreviation AxTB4 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxTB4 \<equiv> AxT \<oplus> AxB \<oplus> Ax4\<close>

lemma soundness_AxTB4: \<open>AxTB4 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT soundness_AxB soundness_Ax4 by fast

lemma strong_soundness\<^sub>S\<^sub>5: \<open>G \<turnstile>\<^sub>S\<^sub>5 p \<Longrightarrow> equivalence; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_AxTB4 .

abbreviation validS5 (\<open>_ \<TTurnstile>\<^sub>S\<^sub>5 _\<close> [50, 50] 50) where
  \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<equiv> equivalence; G \<TTurnstile> p\<close>

lemma strong_completeness\<^sub>S\<^sub>5: \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<Longrightarrow> G \<turnstile>\<^sub>S\<^sub>5 p\<close>
  using strong_completeness[of equivalence]
    reflexive\<^sub>T[of AxTB4] symmetric\<^sub>K\<^sub>B[of AxTB4] transitive\<^sub>K\<^sub>4[of AxTB4]
  by blast

theorem main\<^sub>S\<^sub>5: \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>S\<^sub>5 p\<close>
  using strong_soundness\<^sub>S\<^sub>5[of G p] strong_completeness\<^sub>S\<^sub>5[of G p] by fast

corollary \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<longrightarrow> equivalence; G \<TTurnstile>\<star> p\<close>
  using strong_soundness\<^sub>S\<^sub>5[of G p] strong_completeness\<^sub>S\<^sub>5[of G p] by fast

subsection \<open>T + 5\<close>

abbreviation SystemS5' (\<open>_ \<turnstile>\<^sub>S\<^sub>5'' _\<close> [50, 50] 50) where
  \<open>G \<turnstile>\<^sub>S\<^sub>5' p \<equiv> AxT \<oplus> Ax5; G \<turnstile> p\<close>

abbreviation AxT5 :: \<open>'i fm \<Rightarrow> bool\<close> where
  \<open>AxT5 \<equiv> AxT \<oplus> Ax5\<close>

lemma symm_trans_Euclid: \<open>symmetric M \<Longrightarrow> transitive M \<Longrightarrow> Euclidean M\<close>
  unfolding symmetric_def transitive_def Euclidean_def by blast

lemma soundness_AxT5: \<open>AxT5 p \<Longrightarrow> equivalence M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> M, w \<Turnstile> p\<close>
  using soundness_AxT[of p M w] soundness_Ax5[of p M w] symm_trans_Euclid by blast

lemma strong_soundness\<^sub>S\<^sub>5': \<open>G \<turnstile>\<^sub>S\<^sub>5' p \<Longrightarrow> equivalence; G \<TTurnstile>\<star> p\<close>
  using strong_soundness soundness_AxT5 .

lemma refl_Euclid_equiv: \<open>reflexive M \<Longrightarrow> Euclidean M \<Longrightarrow> equivalence M\<close>
  unfolding reflexive_def symmetric_def transitive_def Euclidean_def by metis

lemma strong_completeness\<^sub>S\<^sub>5': \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<Longrightarrow> G \<turnstile>\<^sub>S\<^sub>5' p\<close>
  using strong_completeness[of equivalence]
    reflexive\<^sub>T[of AxT5] Euclidean\<^sub>K\<^sub>5[of AxT5] refl_Euclid_equiv by blast

theorem main\<^sub>S\<^sub>5': \<open>G \<TTurnstile>\<^sub>S\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>S\<^sub>5' p\<close>
  using strong_soundness\<^sub>S\<^sub>5'[of G p] strong_completeness\<^sub>S\<^sub>5'[of G p] by fast

subsection \<open>Equivalence between systems\<close>

subsubsection \<open>Axiom 5 from B and 4\<close>

lemma K4_L:
  assumes \<open>Ax4 \<le> A\<close>
  shows \<open>A \<turnstile> L i (L i p) \<^bold>\<longrightarrow> L i p\<close>
proof -
  have \<open>A \<turnstile> K i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i (K i (\<^bold>\<not> p))\<close>
    using assms by (auto intro: Ax Ax4.intros)
  then show ?thesis
    by (meson K_LK K_trans R1)
qed

lemma KB4_5:
  assumes \<open>AxB \<le> A\<close> \<open>Ax4 \<le> A\<close>
  shows \<open>A \<turnstile> L i p \<^bold>\<longrightarrow> K i (L i p)\<close>
proof -
  have \<open>A \<turnstile> L i p \<^bold>\<longrightarrow> K i (L i (L i p))\<close>
    using assms by (auto intro: Ax AxB.intros)
  moreover have \<open>A \<turnstile> L i (L i p) \<^bold>\<longrightarrow> L i p\<close>
    using assms by (auto intro: K4_L)
  then have \<open>A \<turnstile> K i (L i (L i p)) \<^bold>\<longrightarrow> K i (L i p)\<close>
    using K_map by fast
  ultimately show ?thesis
    using K_trans R1 by metis
qed

subsubsection \<open>Axioms B and 4 from T and 5\<close>

lemma T_L:
  assumes \<open>AxT \<le> A\<close>
  shows \<open>A \<turnstile> p \<^bold>\<longrightarrow> L i p\<close>
proof -
  have \<open>A \<turnstile> K i (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<not> p\<close>
    using assms by (auto intro: Ax AxT.intros)
  moreover have \<open>A \<turnstile> (P \<^bold>\<longrightarrow> \<^bold>\<not> Q) \<^bold>\<longrightarrow> Q \<^bold>\<longrightarrow> \<^bold>\<not> P\<close> for P Q
    by (auto intro: A1)
  ultimately show ?thesis
    by (auto intro: R1)
qed

lemma S5'_B:
  assumes \<open>AxT \<le> A\<close> \<open>Ax5 \<le> A\<close>
  shows \<open>A \<turnstile> p \<^bold>\<longrightarrow> K i (L i p)\<close>
proof -
  have \<open>A \<turnstile> L i p \<^bold>\<longrightarrow> K i (L i p)\<close>
    using assms(2) by (auto intro: Ax Ax5.intros)
  moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> L i p\<close>
    using assms(1) by (auto intro: T_L)
  ultimately show ?thesis
    using K_trans R1 by metis
qed

lemma K5_L:
  assumes \<open>Ax5 \<le> A\<close>
  shows \<open>A \<turnstile> L i (K i p) \<^bold>\<longrightarrow> K i p\<close>
proof -
  have \<open>A \<turnstile> L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i (L i (\<^bold>\<not> p))\<close>
    using assms by (auto intro: Ax Ax5.intros)
  then have \<open>A \<turnstile> L i (\<^bold>\<not> p) \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p)\<close>
    using K_LK by (metis K_map K_trans R1)
  moreover have \<open>A \<turnstile> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> \<^bold>\<not> Q \<^bold>\<longrightarrow> \<^bold>\<not> P\<close> for P Q
    by (auto intro: A1)
  ultimately have \<open>A \<turnstile> \<^bold>\<not> K i (\<^bold>\<not> K i p) \<^bold>\<longrightarrow> \<^bold>\<not> L i (\<^bold>\<not> p)\<close>
    using R1 by blast
  then have \<open>A \<turnstile> \<^bold>\<not> K i (\<^bold>\<not> K i p) \<^bold>\<longrightarrow> K i p\<close>
    using K_L_dual R1 K_trans by metis
  then show ?thesis
    by blast
qed

lemma S5'_4:
  assumes \<open>AxT \<le> A\<close> \<open>Ax5 \<le> A\<close>
  shows \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> K i (K i p)\<close>
proof -
  have \<open>A \<turnstile> L i (K i p) \<^bold>\<longrightarrow> K i (L i (K i p))\<close>
    using assms(2) by (auto intro: Ax Ax5.intros)
  moreover have \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> L i (K i p)\<close>
    using assms(1) by (auto intro: T_L)
  ultimately have \<open>A \<turnstile> K i p \<^bold>\<longrightarrow> K i (L i (K i p))\<close>
    using K_trans R1 by metis
  moreover have \<open>A \<turnstile> L i (K i p) \<^bold>\<longrightarrow> K i p\<close>
    using assms(2) K5_L by metis
  then have \<open>A \<turnstile> K i (L i (K i p)) \<^bold>\<longrightarrow> K i (K i p)\<close>
    using K_map by fast
  ultimately show ?thesis
    using R1 K_trans by metis
qed

lemma S5_S5': \<open>AxTB4 \<turnstile> p \<Longrightarrow> AxT5 \<turnstile> p\<close>
proof (induct p rule: AK.induct)
  case (Ax p)
  moreover have \<open>AxT5 \<turnstile> p\<close> if \<open>AxT p\<close>
    using that AK.Ax by metis
  moreover have \<open>AxT5 \<turnstile> p\<close> if \<open>AxB p\<close>
    using that S5'_B by (metis (no_types, lifting) AxB.cases predicate1I)
  moreover have \<open>AxT5 \<turnstile> p\<close> if \<open>Ax4 p\<close>
    using that S5'_4 by (metis (no_types, lifting) Ax4.cases predicate1I)
  ultimately show ?case
    by blast
qed (auto intro: AK.intros)

lemma S5'_S5: \<open>AxT5 \<turnstile> p \<Longrightarrow> AxTB4 \<turnstile> p\<close>
proof (induct p rule: AK.induct)
  case (Ax p)
  moreover have \<open>AxTB4 \<turnstile> p\<close> if \<open>AxT p\<close>
    using that AK.Ax by metis
  moreover have \<open>AxTB4 \<turnstile> p\<close> if \<open>Ax5 p\<close>
    using that KB4_5 by (metis (no_types, lifting) Ax5.cases predicate1I)
  ultimately show ?case
    by blast
qed (auto intro: AK.intros)

corollary S5_S5'_assms: \<open>G \<turnstile>\<^sub>S\<^sub>5 p \<longleftrightarrow> G \<turnstile>\<^sub>S\<^sub>5' p\<close>
  using S5_S5' S5'_S5 by blast


section \<open>Acknowledgements\<close>

text \<open>
The formalization is inspired by Berghofer's formalization of Henkin-style completeness.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end

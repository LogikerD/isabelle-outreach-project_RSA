theory "5sol_extendedEuclAlgo"

imports Main "4sol_Congruence" Complex_Main

begin

chapter \<open>Group 5: Euclidean Algorithm and code generation\<close>

section \<open>Informal introduction and instructions\<close>

text \<open>This project aims at
  \<^item> defining the Euclidean algorithm and the extended Euclidean algorithm,
  \<^item> proving their properties,
  \<^item> exporting both  to an executable programme\<close>

subsection \<open>Connection to Project 4, little Fermat theorem\<close>

text \<open>In this project you may use results from Project 4. 
    This is to say that there is no need to bother about the sorries therein and you only must work 
    in this file. \<close>

subsection \<open>Tasks\<close>

text \<open>
  \<^enum> Replace all sorries in this theory by a proof. This may include adding new lemmas.
  \<^enum> Do the other tasks indicated throughout this document.
  presentation:
  \<^enum> Prepare a short presentation regarding the content of your project and your progress.
  \<^enum> Present around 3 exercise regarding the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance.\<close>

section \<open>Connection of Project 4 with the mod function\<close>

text \<open>The Euclidean algorithm is built base on the mod function.
  To see its definition press Ctrl and klick on any "mod".
  The crucial connection between the mod function and the congruence relation examined in the 
  Project 4 is as expressed by the following lemma.\<close>

lemma mod_cogruent: "(a \<equiv> b \<langle>n\<rangle>)  \<longleftrightarrow> (a mod n) = (b mod n)"
  using %sol mult.commute nat_mod_eq_iff congruent_def
  by %sol presburger


section \<open>The simple Euclidean algorithm\<close>

text \<open>The Euclidean algorithm calculates the greatest common divisor (gcd, Germ. größter gemeinsamer 
  Teiler, ggT) of two given natural numbers.
  It may be defined as:\<close>

fun gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"gcd m 0 = m" |
"gcd m n = gcd n (m mod n)"

subsection \<open>Properties\<close>

lemma divides_0[simp]:"n divides 0"
  unfolding %sol divides_def by %sol simp

lemma divides_mod_imp_divides:
  assumes "c divides a mod b" and "c divides b"
  shows "c divides a"
  using %sol assms div_mod_decomp divides_plus mult.left_commute unfolding %sol divides_def by %sol metis

theorem gcd_divides_both: "(gcd m n divides m) \<and> (gcd m n divides n)"
  text \<open>Hint: Consult \<^doc>\<open>prog-prove\<close>, 4.4.3, and also 2.3.4\<close>
 apply %sol (induction m n rule: "gcd.induct", simp)
  apply %sol (simp)
using %sol divides_mod_imp_divides by %sol blast

lemma %solDel divides_mod: "k divides m \<Longrightarrow> k divides n \<Longrightarrow> k divides (m mod n)"
  unfolding divides_def by fastforce

theorem gcd_greatest: "k divides m \<longrightarrow> k divides n \<longrightarrow> k divides gcd m n"
  text \<open>Hint: Consult \<^doc>\<open>prog-prove\<close>, 4.4.3, and also 2.3.4\<close>
  apply %sol (induction m n rule: "gcd.induct")
   apply %sol simp
    using %sol divides_mod gcd.simps(2) by %sol presburger

proposition gcd_sym:"gcd a b = gcd b a"
  by %sol (metis gcd.elims gr_zeroI linorder_neqE_nat mod_less)

subsection \<open>Task: Now export!\<close>

text \<open>
  \<^enum> export the function to a programming language of your choosing. 
    To this end consult the \<^doc>\<open>codegen\<close> tutorial.
  \<^enum> Run the code on your machine.
\<close>


export_code %solDel gcd in Haskell module_name gcd

section \<open>The extended algorithm\<close> 

text \<open>For applications one often does not only require only the gcd, but also a concrete way 
  to represent it as a linear combination of its arguments.
  This linear combination is called Bézout identity.
  There are many resources online available, let's say at proof wiki 
  \<^url>\<open>https://proofwiki.org/wiki/Extended_Euclidean_Algorithm#google_vignette\<close>.\<close>

subsection \<open>Tasks\<close>

text \<open>
  \<^enum> Replace the definition of gcdExt below by one resembling the extended Euclidean algorithm 
    such that for gcdExt(a,b) = (l,m,n) the Bézout identity l = ma + nb holds.
  \<^enum> Poof the lemmas stated below.
  \<^enum> Export the algorithm like in the case of the simple one
  \<close>

subsection \<open>Templates\<close>

definition gcdExt_task :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (int \<times> int))" ("gcdExt") where
  "gcdExt_task a b = (gcd a b, (0, 0))"

no_notation %solDel gcdExt_task ("gcdExt")

fun %solDel gcdExt :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (int \<times> int))" where
  "gcdExt a 0 = (a, (1, 0))" |  
  "gcdExt a b = (
      fst(gcdExt b (a mod b)), (
      snd (snd (gcdExt b (a mod b)))),
      (fst (snd ( gcdExt b (a mod b ))  ) - (a div b) * (snd (snd (gcdExt b (a mod b))))
    ))"

text \<open>Define abbreviations @{text "gcdExt\<^sub>1, gcdExt\<^sub>2, gcdExt\<^sub>3"} (\<^doc>\<open>prog-prove\<close>, 2.3.3) for the 
  values of @{text "gcdExt"}. Note that the consts/notation below serves as placeholders and can 
  be overwritten as shown with @{theory_text\<open>foo\<close>} \<close>

consts
  gcdExt_1_task :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  gcdExt_2_task :: "nat \<Rightarrow> nat \<Rightarrow> int"
  gcdExt_3_task :: "nat \<Rightarrow> nat \<Rightarrow> int"
  foo :: "nat \<Rightarrow> nat \<Rightarrow> int"

notation
  gcdExt_1_task ("gcdExt\<^sub>1") and
  gcdExt_2_task ("gcdExt\<^sub>2") and
  gcdExt_3_task ("gcdExt\<^sub>3") and
  foo ("fo")

no_notation %solDel foo ("fo")
abbreviation %solDel fo:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fo a b \<equiv> a + b"

no_notation %solDel gcdExt_1_task ("gcdExt\<^sub>1")
abbreviation %solDel gcdExt\<^sub>1:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcdExt\<^sub>1 a b \<equiv> fst(gcdExt a b)"

no_notation %solDel gcdExt_2_task ("gcdExt\<^sub>2")
abbreviation %solDel gcdExt\<^sub>2:: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "gcdExt\<^sub>2 a b \<equiv> fst(snd(gcdExt a b))"

no_notation %solDel gcdExt_3_task ("gcdExt\<^sub>3")
abbreviation %solDel gcdExt\<^sub>3:: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "gcdExt\<^sub>3 a b \<equiv> snd(snd(gcdExt a b))"

text \<open>Discuss: Why is it more convenient to use abbreviations in place of definitions at this point?\<close>

lemma gcd_extension: "gcd a b = gcdExt\<^sub>1 a b"
  apply %sol (induction a b rule:gcd.induct)
   apply %sol (auto)[1]
  by %sol simp

lemma "a*(b+c) = a*b + a*c" for a b c::int
  oops

lemma %solDel gcd_Bezout_lem: " int (gcdExt\<^sub>1 (Suc v) (a mod Suc v)) 
        =
           (gcdExt\<^sub>2 (Suc v) (a mod Suc v)) * int (Suc v) 
          + (gcdExt\<^sub>3 (Suc v) (a mod Suc v)) * int (a mod Suc v)
   \<Longrightarrow>
           int (gcdExt\<^sub>1 a (Suc v)) 
        =
           (gcdExt\<^sub>2 a (Suc v)) * int a + (gcdExt\<^sub>3 a (Suc v)) * int (Suc v)"
  (is "?IH_L = ?IH_R \<Longrightarrow> ?IS_L = ?IS_R") for a v :: nat
proof -
  let ?v="Suc v"
  assume IH:"?IH_L = ?IH_R"
  have 
    " (gcdExt\<^sub>3 ?v (a mod ?v)) * int (a mod ?v) = (gcdExt\<^sub>3 ?v (a mod ?v)) * int( a - (a div ?v)*?v )"
    unfolding modulo_nat_def by simp
  also have
    "... = (gcdExt\<^sub>3 ?v (a mod ?v)) * (int(a) - (a div ?v)*?v )"
    by (metis minus_div_mult_eq_mod of_nat_mult zdiv_int zmod_int)  
  also have       
    " ... =  (gcdExt\<^sub>3 ?v (a mod ?v)) * int(a) - (gcdExt\<^sub>3 ?v (a mod ?v)) * (a div ?v)*?v "
    by (simp add: int_distrib(2,4)) 
  also have 
    "... + (gcdExt\<^sub>2 ?v (a mod ?v)) * int ?v = ?IS_R" 
    using  int_distrib(3)  zdiv_int by fastforce
  finally have
    "(gcdExt\<^sub>3 ?v (a mod ?v)) * int (a mod ?v) +(gcdExt\<^sub>2 ?v (a mod ?v)) * int ?v = ?IS_R"
    by blast
  moreover have " int (gcdExt\<^sub>1 a ?v) = int (gcdExt\<^sub>1 ?v (a mod ?v) ) " 
    by simp
  ultimately show "?IS_L = ?IS_R"  
    using IH by presburger
qed

theorem gcd_Bezout: "fst(gcdExt a b) = (fst (snd (gcdExt a b)))*a + (snd (snd (gcdExt a b)))*b  "
  text \<open>Hint: Transform the induction step to an own lemma\<close>
  apply %sol (induction  rule: gcdExt.induct)
   apply %sol auto[1]
using %sol gcd_Bezout_lem by %sol fast


section \<open>Lowest common multiple\<close>

fun lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lcm a b = a*b div (gcd a b) "

lemma lcm_divided_by_first: "a divides lcm a b"
proof %sol -
  obtain b' where 2:"b = b' * gcd a b" 
    using gcd_divides_both mult.commute unfolding divides_def by metis
  hence "a * b = a * b' * gcd a b" 
    by simp
  hence " (a * b) div (gcd a b) = (a * b' * gcd a b)  div (gcd a b) " 
    by argo
  hence "lcm a b = (a * b' * gcd a b)  div (gcd a b)" 
    by simp
  hence "lcm a b = a * b'" using "2" 
    by fastforce
  thus ?thesis unfolding divides_def by simp
qed

proposition lcm_sym:"lcm a b = lcm b a"
proof %sol -
  have "a*b = b* a" and "gcd a b = gcd b a" using gcd_sym by auto
  thus ?thesis using lcm.elims by metis
qed

theorem lcm_divided_by_both: "(a divides lcm a b) \<and> (b divides lcm a b)"
  using %sol lcm_sym lcm_divided_by_first by %sol metis

end

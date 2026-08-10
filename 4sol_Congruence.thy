theory "4sol_Congruence"
  imports Main HOL.Equiv_Relations
begin

chapter \<open>Group 4: Fermat’s Little Theorem using binomial coefficients\<close>

section \<open>Informal introduction and instructions\<close>

text \<open>This project comprises the current file together with 4sol_LittleFermat.thy, which continues 
  the current file.\<close>

text \<open>Subject of this project is 
  \<^item> to proof little Fermat's theorem in an elementary way and
  \<^item> thereby to develop some elementary notions from number theory like divisibility and congruence
  \<^item> and the concept of equivalence relation;
  \<^item> to practise induction extensively;
  \<^item> to apply binomial coefficients and sums over sets.
  
  In project 7 a more theoretic roote via the theory of groups will be taken. 
  It should be remarked that actually the path taken in this projects generalizes in another way.
  Namely that for an @{text "\<bbbF>\<^sub>p"}-algebra a map @{text "x \<mapsto> x\<^sup>p"} constitutes an automorphism.
  Potentially, this will be explained in an excursion during the course.
  This is to say, your are neither supposed to understand nor trying to understand the penultimate
  sentence.\<close>

subsection \<open>Tasks\<close>

text \<open>
  \<^enum> Replace the sorry below by a proof. 
    Remark: This will include adding additional lemmas
  In your presentation:
  \<^enum> Provide the course with an informal understanding of the concept of an equivalence relation.
    Discuss to this end informally examples especially from high school mathematics, e.g.
    \<^item> congruent geometry, 
    \<^item> similarity geometry (germ. Ähnlichkeitsgeometrie)
    \<^item> components of a graph (optional).
  \<^enum> Present the formal definition of equivalence relation from \<^file>\<open>~~/src/HOL/Equiv_Relations.thy\<close>.
  \<^enum> Outline the content of your project, how far you got and what you find challenging.
  \<^enum> Present around 3 exercise regarding the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance.
  \<close>


section \<open>Congruence\<close>

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<equiv> _ \<langle>_\<rangle>" [50]  40) where
  " (a \<equiv> b \<langle>n\<rangle>)  \<longleftrightarrow> ( \<exists> k ::nat. \<exists> l::nat. a + k*n = b + l*n  ) "

definition divides :: "nat \<Rightarrow> nat \<Rightarrow> bool" (infixl "divides" 60)  where
  "a divides b \<longleftrightarrow> (\<exists> k ::nat. a * k = b)"

inductive ispositive :: "nat \<Rightarrow> bool"("_ ispositive")  where
  ispositive1: "1 ispositive" |
  ispositiveSuc: "n ispositive \<Longrightarrow> (Suc n) ispositive"

definition\<^marker>\<open>tag important\<close> isprime :: "nat \<Rightarrow> bool" ("_ isprime") where
  "n isprime \<longleftrightarrow> (n \<noteq> 0 \<and> n \<noteq> 1  \<and> (\<forall> a b::nat. n divides a * b \<longrightarrow> (n divides a \<or> n divides b) ))"

section \<open>Equivalence relation\<close>


subsection \<open>Congruence is an equivalence relation \<close>

theorem congruence_sym [simp]:
  fixes a b n::nat
  assumes "a \<equiv> b \<langle>n\<rangle>"
  shows "b \<equiv> a \<langle>n\<rangle>"

  using %sol assms unfolding %sol congruent_def by %sol metis

theorem congruence_refl [simp]:
  fixes a n::nat
  shows "a \<equiv> a \<langle>n\<rangle>"
  unfolding %sol congruent_def by %sol simp

theorem congruence_trans [simp]:
  fixes a b c n::nat
  assumes "a \<equiv> b \<langle>n\<rangle>"
  assumes "b \<equiv> c \<langle>n\<rangle>"
  shows   "a \<equiv> c \<langle>n\<rangle>"
proof %sol -
  from assms obtain k l l' m ::nat where "a +  k*n = b + l*n" and "b + l'*n = c + m*n" 
    unfolding congruent_def by blast
  hence "a + (k+l')*n = c + (m + l)*n" by (simp add: distrib_right)
  thus ?thesis unfolding congruent_def by fast
qed
                                           
subsection \<open>Basic properties\<close>

lemma congruent_plus [simp]:
  fixes a b a' b' n::nat
  assumes "a \<equiv> b  \<langle>n\<rangle>"
  assumes "a' \<equiv> b' \<langle>n\<rangle>"
  shows "a+a' \<equiv> b+b' \<langle>n\<rangle>"
proof %sol -
  from assms obtain k l k' l' ::nat where "a +  k*n = b + l*n" and "a' + k'*n = b' + l'*n" 
    unfolding congruent_def by blast
  hence "a + a' + (k+k')*n = b + b' + (l+l')*n" by (simp only: distrib_right)
  thus ?thesis unfolding congruent_def by blast
qed

lemma congruent_mult [simp]:
  fixes a b a' b' n::nat
  assumes "a \<equiv> b \<langle>n\<rangle>"
  assumes "a' \<equiv> b' \<langle>n\<rangle>"
  shows "a*a' \<equiv> b*b' \<langle>n\<rangle>"
proof %sol -
  from assms obtain k l k' l' ::nat where "a +  k*n = b + l*n" and "a' + k'*n = b' + l'*n" 
    unfolding congruent_def by blast
  hence "(a +  k*n)*(a' + k'*n) = (b + l*n)*(b' + l'*n)" by simp

  hence %sol "a*a' + ((a*k'+a'*k)*n  + (k*k')*n*n) = b*b' + ((b*l'+b'*l)*n  + (l*l')*n*n)" 
    by %solDel (simp add: algebra_simps)
  then %sol show ?thesis unfolding %sol congruent_def by %sol (metis add_mult_distrib)
qed

lemma %sol congruent_multiple:
  fixes n N::nat
  shows "N*n \<equiv> 0 \<langle>n\<rangle>"
  using %sol add_0 add_mult_distrib unfolding %sol congruent_def by %sol metis

lemma congruent_add_l[simp]:
  fixes a b n N::nat
  assumes "a + N*n \<equiv> b \<langle>n\<rangle>"
  shows "a \<equiv> b \<langle>n\<rangle>"
  using %sol assms congruent_mult congruent_multiple congruent_def
    add.assoc add_mult_distrib by %sol metis

lemma congruent_add_r[simp]:
  fixes a b n N::nat
  assumes "a \<equiv> (b + N*n) \<langle>n\<rangle>"
  shows "a \<equiv> b \<langle>n\<rangle>"
  using %sol congruent_add_l congruence_sym assms by %sol blast

corollary congruent_divides_r[simp]:
  fixes a b n N::nat
  assumes "a \<equiv> (b + N) \<langle>n\<rangle>"
  assumes "n divides N"
  shows "a \<equiv> b \<langle>n\<rangle>"
  using %sol congruent_add_r assms unfolding %sol divides_def by %sol (metis mult.commute)

corollary congruent_divides_l[simp]:
  fixes a b n N::nat
  assumes "(a + N) \<equiv> b \<langle>n\<rangle>"
  assumes "n divides N"
  shows "a \<equiv> b \<langle>n\<rangle>"
  using %sol congruent_divides_r congruence_sym assms by %sol blast

section \<open>Basic properties of primes\<close>

lemma ispositive_rel:
  fixes n::nat
  shows "n ispositive \<longleftrightarrow> n > 0"
  by %sol (metis gr0_conv_Suc ispositive.simps nat_1 nat_induct_non_zero nat_one_as_int)

lemma divides_refl[simp]:
  fixes a::nat
  shows "a divides a"
  using %sol mult.right_neutral unfolding %sol divides_def by %sol blast

lemma divides_plus:
  fixes n a b::nat
  assumes "n divides a" and "n divides b"
  shows "n divides (a + b)"
  using %sol assms unfolding %sol divides_def by %sol (metis add_mult_distrib2)

lemma divides_sum:
  fixes n::nat
  fixes D::"nat set"
  shows "finite D \<Longrightarrow>\<forall> i\<in> D. n divides f(i) \<Longrightarrow> n divides( sum f D)"
text %sol \<open>Use induction rule @{thm finite.induct}. This rule defines a finite set by adding elements.
  In the proof of the induction step, distinguish the cases that the added element is already 
  contained in the set that it isn't.\<close>
proof %sol2 (induction rule:finite.induct)
  case emptyI
  have "sum f {} = 0" by simp
  then show ?case unfolding divides_def by auto
next
  case (insertI A a)
  from  \<open>\<forall>i \<in> insert a A. n divides f i\<close> have "\<forall> i \<in> A. n divides f(i)" by auto
  hence assumption1:"n divides sum f A" using \<open>\<forall>i\<in>A. n divides f i \<Longrightarrow> n divides sum f A\<close> by metis
  from  \<open>\<forall>i \<in> insert a A. n divides f i\<close> have assumption2: "n divides f(a)" by simp
  show ?case
  proof cases
    assume "a \<in> A"
    hence "A = (insert a A)" by auto
    thus ?thesis using \<open>n divides sum f A\<close> by simp
  next
    assume "a \<notin> A"
    hence step:"sum f (insert a A) = (sum f A) + f(a)" by (simp add: insertI.hyps)
    then show ?thesis
        using assumption1 assumption2 divides_plus[of n "sum f A" "f(a)"] by presburger
    qed
qed

lemma divides_mult:
  fixes n a N::nat
  assumes "n divides a"
  shows "n divides a*N"
  using %sol assms unfolding %sol divides_def by %sol auto


text \<open>The next result will be crucial for us\<close>

lemma divides_witness:
  fixes n m::nat
  assumes "n divides m"
  assumes "m > 0"
  shows "\<exists> k ::nat. n * k = m \<and> k \<noteq> 0"
proof %sol -
  from assms(1) obtain k where "m = n*k" unfolding divides_def by auto
  moreover
  have " k \<noteq> 0"
  proof %sol
      assume "k=0"
      hence "m=0" using \<open>m = n*k\<close> by auto
      thus "False" using assms(2) by simp
    qed
  ultimately show "\<exists>k. n * k = m \<and> k \<noteq> 0" using \<open>m = n*k\<close> by auto
qed

lemma %sol divides_impl_congruence:
  fixes n m::nat
  assumes "n divides m"
  shows "0 \<equiv> m \<langle>n\<rangle>"
proof%sol -
  obtain k::nat where "n * k = m " using assms divides_def by blast
  hence "0 + k * n = m + 0 * n" by auto
  thus ?thesis unfolding congruent_def by blast
qed

lemma %sol mult_incr:
  fixes m n k::nat
  shows "(m = n*k \<and> k > 0) \<longrightarrow> m \<ge> n"
  apply %sol2 (induct k arbitrary:n m) 
  by %sol2 simp_all

lemma notDivides:
  fixes n m::nat
  assumes "n < m"
  assumes "n \<noteq> 0 "
  shows " \<not>(m divides n)"
  text %sol1 \<open>Idea: Induction over n.\<close>
proof %sol2
  assume "m divides n"
  show "False" 
  proof (cases n)
    case 0
    then show "False" using assms by auto
  next
    case (Suc nat)
    hence "\<exists> k ::nat. m * k = n \<and> k \<noteq> 0" using \<open>m divides n\<close> divides_witness by auto
    hence "m \<le> n" using mult_incr by auto
    thus ?thesis using assms by auto
  qed
qed


end
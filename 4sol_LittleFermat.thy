theory "4sol_LittleFermat"
  imports Main "4sol_Congruence"

begin


section \<open>Little Fermat's Theorem\<close>

text \<open>For an elementary proof of little Fermat's theorem the next lemma on the binomial coefficient 
  is the key\<close>

subsection \<open>The factorial\<close>

proposition fact_divides:
  fixes n::nat
  shows "n = 0 \<or> n divides fact n"
  apply %sol (induct n)
   apply %sol simp
  using %sol of_nat_eq_iff unfolding %sol divides_def by %sol auto

lemma %solDel fact_notDivides_lemLem:
  fixes p n::nat
  assumes "p isprime"
  assumes "p divides fact (Suc n)"
  shows "(p divides Suc n)\<or>(p divides fact n)"
proof %sol -
  have "fact(Suc n) = (Suc n)*fact n " by simp
  with assms show "?thesis" unfolding isprime_def by auto
qed

lemma %sol fact_notDivides_lem:
  fixes p n::nat
  shows "n ispositive \<Longrightarrow> (p isprime \<and> p divides fact n) \<Longrightarrow> \<exists> k\<in>{1..n}. p divides k"
  text \<open>Hint: Induction over positive numbers\<close>
proof %sol (induction rule: ispositive.induct)
  case ispositive1 
  hence "False" unfolding isprime_def divides_def by auto
  thus ?case by auto
next
  case (ispositiveSuc n)
  hence "(p divides Suc n)\<or>(p divides fact n)" using fact_notDivides_lemLem[of p n] by blast
  hence "(p divides Suc n)\<or>(\<exists>a\<in>{1..n}. p divides a)" using ispositiveSuc by blast
  then show ?case by auto
qed

proposition fact_notDivides:
  fixes p n::nat
  assumes "p isprime"
  assumes "p > n"
  shows "\<not> p divides fact n"
  text %sol \<open>Hint: Distinguish positive and non-positive cases.\<close>
proof %sol2 cases
  assume "n ispositive"
  show ?thesis
  proof
    have "p \<noteq> 0 " using \<open>p isprime\<close> unfolding isprime_def by metis
    assume "p divides fact n"
    then obtain k::nat where "p divides k" and "k \<in> {1..n} "
      using fact_notDivides_lem[of n p] \<open>p isprime\<close> \<open>n ispositive\<close> by auto
    thus "False" using notDivides \<open>p > n\<close> \<open>p \<noteq> 0\<close> by simp
  qed
  next
    assume "\<not>(n ispositive)"
    then have 1:"n=0" by (metis ispositive1 ispositiveSuc nat_induct_non_zero not_gr_zero)
    have 2:"p > 1" using \<open>p isprime\<close> unfolding isprime_def by simp
    from 1 2 show ?thesis using notDivides by auto
qed

subsection \<open>The binomial\<close>

lemma binomialCoeff_divisible:
  fixes p k::nat
  assumes "p isprime"
  assumes "k ispositive" and "k < p"
  shows "p divides (p choose k) "

  text \<open>To proof this lemma look up the function choose by pressing Ctrl and clicking on the 
  function "choose" in the code above. You will jump to a file with its definition. 
  Scan this file for a useful lemmas to prove the lemma. 
  If you don't get along with this instruction ask the instructor for a hint\<close>

  text %sol \<open>Hint: binomial_fact_lemma[of k p]\<close>
proof %sol2 -
  from \<open>k ispositive\<close> have "p - k < p" using ispositive_rel[of k] assms(3) by auto
  have 1:"fact k * fact (p - k) * (p choose k) = fact p" 
    using assms(2) binomial_fact_lemma[of k p] by (simp add: assms(3) less_or_eq_imp_le)
  hence "p divides (fact k * fact (p - k)) \<or> p divides (p choose k)"
    using fact_divides \<open>k ispositive\<close> assms(1) unfolding isprime_def by metis
  thus "p divides (p choose k)" 
    using \<open>p isprime\<close>  isprime_def
    by (meson \<open>p - k < p\<close> \<open>k<p\<close> fact_notDivides)
qed

lemma "freshman's dream":
  fixes p a b::nat
  assumes "p isprime "
  shows "((a+b)^p) \<equiv> (a^p + b^p ) \<langle>p\<rangle>"
proof -
  from assms have "p \<ge> 2" unfolding isprime_def by simp
  hence decomp:"{0..p} = {0} \<union> {0<..<p} \<union> {p}" by auto
  have %solDel "(a+b)^p = (\<Sum>k\<le>p. (p choose k) * a^k * b^(p-k))" using binomial by auto                                                   
    also %solDel have %solDel "... = (\<Sum>k\<in>{0..p}. (p choose k) * a^k * b^(p-k))"  using atMost_atLeast0 by fastforce
    also %solDel have %solDel "... = (p choose 0) * a^0 * b^(p-0) + (p choose p) * a^p * b^(p-p) 
                      + (\<Sum>k\<in>{0<..<p}. (p choose k) * a^k * b^(p-k)) " 
      using \<open>p \<ge> 2\<close> decomp by (simp add: atMost_atLeast0 field_simps)
    also %solDel have %solDel "... = a^p + b^p + (\<Sum>k\<in>{0<..<p}. (p choose k) * a^k * b^(p-k))" by simp
  finally %solDel
  have 1:"(a+b)^p = a^p + b^p + (\<Sum>k\<in>{0<..<p}. (p choose k) * a^k * b^(p-k))" 
    (is "?A = ?B + ?C")
  . %sol
  text \<open>for the step above "have ... also have ... finally have ..." from \<^doc>\<open>prog-prove\<close>, \\<section> 4.2.2, makes sense.\<close>
  have %solDel "\<forall> k\<in>{0<..<p}. (k ispositive) \<and> k < p" by (simp add: ispositive_rel)
    hence %solDel "\<forall> k\<in>{0<..<p}. p divides (p choose k)" using  \<open>p isprime\<close> binomialCoeff_divisible by blast
    hence %solDel "\<forall> k\<in>{0<..<p}. p divides (p choose k) * a^k * b^(p-k)" using divides_mult by simp
    hence %solDel "p divides (sum (\<lambda> k.(p choose k) * a^k * b^(p-k)) {0<..<p})"
      using divides_sum[of "{0<..<p}" p "\<lambda> k.(p choose k) * a^k * b^(p-k)"]  by blast
  then %solDel
  have "p divides ?C" 
    by %sol simp
  with 1 show "?A \<equiv> ?B \<langle>p\<rangle> " using congruent_divides_r[of "?A" "?B" "?C" p] 
      congruence_refl by metis 
qed

subsection \<open>The little Fermat Theorem\<close>

theorem littleFermat: 
  fixes p::nat 
  fixes n::nat  
  assumes "p isprime"
  shows " (n^p) \<equiv> n \<langle>p\<rangle> "
  text %sol \<open>Hint: induction over n\<close>
proof %sol2 (induction n)
  case 0
  have "0 < p" using assms unfolding isprime_def by simp
  thus ?case using zero_power congruence_refl  by metis
next
  case (Suc n)
  assume "congruent (n ^ p) n p"
  hence step:"congruent (n ^ p + 1) (n+ 1) p" using  congruent_plus congruence_refl by blast
  from "freshman's dream" have "congruent (Suc n ^ p) (n^p + 1) p" 
    using assms by (metis Suc_eq_plus1 power_one)
  thus ?case using step congruence_trans Suc_eq_plus1 by metis
qed

corollary littleFermat_prime:
  fixes p::nat 
  fixes n::nat  
  assumes "p isprime" and "\<not> p divides n"
  shows " (n^(p-1)) \<equiv> 1 \<langle>p\<rangle> "
proof %sol -
  from assms(2) have "n > 0" unfolding divides_def by fastforce
  hence "n^(p-1)> 0" by simp
  have "p \<noteq> 0" using assms(1) unfolding isprime_def by simp
  have " n^p \<equiv> n \<langle>p\<rangle> " using littleFermat assms(1) by blast
  then obtain "k'" "l'" :: nat 
    where littleFermat:"n^p + k'*p = n + l'*p" 
      using congruent_def by fast
  obtain m::nat 
    where " (n^ (p - 1)) \<equiv> Suc m  \<langle>p\<rangle>"
    using congruence_refl \<open>n^(p-1)> 0\<close> Suc_diff_1 by metis
  hence %solDel " n*(n^ (p - 1)) \<equiv> n*(Suc m) \<langle>p\<rangle> " using congruence_refl congruent_mult by presburger
  hence %solDel " n^p \<equiv> n*(Suc m) \<langle>p\<rangle>" using  power_eq_if \<open>p \<noteq> 0\<close> by metis
  then %solDel obtain %solDel k l::nat where " n^p + k*p = n*(Suc m) + l*p " unfolding congruent_def by blast
  with %solDel littleFermat have %solDel " n + l'*p + k*p = n*(Suc m) + l*p + k'*p " by simp
  hence %solDel " l'*p + k*p = n*m + l*p + k'*p " by auto
  hence %solDel " (l' + k)*p = n*m + (l + k')*p " by algebra
  hence %solDel "p divides n*m" unfolding divides_def 
    using add_diff_cancel_right' mult.commute right_diff_distrib' by metis
  with %solDel \<open>p isprime\<close> \<open>\<not> p divides n\<close> have %solDel "p divides m" using isprime_def by auto
  hence %solDel "0 \<equiv> m \<langle>p\<rangle>" using divides_impl_congruence by blast
  hence %solDel "1 \<equiv> Suc m \<langle>p\<rangle>"  by (metis One_nat_def congruence_refl congruent_plus plus_1_eq_Suc)
  with %solDel \<open> (n^ (p - 1)) \<equiv> Suc m  \<langle>p\<rangle> \<close>
  show ?thesis 
    using %sol congruence_trans congruence_sym by %sol blast
qed
  
end

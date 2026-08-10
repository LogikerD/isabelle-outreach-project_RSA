theory "7sol_Lagrange"
  imports Main "HOL-Algebra.Group" HOL.Groups HOL.Nat "4sol_Congruence"


begin

chapter \<open>Group 7: Lagrange’s Theorem and Fermat’s Little Theorem as a corollary\<close>
                                                                                                    
section \<open>Informal introduction and instructions\<close>

text \<open>Aim of thiproves project is to
  \<^enum>  the Lagrange theorem
  \<^enum> derive the Little Fermat's theorem as a corollary
  \<^enum> doing so, to familiarise oneself with the following tools
    \<^enum> records, a kind on enhanced product type
    \<^enum> locales
  Note that the aim of Project 4 is to prove Little Fermat's theorem on a different route.
  Both project share common definitions and lemmas that are found in 4sol_Congruence.thy, which can 
  be used without proof in this project.
  Actually, both approaches generalize in different ways, as may be discussed in an excursion during 
  the course.\<close>

text\<open>References
  \<^item> \<section> 8.3 - 8.3.2, Tobias Nipkow, Lawrence C. Paulson, and Markus Wenzel
    \<^emph>\<open>Isabelle/HOL: A Proof Assistant for Higher-Order Logic\<close> 2024
  \<^item> \<section> 1 - 2.1, \<^doc>\<open>locales\<close>
  \<^item> \<section> 9, B. L. van der Waerden \<^emph>\<open>Algebra\<close> 1955
  
  If you want some spare time reading on historical backgrounds you may have a look at
  \<^item> Saunders Mac Lane \<^emph>\<open>Van der Waerden's Modern Algebra\<close> 1997
\<close>

subsection \<open>Group theory\<close>

text \<open>This project presupposes a basic understanding of what a group is.

  A group is an abstraction of many concepts like addition, multiplication and symmetries of 
  geometrical object.
  Examples encompass congruence (germ. Kongruenz), similarity (germ. Ähnlichkeit). 
  The notion is based on a binary operation, let's denote it by \<otimes>, i.e. taking two element x and y 
    to another element x \<otimes> y.
  
  The set from which these elements are taken is called the carrier. An even more basic concept than 
  a group is a monoid. 
  Besides its carrier set a monoid consists of just a neutral element \<one> and a binary 
  operation \<otimes>—often called multiplication—, subject to the axioms

   \<one> \<otimes> x  = x \<otimes> \<one> = x  for all x in the carrier
   x \<otimes> (y \<otimes> )z =  (x \<otimes> )y \<otimes> z  for all x, y, z in the carrier.

  For a group we also have an inverse for each element x in the carrier.
  The inverse is denoted by @{text "inv x"} in Isabelle, while x\<inverse> is most often used in standard 
  mathematics).

  Immediately, one can verify that addition provides a group structure on the integers or also the 
  rational or real numbers. 
  Multiplication can be viewed as a group structure on the rationals or real if one excludes 0.

  For understanding the structure of groups, the concept of a subgroup is crucial. 
  A subgroup is formed by a subset of the carrier such that it contains \<one> and the operations \<otimes> and 
  inv restrict to it. 
  As an example one may take the rationals inside the reals.

  For a rigorous introduction in the classical sense consult:
  \<^item> \<section> 9 in B. L. van der Waerden \<^emph>\<open>Algebra\<close> 1955
  \<^item> Any of the numerous script in the topic in the internet.
  Note that in Project 6 they concerns themselves with the fundamentals of group theory.
  So you may approach them as well.\<close>

subsection \<open>Tasks\<close>

text \<open>
  \<^enum> Replace the sorry below by a proof. 
    Remark: This may include adding additional lemmas
  In your presentation:
  \<^enum> Provide the course with an informal understanding of the new concepts like subgroup (if not done 
    so by project 6, consult!).
  \<^enum> Outline the content of your project, how far you got and what you find challenging.
  \<^enum> Present around 3 exercise regarding the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance. 
  \<close>

subsection \<open>Remarks\<close>

text \<open>
  The aim of this project is to establish the Lagrange theorem in the case of finite groups and 
  derive the little Fermat's theorem as a corollary.

  As you can see above, the theory Group is already included. 
  So you are at liberty to use all theorems established in this theory. 
  You can either search this theory manually (Ctrl + click on the theory) or use sledgehammer to 
  find suitable theorems automatically. 
  A useful strategy is often to think about what could already be proven and then ask sledgehammer 
  to prove it.

  Here a short summary on how groups are build in Isabelle in \<^file>\<open>~~/src/HOL/Groups.thy\<close>:
  First, a record monoid is defined which comprises
  \<^enum> a carrier, i.e. a set of elements of type 'a
  \<^enum> a multiplication, i.e. a an operation of type carrier \<times> carrier \<rightarrow> carrier
  \<^enum> a unit element e.
  Second, the set of (two-sided) unit elements (i.e. elements x with an inverse x\<inverse> such that x x\<inverse> 
  = x\<inverse> x = e) is defined.
  Finally, a locale group is defined which assumes, that all elements in carrier are units.
\<close>
  

section \<open>Preparation\<close>

definition
  r_coset    :: "[_, 'a set, 'a] \<Rightarrow> 'a set"    (infixl "#>\<index>" 60)
  where "H #>\<^bsub>G\<^esub> a = (\<Union>h\<in>H. {h \<otimes>\<^bsub>G\<^esub> a})"

definition
  RCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   ("rcosets\<index> _" [81] 80)
  where "rcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a})"

definition
  order :: "('a, 'b) monoid_scheme \<Rightarrow> nat"
  where "order S = card (carrier S)"

lemma (in group) rcos_equation:
  assumes "subgroup H G"
  assumes p: "ha \<otimes> a = h \<otimes> b" "a \<in> carrier G" "b \<in> carrier G" "h \<in> H" "ha \<in> H" "hb \<in> H"
  shows "hb \<otimes> a \<in> (\<Union>h\<in>H. {h \<otimes> b})"
proof -
  interpret subgroup H G by fact
  from p show ?thesis 
  (*solution*)
    by (rule_tac UN_I [of "hb \<otimes> ((inv ha) \<otimes> h)"]) (auto simp: inv_solve_left m_assoc)
  (*/solution*)
qed

lemma (in group) rcos_disjoint:
  assumes "subgroup H G"
  shows "pairwise disjnt (rcosets H)"
proof -
  interpret subgroup H G by fact
  show ?thesis
    unfolding RCOSETS_def r_coset_def pairwise_def disjnt_def
    by (blast intro: rcos_equation assms sym)
qed

lemma (in group) rcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(rcosets H) = carrier G"
proof -
  interpret subgroup H G by fact
  show ?thesis
  (*solution*)
    unfolding RCOSETS_def r_coset_def by auto
  (*/solution*)
qed

section \<open>Satz von Lagrange\<close>

lemma (in group) inj_on_g:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> a) H"
using subsetD unfolding inj_on_def by force

lemma (in group) card_cosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "\<exists>f. bij_betw f H R"
(*solution*)
proof -
  obtain g where g: "g \<in> carrier G" "R = H #> g"
    using assms(1) unfolding RCOSETS_def by blast

  let ?f = "\<lambda>h. h \<otimes> g"
  have "\<And>r. r \<in> R \<Longrightarrow> \<exists>h \<in> H. ?f h = r"
  proof -
    fix r assume "r \<in> R"
    then obtain h where "h \<in> H" "r = h \<otimes> g"
      using g unfolding r_coset_def by blast
    thus "\<exists>h \<in> H. ?f h = r" by blast
  qed
  hence "R \<subseteq> ?f ` H" by blast
  moreover have "?f ` H \<subseteq> R"
    using g unfolding r_coset_def by blast
  ultimately show ?thesis using inj_on_g unfolding bij_betw_def
    using assms(2) g(1) by auto
qed
(*/solution*)

corollary (in group) card_rcosets_equal:
  assumes "R \<in> rcosets H" "H \<subseteq> carrier G"
  shows "card H = card R"
(*solution*)
  using card_cosets_equal assms bij_betw_same_card by blast
(*/solution*)

proposition (in group) lagrange_finite:
  assumes "finite(carrier G)" and HG: "subgroup H G"
  shows "card(rcosets H) * card(H) = order(G)"
proof -
  have "card H * card (rcosets H) = card (\<Union>(rcosets H))"
    text \<open>Hint: use @{thm card_partition}\<close>
  (*solution*)
  proof (rule card_partition)
      show "\<And>c1 c2. \<lbrakk>c1 \<in> rcosets H; c2 \<in> rcosets H; c1 \<noteq> c2\<rbrakk> \<Longrightarrow> c1 \<inter> c2 = {}"
        using HG rcos_disjoint unfolding pairwise_def disjnt_def by auto
  qed (auto simp: assms finite_UnionD rcosets_part_G card_rcosets_equal subgroup.subset)
  (*/solution*)
  then show ?thesis
    using HG mult.commute rcosets_part_G order_def by metis
qed

section \<open>Little Fermat theorem as corollary\<close>

text \<open>Link to Project 4:
  The definitions used in Project 4 are imported from
\<^file>\<open>4sol_Congruence.thy\<close>.\<close>

text \<open>Tasks:
  \<^item> Define a monoid structure on (\<Z>\<div> n) without the 0-class and * as multiplication.
  \<^item> show that this is well-defined as a monoid
  \<^item> show that it is a group in case n is a prime (see definition isprime)\<close>

text \<open>Hints: 
  \<^item> Hint: Formalize \<^url>\<open>https://proofwiki.org/wiki/Fermat%27s_Little_Theorem/Proof_3\<close>
  \<^item> make a skeleton(outline first
 \<close>

text \<open>Try to get as far as you can. Good luck!\<close>

subsection \<open>The additive group of the quotient\<close>

text \<open>Consider the additive monoid of integers\<close>

definition int_monoid :: "int monoid" ("\<Z>")
  where "\<Z> \<equiv> \<lparr>carrier = UNIV, mult = (+), one = 0\<rparr>"

text \<open>with its cosets\<close>

definition int_submonoid :: "int \<Rightarrow> (int set)" ("\<Z>\<cdot>_" [100])
  where "\<Z>\<cdot>p \<equiv> { m. (\<exists> n::int. m = p * n) } "

abbreviation int_monoid_coset :: "int \<Rightarrow> int \<Rightarrow> int set" ("\<Z>_\<cdot>_" 60)
  where "int_monoid_coset p n \<equiv> (\<Z>\<cdot>p) #>\<^bsub>\<Z>\<^esub> n"

text \<open>and its set of cosets\<close>

definition int_monoid_COSETS :: "int \<Rightarrow> (int set set)" ("\<Z>\<div>_")
  where "\<Z>\<div> p \<equiv> rcosets\<^bsub>\<Z>\<^esub> (\<Z>\<cdot>p)"

text \<open>Observe that these cosets form a monoid under multiplication:\<close>

(*solution replacement=""*)
text \<open>Adapt def. FactGroup from \<^file>\<open>~~/src/HOL/Algebra/Coset.thy\<close> \<close>
(*/solution*)

definition
  int_set_mult  :: "[int set, int set] \<Rightarrow> int set" (infixl "\<^bold>+" 58)
  where "U \<^bold>+ V  = (\<Union>u\<in>U. \<Union>v\<in>V. {u + v})"

lemma int_set_mult_var: "U \<^bold>+ V  = (\<Union>u\<in>U. \<Union>v\<in>V. {u \<otimes>\<^bsub>\<Z>\<^esub> v})"
(*solution*)
  using monoid.select_convs(1) unfolding int_set_mult_def int_monoid_def by metis
(*/solution*)

definition mod_group :: "int \<Rightarrow> ((int set) monoid)"
  where "(mod_group n) = \<lparr> carrier = (\<Z>\<div> n), mult = int_set_mult, one = \<Z>\<cdot>n \<rparr>"

abbreviation mod_group_one :: "int \<Rightarrow> int set" ("\<one>\<^sub>_" [1000] ) where
  "\<one>\<^sub>n \<equiv> \<one>\<^bsub>mod_group n\<^esub>"

abbreviation mod_group_mult :: "int set \<Rightarrow> int \<Rightarrow> int set \<Rightarrow> int set"
    ("_ \<otimes>\<^sub>_ _" [70, 1000, 71] 70) where
  "x \<otimes>\<^sub>n y \<equiv> x \<otimes>\<^bsub>mod_group n\<^esub> y"


(*solution replacement=""*)
lemma "0 \<in> (\<Z>\<cdot>p)"
proof -
  have "p * 0 \<in> \<Z>\<cdot>p" unfolding int_submonoid_def by blast
  thus ?thesis by simp
qed
(*/solution*)

lemma rcosets_explicitly: "m \<in> U #>\<^bsub>G\<^esub> k \<Longrightarrow> \<exists> l\<in> U.  m = l \<otimes>\<^bsub>G\<^esub> k"
(*solution*)
unfolding r_coset_def by simp
(*/solution*)

(*solution replacement=""*)
lemma int_rcoset_representation:"m \<in> (\<Z> n \<cdot> k) \<Longrightarrow> \<exists> l. m = n*l + k"
proof -
  assume "m \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k"
  then obtain N::int where "N \<in> (\<Z>\<cdot>n)" and 1:"m = N + k"
    using rcosets_explicitly[of m "\<Z>" "(\<Z>\<cdot>n)" k] unfolding int_monoid_def
    by (metis monoid.select_convs(1))
  from \<open>N \<in> (\<Z>\<cdot>n)\<close> obtain l::int where 2:"N = n*l"
    unfolding int_submonoid_def by auto
  from 1 2 show ?thesis by auto
qed
(*/solution*)


lemma int_rcoset_incl:
  fixes n l k::int
  shows "n*l + k \<in> (\<Z> n \<cdot> k)"
(*solution*)
proof -
  have "n*l \<in> (\<Z>\<cdot>n)" unfolding int_submonoid_def by simp
  hence " n*l \<otimes>\<^bsub>\<Z>\<^esub> k \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k"
    unfolding r_coset_def by fast
  thus ?thesis using monoid.select_convs(1) unfolding int_monoid_def by metis
qed
(*/solution*)

lemma int_rcoset_characterisation:"(\<Z> n \<cdot> k) = {m. \<exists> l. m = n*l + k}" (is "?Def = ?set")
(*solution*)
  using  int_rcoset_representation int_rcoset_incl by blast
(*/solution*)

lemma mod_group_unit [simp]:"(\<Z> n \<cdot> 0) = \<Z>\<cdot>n"
(*solution*)
  using int_rcoset_characterisation unfolding int_submonoid_def by simp
(*/solution*)

lemma rcos_sum:
  fixes n l k::int
  shows "(\<Z> n \<cdot> k) \<^bold>+ (\<Z> n \<cdot> l) = \<Z> n \<cdot> (k + l)" (is "?sum = ?class")
(*solution*)
proof
  show "?sum \<subseteq> ?class"
  proof
    fix m::int
    assume "m \<in> ?sum"
    from this obtain mk ml::int 
      where mk:"mk \<in> ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k)" and ml:"ml \<in> ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> l)" and m:"m = mk + ml"
      unfolding int_set_mult_def by blast
    from mk obtain lmk::int where "mk = n*lmk + k" using int_rcoset_characterisation by blast
    from ml obtain lml::int where "ml = n*lml + l" using int_rcoset_characterisation by blast
    from \<open>m = mk + ml\<close> \<open>mk = n*lmk + k\<close> \<open>ml = n*lml + l\<close> have "m = n*lmk + n*lml + k + l" by auto
    hence "m = n*(lmk + lml) + k + l" by algebra
    thus " m \<in> ?class" using int_rcoset_characterisation
      unfolding RCOSETS_def int_monoid_def by simp
  qed
  show "?class \<subseteq> ?sum"
  proof
    fix m::int
    assume "m \<in> ?class"
    from this int_rcoset_characterisation[of n "k+l"] obtain L::int where "m = n*L + (k+l)" by blast
    hence "m = (n*L + k) + (n*0 + l)" by algebra
    moreover have "n*L + k \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k" and "n*0 + l \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> l" 
      using int_rcoset_characterisation by auto
    ultimately show " m \<in> ?sum " using int_rcoset_characterisation
      unfolding int_set_mult_def RCOSETS_def int_monoid_def by blast
  qed
qed
(*/solution*)

lemma 
  assumes  "a \<in> carrier G"
  shows "{(H #>\<^bsub>G\<^esub> a)} \<subseteq> (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a} )"
  (*solution*)
    using assms by blast
  (*/solution*)

lemma mod_group_wellDefined : 
  assumes "U \<in> (\<Z>\<div> n)" "V \<in> (\<Z>\<div> n)"
  shows "(int_set_mult U V) \<in> (\<Z>\<div> n)"
(*solution*)
proof -
  from \<open>U \<in> (\<Z>\<div> n)\<close> obtain k::int where U:"U = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k" 
    unfolding int_monoid_COSETS_def RCOSETS_def by (smt (verit) UN_iff singletonD)
  from \<open>V \<in> (\<Z>\<div> n)\<close> obtain l::int where V:"V = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> l" 
    unfolding int_monoid_COSETS_def RCOSETS_def by (smt (verit) UN_iff singletonD)
  have "k \<in> carrier \<Z>" unfolding int_monoid_def by simp
  have "k \<in> UNIV" by blast
  moreover have "l \<in> UNIV" by blast
  ultimately have  "k+l \<in> UNIV" unfolding int_monoid_def by blast
  from this have 1:"k+l \<in> carrier \<Z>" unfolding int_monoid_def by simp
  have " U \<^bold>+ V = ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k) \<^bold>+ ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> l) " using U V by auto
  also have " ... = ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (k + l)) " using rcos_sum by auto
  also have " ... \<in> (\<Union>a\<in>carrier \<Z>. {(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> a} )" using 1 by blast
  finally show ?thesis unfolding int_monoid_COSETS_def RCOSETS_def by blast
qed
(*/solution*)

text \<open>Now we can check that mod_group n is actually a monoid\<close>

lemma mod_group_is_monoid: "monoid (mod_group n)"
(*solution*)
proof 
  show "\<And>x y. x \<in> carrier (mod_group n) \<Longrightarrow> y \<in> carrier (mod_group n) 
          \<Longrightarrow> x \<otimes>\<^bsub>mod_group n\<^esub> y \<in> carrier (mod_group n)"
    using mod_group_wellDefined unfolding mod_group_def by simp
  show "\<And>x y z. x \<in> carrier (mod_group n) \<Longrightarrow> y \<in> carrier (mod_group n) \<Longrightarrow> z \<in> carrier (mod_group n) 
          \<Longrightarrow> x \<otimes>\<^sub>n y \<otimes>\<^sub>n z = x \<otimes>\<^sub>n (y \<otimes>\<^sub>n z) " 
  proof
    show " \<And>x y z. x \<in> carrier (mod_group n) \<Longrightarrow> y \<in> carrier (mod_group n) \<Longrightarrow> z \<in> carrier (mod_group n) \<Longrightarrow> x \<otimes>\<^sub>n y \<otimes>\<^sub>n z \<subseteq> x \<otimes>\<^sub>n (y \<otimes>\<^sub>n z)"
    proof -
      fix x y z
      assume "x \<in> carrier (mod_group n)" and "y \<in> carrier (mod_group n)" and "z \<in> carrier (mod_group n)"
      show "x \<otimes>\<^sub>n y \<otimes>\<^sub>n z \<subseteq> x \<otimes>\<^sub>n (y \<otimes>\<^sub>n z)"
        unfolding mod_group_def int_set_mult_def by (simp add: add.assoc)
    qed
  next show "\<And>x y z. x \<in> carrier (mod_group n) \<Longrightarrow> y \<in> carrier (mod_group n) \<Longrightarrow> z \<in> carrier (mod_group n) \<Longrightarrow> x \<otimes>\<^sub>n (y \<otimes>\<^sub>n z) \<subseteq> x \<otimes>\<^sub>n y \<otimes>\<^sub>n z"
      proof -
      fix x y z
      assume "x \<in> carrier (mod_group n)" and "y \<in> carrier (mod_group n)" and "z \<in> carrier (mod_group n)"
      show " x \<otimes>\<^sub>n (y \<otimes>\<^sub>n z) \<subseteq> x \<otimes>\<^sub>n y \<otimes>\<^sub>n z"
        unfolding mod_group_def int_set_mult_def by (simp add: add.assoc)
    qed
  qed
  text\<open>Unfortunetelly, I did not find any way to use lemmas group.rcos_disjoint, etc. to reduce this proof to one inclusion.\<close>
                         
  show "\<one>\<^sub>n \<in> carrier (mod_group n)"
  proof -
    have "0 \<in> carrier \<Z>"
      unfolding int_monoid_def by simp
    hence "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> 0 \<in> (\<Z>\<div> n)"
      unfolding int_monoid_COSETS_def RCOSETS_def by blast
    thus ?thesis
      unfolding mod_group_def by simp
  qed

  show "\<And>x. x \<in> carrier (mod_group n) \<Longrightarrow> \<one>\<^sub>n \<otimes>\<^sub>n x = x"                        
  proof -
    fix x
    assume "x \<in> carrier (mod_group n)"
    then obtain k where x: "x = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k"
      unfolding mod_group_def int_monoid_COSETS_def RCOSETS_def by auto
    show "\<one>\<^sub>n \<otimes>\<^sub>n x = x"
      using rcos_sum[of n 0 k]
      unfolding x mod_group_def by simp
  qed

  show "\<And>x. x \<in> carrier (mod_group n) \<Longrightarrow> x \<otimes>\<^sub>n \<one>\<^sub>n = x"
  proof -
    fix x
    assume "x \<in> carrier (mod_group n)"
    then obtain k where x: "x = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k"
      unfolding mod_group_def int_monoid_COSETS_def RCOSETS_def by auto
    show "x \<otimes>\<^sub>n \<one>\<^sub>n = x"
      using rcos_sum[of n k 0]
      unfolding x mod_group_def by simp
  qed
qed
(*/solution*)

text \<open>But it's even a group:\<close>

lemma mod_group_is_group: 
  assumes "n > 0"
  shows "group (mod_group n)"
  unfolding group_def
  apply (simp add:mod_group_is_monoid)
(*solution*)
proof 
  show "carrier (mod_group n) \<subseteq> Units (mod_group n)"
  proof
    fix U
    assume "U \<in> carrier (mod_group n)"
    from this obtain k::int where " U = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k " 
      unfolding mod_group_def int_monoid_COSETS_def RCOSETS_def by auto
    have "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k \<in>  Units (mod_group n)" 
    proof -
      have "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k  \<^bold>+ (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k) = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (k -k)" using rcos_sum by auto
      also have "... = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> 0" by simp
      also have "... = \<one>\<^bsub>mod_group n\<^esub>" using mod_group_unit
        unfolding mod_group_def by simp
      finally have 1:"(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k  \<^bold>+ (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k) = \<one>\<^bsub>mod_group n\<^esub>" .
      have "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k)  \<^bold>+ (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k +k)" using rcos_sum by auto
      also have "... = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> 0" by simp
      also have "... = \<one>\<^bsub>mod_group n\<^esub>" using mod_group_unit
        unfolding mod_group_def by simp
      finally have 2:"(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k)  \<^bold>+ (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k = \<one>\<^bsub>mod_group n\<^esub>".
      have "-k \<in> UNIV" by simp
      hence "-k \<in> carrier(\<Z>)" unfolding int_monoid_def
        by (metis partial_object.select_convs(1))
      hence "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k) \<in> rcosets\<^bsub>\<Z>\<^esub> \<Z>\<cdot>n"
        unfolding RCOSETS_def by auto
      have "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (-k) \<in> \<Z>\<div>n" 
          unfolding int_monoid_COSETS_def
          by (simp add: \<open>((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (- k)) \<in> rcosets\<^bsub>\<Z>\<^esub> \<Z>\<cdot>n\<close>)
      hence 3:"\<Z>\<cdot>n #>\<^bsub>\<Z>\<^esub> (-k) \<in> carrier(mod_group n)"
        unfolding mod_group_def by simp
      from 1 2 3 show ?thesis using partial_object.select_convs(1)
        \<open>U = \<Z>\<cdot>n #>\<^bsub>\<Z>\<^esub> k\<close> \<open>U \<in> carrier (mod_group n)\<close>
        unfolding Units_def mod_group_def by auto
    qed
    from this show "U \<in>  Units (mod_group n)" using \<open>U = (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> k\<close> by auto
  qed
qed
(*/solution*)

subsection \<open>The multiplicative group of the quotient\<close>


subsubsection \<open>Lagrange and powers\<close>

text \<open>Apply @{thm group.lagrange_finite} to the cyclic subgroup generated
by a to prove the following standard finite-group consequence.\<close>

definition generated_subgroup_by ::
  "('a, 'b) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a monoid"
where
  "generated_subgroup_by G x =
    \<lparr>carrier = {x [^]\<^bsub>G\<^esub> i | i :: int. True},
      mult = mult G,
      one = one G\<rparr>"

definition
  el_order_abstract ::"('a, 'b) monoid_scheme => 'a => nat"
  where "el_order_abstract G x =
    (if x \<in> carrier G \<and> finite (carrier G)
     then card {x [^]\<^bsub>G\<^esub> i | i :: int. True}
     else 0)"

definition
  el_order ::"('a, 'b) monoid_scheme => 'a => nat"
  where " el_order G x =
    (if (\<exists> k::nat. k \<noteq> 0 \<and> x [^]\<^bsub>G\<^esub> k = \<one>\<^bsub>G\<^esub>)
     then (LEAST k. 0 < k \<and> x [^]\<^bsub>G\<^esub> k = \<one>\<^bsub>G\<^esub>)
     else 0)"

lemma generated_subgroup_by_is_subgroup:
  assumes "group G" and "x \<in> carrier G"
  shows "subgroup (carrier (generated_subgroup_by G x)) G"
(*solution*)
proof -
  interpret group G by fact
  show ?thesis
  proof (rule subgroup.intro)
    show "carrier (generated_subgroup_by G x) \<subseteq> carrier G"
      unfolding generated_subgroup_by_def using assms(2) by auto
  next
    fix y z
    assume y: "y \<in> carrier (generated_subgroup_by G x)"
      and z: "z \<in> carrier (generated_subgroup_by G x)"
    then obtain i j :: int where
      "y = x [^]\<^bsub>G\<^esub> i" and "z = x [^]\<^bsub>G\<^esub> j"
      unfolding generated_subgroup_by_def by auto
    hence yz: "y \<otimes>\<^bsub>G\<^esub> z =
        x [^]\<^bsub>G\<^esub> (i + j)"
      using int_pow_mult[OF assms(2), of i j] by simp
    show "y \<otimes>\<^bsub>G\<^esub> z \<in> carrier (generated_subgroup_by G x)"
      unfolding generated_subgroup_by_def using yz by auto
  next
    show "\<one>\<^bsub>G\<^esub> \<in> carrier (generated_subgroup_by G x)"
      unfolding generated_subgroup_by_def
      using assms(2) by (auto intro!: exI[of _ "0::int"])
  next
    fix y
    assume y_mem: "y \<in> carrier (generated_subgroup_by G x)"
    then obtain i :: int where y: "y = x [^]\<^bsub>G\<^esub> i"
      unfolding generated_subgroup_by_def by auto
    have "inv\<^bsub>G\<^esub> y = x [^]\<^bsub>G\<^esub> (-i)"
      using int_pow_neg[OF assms(2), of i] y by simp
    thus "inv\<^bsub>G\<^esub> y \<in> carrier (generated_subgroup_by G x)"
      unfolding generated_subgroup_by_def by auto
  qed
qed
(*/solution*)

text \<open>formalises Equal Powers of Finite Order Element from \<^url>\<open>https://proofwiki.org/wiki/Equal_Powers_of_Finite_Order_Element\<close>\<close>
lemma equal_powers:
  assumes "group G" and "a \<in> carrier G"
  assumes "el_order G a > 0"
  fixes k l::nat
  assumes "k\<ge>l"
  shows "a [^]\<^bsub>G\<^esub> k = a [^]\<^bsub>G\<^esub> l \<longleftrightarrow> (el_order G a) divides (k-l)"
(*solution*)
proof -
  interpret group G by fact
  let ?ord = "el_order G a"
  let ?P = "\<lambda>m::nat. 0 < m \<and> a [^]\<^bsub>G\<^esub> m = \<one>\<^bsub>G\<^esub>"
  let ?E = "\<exists>m::nat. m \<noteq> 0 \<and> a [^]\<^bsub>G\<^esub> m = \<one>\<^bsub>G\<^esub>"

  have d_if: "?ord = (if ?E then (LEAST m. ?P m) else 0)"
    unfolding el_order_def by simp

  have return_ex: ?E
  proof (cases ?E)
    case True
    thus ?thesis .
  next
    case False
    have "(if ?E then (LEAST m. ?P m) else 0) = 0"
      by (rule if_not_P[OF False])
    hence "el_order G a = 0" using d_if by simp
    with assms(3) show ?thesis by simp
  qed
  have d_eq: "?ord = (LEAST m. ?P m)"
    using return_ex d_if by simp
  obtain m where m: "?P m" using return_ex by blast
  have least_prop: "?P (LEAST m. ?P m)"
    by (rule wellorder_Least_lemma(1)[where P="?P" and k=m]) (fact m)
  have d_pos: "0 < ?ord" and d_return: "a [^]\<^bsub>G\<^esub> ?ord = \<one>\<^bsub>G\<^esub>"
    using d_eq least_prop by auto
  have d_min: "?ord \<le> r"
    if "0 < r" and "a [^]\<^bsub>G\<^esub> r = \<one>\<^bsub>G\<^esub>" for r
  proof -
    have "(LEAST m. ?P m) \<le> r"
      by (rule wellorder_Least_lemma(2)) (use that in simp)
    thus ?thesis using d_eq by simp
  qed

  show ?thesis
  proof
    assume powers_eq: "a [^]\<^bsub>G\<^esub> k = a [^]\<^bsub>G\<^esub> l"
    let ?r = "k-l"
    have k_eq: "k = l + ?r" using assms(4) by simp
    have r_return: "a [^]\<^bsub>G\<^esub> ?r = \<one>\<^bsub>G\<^esub>"
    proof -
      have "a [^]\<^bsub>G\<^esub> l \<otimes>\<^bsub>G\<^esub> a [^]\<^bsub>G\<^esub> ?r =
          a [^]\<^bsub>G\<^esub> l"
        using powers_eq k_eq nat_pow_mult[OF assms(2), of l ?r] by simp
      thus ?thesis using assms(2) by simp
    qed

    let ?q = "?r div ?ord"
    let ?t = "?r mod ?ord"
    have r_eq: "?r = ?ord * ?q + ?t"
      using d_pos by (simp add: div_mult_mod_eq mult.commute)
    have t_lt: "?t < ?ord" using d_pos by simp
    have "a [^]\<^bsub>G\<^esub> ?r =
        (a [^]\<^bsub>G\<^esub> ?ord) [^]\<^bsub>G\<^esub> ?q
          \<otimes>\<^bsub>G\<^esub> a [^]\<^bsub>G\<^esub> ?t"
      using r_eq assms(2) nat_pow_mult nat_pow_pow by metis
    also have "... = a [^]\<^bsub>G\<^esub> ?t" using d_return assms(2) by simp
    finally have t_return: "a [^]\<^bsub>G\<^esub> ?t = \<one>\<^bsub>G\<^esub>"
      using r_return by simp
    have t_zero: "?t = 0"
    proof (rule ccontr)
      assume "?t \<noteq> 0"
      hence "0 < ?t" by simp
      hence "?ord \<le> ?t" using d_min t_return by blast
      with t_lt show False by simp
    qed
    show "?ord divides ?r"
      unfolding divides_def
      apply (rule exI[where x="?q"])
      using r_eq t_zero by simp
  next
    assume divides: "?ord divides (k-l)"
    then obtain q where q: "?ord * q = k-l"
      unfolding divides_def by blast
    have k_eq: "k = l + ?ord * q" using assms(4) q by simp
    have "a [^]\<^bsub>G\<^esub> k = a [^]\<^bsub>G\<^esub> (l + ?ord * q)"
      using k_eq by simp
    also have "... = a [^]\<^bsub>G\<^esub> l \<otimes>\<^bsub>G\<^esub>
        a [^]\<^bsub>G\<^esub> (?ord * q)"
      using nat_pow_mult[OF assms(2), of l "?ord*q"] by simp
    also have "... = a [^]\<^bsub>G\<^esub> l \<otimes>\<^bsub>G\<^esub>
        (a [^]\<^bsub>G\<^esub> ?ord) [^]\<^bsub>G\<^esub> q"
      using nat_pow_pow[OF assms(2), of ?ord q] by simp
    also have "... = a [^]\<^bsub>G\<^esub> l" using d_return assms(2) by simp
    finally show "a [^]\<^bsub>G\<^esub> k = a [^]\<^bsub>G\<^esub> l" .
  qed
qed
(*/solution*)

proposition el_order_annihil [simp]:
  assumes "group G" and "a \<in> carrier G" and "0 < el_order G a"
  shows "a [^]\<^bsub>G\<^esub> el_order G a = \<one>\<^bsub>G\<^esub>"
(*solution*)
proof -
  have nonneg: "el_order G a \<ge> 0" by simp
  have dvd: "el_order G a divides (el_order G a - 0)"
    unfolding divides_def
    by (rule exI[where x=1]) simp
  have "a [^]\<^bsub>G\<^esub> el_order G a = a [^]\<^bsub>G\<^esub> (0::nat)"
    apply (subst equal_powers[OF assms(1) assms(2) assms(3) nonneg])
    by (fact dvd)
  thus ?thesis by simp
qed
(*/solution*)

text \<open>formalises \<^url>\<open>https://proofwiki.org/wiki/Element_to_Power_of_Remainder\<close>\<close>
lemma element_to_power_remainder:
  assumes "group G" and "a \<in> carrier G" and "0 < el_order G a"
  shows "a [^]\<^bsub>G\<^esub> n = a [^]\<^bsub>G\<^esub> (n mod el_order G a)"
(*solution*)
proof -
  let ?ord = "el_order G a"
  have rem_le: "n mod ?ord \<le> n" by simp
  have dvd: "?ord divides (n - n mod ?ord)"
    unfolding divides_def
  proof (rule exI[where x="n div ?ord"])
    have "?ord * (n div ?ord) + n mod ?ord = n"
      by (simp add: div_mult_mod_eq mult.commute)
    hence decomp: "n = ?ord * (n div ?ord) + n mod ?ord" by simp
    have "?ord * (n div ?ord) =
        (n mod ?ord + ?ord * (n div ?ord)) - n mod ?ord"
      by (rule sym, rule add_diff_cancel_left')
    also have "... = n - n mod ?ord" using decomp by simp
    finally show "?ord * (n div ?ord) = n - n mod ?ord" .
  qed
  show ?thesis
    using equal_powers[OF assms rem_le] dvd by blast
qed
(*/solution*)

text \<open>formalises \<^url>\<open>https://proofwiki.org/wiki/List_of_Elements_in_Finite_Cyclic_Group\<close>\<close>
lemma finite_cyclic_group_elements:
  assumes "group G" and "a \<in> carrier G" and "0 < el_order G a"
  shows "bij_betw (\<lambda>n. a [^]\<^bsub>G\<^esub> n)
    {0..<el_order G a} (carrier (generated_subgroup_by G a))"
proof -
  interpret group G by fact
  let ?ord = "el_order G a"
  let ?exp = "\<lambda>n. a [^]\<^bsub>G\<^esub> n"

  have order_return: "a [^]\<^bsub>G\<^esub> ?ord = \<one>\<^bsub>G\<^esub>"
    using el_order_annihil[OF assms] .

  have image_eq: "?exp ` {0..< ?ord} = carrier (generated_subgroup_by G a)"
  proof
    show "?exp ` {0..< ?ord} \<subseteq> carrier (generated_subgroup_by G a)"
      unfolding generated_subgroup_by_def
      by (auto intro!: exI[of _ "int _"] simp: int_pow_int)
  next
    show "carrier (generated_subgroup_by G a) \<subseteq> ?exp ` {0..< ?ord}"
    proof
      fix y
      assume "y \<in> carrier (generated_subgroup_by G a)"
      then obtain i :: int where y: "y = a [^]\<^bsub>G\<^esub> i"
        unfolding generated_subgroup_by_def by auto
      show "y \<in> ?exp ` {0..< ?ord}"
      proof (cases "0 \<le> i")
        case True
        let ?r = "nat i mod ?ord"
        have r_lt: "?r < ?ord" using assms(3) by simp
        have "y = a [^]\<^bsub>G\<^esub> nat i"
          using y True by simp
        also have "... = a [^]\<^bsub>G\<^esub> ?r"
          by (rule element_to_power_remainder[OF assms])
        finally have yr: "y = ?exp ?r" .
        show ?thesis
        proof (rule rev_image_eqI[where x="?r"])
          show "?r \<in> {0..< ?ord}" using r_lt by simp
          show "y = ?exp ?r" by fact
        qed
      next
        case False
        let ?m = "nat (-i)"
        let ?r = "?m mod ?ord"
        let ?s = "(?ord - ?r) mod ?ord"
        have r_lt: "?r < ?ord" using assms(3) by simp
        have s_lt: "?s < ?ord" using assms(3) by simp
        have i_eq: "i = - int ?m" using False by simp
        have yi: "y = inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> ?m)"
        proof -
          have "y = a [^]\<^bsub>G\<^esub> (- int ?m)" using y i_eq by simp
          also have "... = inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> ?m)"
            by (rule int_pow_neg_int[OF assms(2)])
          finally show ?thesis .
        qed
        have rem: "a [^]\<^bsub>G\<^esub> ?m = a [^]\<^bsub>G\<^esub> ?r"
          by (rule element_to_power_remainder[OF assms])
        have inverse_rem:
          "inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> ?r) = a [^]\<^bsub>G\<^esub> ?s"
        proof (cases "?r = 0")
          case True
          thus ?thesis using assms(2,3) by simp
        next
          case False
          hence r_pos: "0 < ?r" by simp
          have s_eq: "?s = ?ord - ?r"
            using r_pos r_lt by simp
          have product: "a [^]\<^bsub>G\<^esub> (?ord - ?r) \<otimes>\<^bsub>G\<^esub>
              a [^]\<^bsub>G\<^esub> ?r = \<one>\<^bsub>G\<^esub>"
            using nat_pow_mult[OF assms(2), of "?ord-?r" ?r]
              order_return r_lt by simp
          have "inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> ?r) =
              a [^]\<^bsub>G\<^esub> (?ord - ?r)"
          proof (rule inv_equality)
            show "a [^]\<^bsub>G\<^esub> (?ord - ?r) \<otimes>\<^bsub>G\<^esub>
                a [^]\<^bsub>G\<^esub> ?r = \<one>\<^bsub>G\<^esub>" by fact
            show "a [^]\<^bsub>G\<^esub> ?r \<in> carrier G" using assms(2) by simp
            show "a [^]\<^bsub>G\<^esub> (?ord - ?r) \<in> carrier G"
              using assms(2) by simp
          qed
          thus ?thesis using s_eq by simp
        qed
        have "y = a [^]\<^bsub>G\<^esub> ?s" using yi rem inverse_rem by simp
        hence ys: "y = ?exp ?s" .
        show ?thesis
        proof (rule rev_image_eqI[where x="?s"])
          show "?s \<in> {0..< ?ord}" using s_lt by simp
          show "y = ?exp ?s" by fact
        qed
      qed
    qed
  qed

  have inj: "inj_on ?exp {0..< ?ord}"
  proof (rule inj_onI)
    fix k l
    assume k: "k \<in> {0..< ?ord}" and l: "l \<in> {0..< ?ord}"
      and eq: "?exp k = ?exp l"
    show "k = l"
    proof (cases "l \<le> k")
      case True
      have "?ord divides (k-l)"
        by (rule iffD1[OF equal_powers[OF assms True] eq])
      moreover have "k-l < ?ord" using k by simp
      ultimately have "k-l = 0"
        using assms(3) notDivides[of "k-l" ?ord] by blast
      with True show ?thesis by simp
    next
      case False
      hence kl: "k \<le> l" by simp
      have eq': "?exp l = ?exp k" using eq by simp
      have "?ord divides (l-k)"
        by (rule iffD1[OF equal_powers[OF assms kl] eq'])
      moreover have "l-k < ?ord" using l by simp
      ultimately have "l-k = 0"
        using assms(3) notDivides[of "l-k" ?ord] by blast
      with kl show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding bij_betw_def using inj image_eq by blast
qed

lemma el_order_finite_on_finite_groups:
  assumes "group G" and "finite(carrier G)"
  assumes "x \<in> carrier G"
  shows "0 < el_order G x"
(*solution*)
proof -
  interpret group G by fact
  let ?exp = "\<lambda>k::nat. x [^]\<^bsub>G\<^esub> k"
  let ?annihil = "\<lambda>k::nat. 0 < k \<and> x [^]\<^bsub>G\<^esub> k = \<one>\<^bsub>G\<^esub>"
  have finite_range: "finite (range ?exp)"
    by (rule finite_subset[OF _ assms(2)]) (use assms(3) in auto)
  have not_inj: "\<not> inj ?exp"
  proof
    assume "inj ?exp"
    have finite_image: "finite (?exp ` (UNIV::nat set))"
      using finite_range by simp
    hence "finite (UNIV::nat set)"
      by (rule finite_imageD) (use \<open>inj ?exp\<close> in simp)
    thus False by simp
  qed
  then obtain k l where kl: "k \<noteq> l" "?exp k = ?exp l"
    unfolding inj_def by blast
  have return_diff: "x [^]\<^bsub>G\<^esub> (m - n) = \<one>\<^bsub>G\<^esub>"
    if "n \<le> m" and "?exp m = ?exp n" for m n
  proof -
    have m_eq: "m = n + (m - n)" using that(1) by simp
    have "x [^]\<^bsub>G\<^esub> n \<otimes>\<^bsub>G\<^esub> x [^]\<^bsub>G\<^esub> (m - n) =
        x [^]\<^bsub>G\<^esub> n"
      using that(2) m_eq nat_pow_mult[OF assms(3), of n "m-n"] by simp
    thus ?thesis using assms(3) by simp
  qed
  have witness_ex: "\<exists>n. ?annihil n"
  proof (cases "l \<le> k")
    case True
    have "0 < k-l" using kl(1) True by simp
    moreover have "x [^]\<^bsub>G\<^esub> (k-l) = \<one>\<^bsub>G\<^esub>"
      by (rule return_diff[OF True kl(2)])
    ultimately have "?annihil (k-l)" by simp
    thus ?thesis by blast
  next
    case False
    hence less: "k \<le> l" by simp
    have "0 < l-k" using kl(1) False by simp
    moreover have "x [^]\<^bsub>G\<^esub> (l-k) = \<one>\<^bsub>G\<^esub>"
      by (rule return_diff[OF less]) (use kl(2) in simp)
    ultimately have "?annihil (l-k)" by simp
    thus ?thesis by blast
  qed
  then obtain n where witness: "?annihil n" by blast
  have least_prop: "?annihil (LEAST k. ?annihil k)"
    by (rule wellorder_Least_lemma(1)[where k=n]) (fact witness)
  have return_ex:
      "\<exists>k::nat. k \<noteq> 0 \<and> x [^]\<^bsub>G\<^esub> k = \<one>\<^bsub>G\<^esub>"
    using witness by auto
  have "el_order G x = (LEAST k. ?annihil k)"
    unfolding el_order_def using return_ex by simp
  thus ?thesis using least_prop by simp
qed
(*/solution*)

text \<open>2nd part of \<^url>\<open>https://proofwiki.org/wiki/Equivalence_of_Definitions_of_Order_of_Group_Element\<close>\<close>
lemma el_order_first_second_equiv:
  assumes "group G" and "finite (carrier G)" and "x \<in> carrier G"
  shows "el_order G x = el_order_abstract G x"
(*solution*)
proof -
  let ?ord = "el_order G x"
  have ord_pos: "0 < ?ord"
    by (rule el_order_finite_on_finite_groups[OF assms])
  have bij: "bij_betw (\<lambda>n. x [^]\<^bsub>G\<^esub> n) {0..< ?ord}
      (carrier (generated_subgroup_by G x))"
    by (rule finite_cyclic_group_elements[OF assms(1) assms(3) ord_pos])
  have "card {0..< ?ord} = card (carrier (generated_subgroup_by G x))"
    by (rule bij_betw_same_card[OF bij])
  hence ord_card:
      "?ord = card {x [^]\<^bsub>G\<^esub> i | i :: int. True}"
    unfolding generated_subgroup_by_def by simp
  show ?thesis
    unfolding el_order_abstract_def using assms(2,3) ord_card by simp
qed
(*/solution*)

text\<open>Probably this is quite inefficient. Idea for improvement: add a 3rd definition by the minimality property (intersection)\<close>

proposition order_annihil:
  assumes "group G" and "finite(carrier G)"
  assumes "a \<in> carrier G"
  shows "a [^]\<^bsub>G\<^esub> order G = \<one>\<^bsub>G\<^esub>"
(*solution*)
proof-
  have ord_finite: "0 < el_order G a" using el_order_finite_on_finite_groups assms by fast
  have "a [^]\<^bsub>G\<^esub> el_order_abstract G a = a [^]\<^bsub>G\<^esub> el_order G a" 
    using el_order_first_second_equiv assms by metis
  also have "\<dots> = \<one>\<^bsub>G\<^esub>" 
    by (rule el_order_annihil[OF assms(1) assms(3) ord_finite])
  finally have el_order_abstract_annihil:"a [^]\<^bsub>G\<^esub> el_order_abstract G a = \<one>\<^bsub>G\<^esub>".
  let ?H = "generated_subgroup_by G a"
  interpret group G by fact
  from generated_subgroup_by_is_subgroup  have subgroup:"subgroup (carrier ?H) G " 
    using assms by metis
  have H_carrier:"carrier (generated_subgroup_by G a) = {a [^]\<^bsub>G\<^esub> i |i :: int. True}"
    using generated_subgroup_by_def[of G a]  by simp
  have "el_order_abstract G a = card {a [^]\<^bsub>G\<^esub> i | i :: int. True}"
    using el_order_abstract_def[of G a] assms(2,3) by simp
  with lagrange_finite[OF assms(2) subgroup]
    have "el_order_abstract G a divides order G"
      using divides_def H_carrier by (metis mult.commute)
  from this obtain k::nat where "(el_order_abstract G a)*k = order G" using divides_def by auto
  then have "a [^]\<^bsub>G\<^esub> order G = a [^]\<^bsub>G\<^esub> ((el_order_abstract G a)*k)" by simp
  also have "\<dots> = (a [^]\<^bsub>G\<^esub> (el_order_abstract G a) ) [^]\<^bsub>G\<^esub> k"
    using assms(3) nat_pow_pow by force
  also have "\<dots> =  (\<one>\<^bsub>G\<^esub>) [^]\<^bsub>G\<^esub> k" using el_order_abstract_annihil by simp
  also have "\<dots> = \<one>\<^bsub>G\<^esub>" by simp
  finally show ?thesis.
qed
(*/solution*)

subsection \<open>Unit group of Z/nZ\<close>


subsubsection \<open>Multiplication of residue classes\<close>

definition int_coset_mult :: "int \<Rightarrow> int set \<Rightarrow> int set \<Rightarrow> int set" where
  "int_coset_mult n U V =
    (\<Union>u\<in>U. \<Union>v\<in>V. \<Z> n \<cdot> (u * v))"

definition zero_class :: "int \<Rightarrow> int set" where
  "zero_class n = \<Z> n \<cdot> 0"

definition one_class :: "int \<Rightarrow> int set" where
  "one_class n = \<Z> n \<cdot> 1"

lemma int_rcoset_mult:
  "int_coset_mult n
      (\<Z> n \<cdot> a) (\<Z> n \<cdot> b) = \<Z> n \<cdot> (a * b)"
(*solution*)
proof
  show "int_coset_mult n
      (\<Z> n \<cdot> a) (\<Z> n \<cdot> b) \<subseteq> \<Z> n \<cdot> (a * b) "
  proof
    fix x
    assume "x \<in> int_coset_mult n
      (\<Z> n \<cdot> a) (\<Z> n \<cdot> b)"
    then obtain u v r s t :: int where
      u: "u = n * r + a" and v: "v = n * s + b"
      and x: "x = n * t + u * v"
      unfolding int_coset_mult_def int_rcoset_characterisation by blast
    have "x = n * (t + n * r * s + r * b + s * a) + a * b"
      using u v x by (simp add: algebra_simps)
    thus "x \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (a * b)"
      unfolding int_rcoset_characterisation by blast
  qed
next
  show "(\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (a * b) \<subseteq>
      int_coset_mult n
        ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> a)
        ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> b)"
  proof
    fix x
    assume x: "x \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> (a * b)"
    have a_mem: "a \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> a"
      using int_rcoset_incl[of n 0 a] by simp
    have b_mem: "b \<in> (\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> b"
      using int_rcoset_incl[of n 0 b] by simp
    show "x \<in> int_coset_mult n
        ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> a)
        ((\<Z>\<cdot>n) #>\<^bsub>\<Z>\<^esub> b)"
      unfolding int_coset_mult_def using x a_mem b_mem by blast
  qed
qed
(*/solution*)

subsubsection \<open>Nonzero classes modulo a prime\<close>

definition mult_mod_group :: "nat \<Rightarrow> int set monoid" where
  "mult_mod_group p =
    \<lparr>carrier = (\<Z>\<div>(int p)) - {zero_class (int p)},
      mult = int_coset_mult (int p),
      one = one_class (int p)\<rparr>"

text \<open>Choose the canonical representative @{term "k mod int p"} and
convert it to a natural number.  This connects integer cosets to
@{const divides} and @{const isprime}.\<close>

lemma coset_has_nat_representative:
  assumes "0 < p" and "U \<in> \<Z>\<div>(int p)"
  obtains a :: nat where
    "a < p"
    "U = \<Z> (int p) \<cdot> (int a)"
(*solution*)
proof -
  obtain k :: int where U:
      "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k"
    using assms(2)
    unfolding int_monoid_COSETS_def RCOSETS_def int_monoid_def by auto
  let ?r = "k mod int p"
  have r_nonneg: "0 \<le> ?r" and r_less: "?r < int p"
    using assms(1) by auto
  have decomp: "k = int p * (k div int p) + ?r"
    using div_mult_mod_eq[of k "int p"] by (simp add: mult.commute)
  have coset_mod:
      "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k =
       (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ?r"
  (*solution*)
  proof
    show "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k \<subseteq>
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ?r"
    proof
      fix x
      assume "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k"
      then obtain l :: int where x: "x = int p * l + k"
        unfolding int_rcoset_characterisation by auto
      have "x = int p * (l + k div int p) + ?r"
        using x decomp by (simp add: algebra_simps)
      thus "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ?r"
        unfolding int_rcoset_characterisation by auto
    qed
  next
    show "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ?r \<subseteq>
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k"
    proof
      fix x
      assume "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ?r"
      then obtain l :: int where x: "x = int p * l + ?r"
        unfolding int_rcoset_characterisation by auto
      have "x = int p * (l - k div int p) + k"
        using x decomp by (simp add: algebra_simps)
      thus "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> k"
        unfolding int_rcoset_characterisation by auto
    qed
  qed
  (*/solution*)
  show thesis
  proof (rule that[of "nat ?r"])
    show "nat ?r < p" using r_nonneg r_less by simp
    show "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (nat ?r)"
      using U coset_mod r_nonneg by simp
  qed
qed
(*/solution*)

lemma nat_coset_eq_zero_iff:
  "(\<Z> (int p) \<cdot> (int a)) = zero_class (int p)
    \<longleftrightarrow> p divides a"
(*solution*)
proof
  assume eq: "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a = zero_class (int p)"
  have "int a \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
    using int_rcoset_incl[of "int p" 0 "int a"] by simp
  with eq obtain l :: int where ia: "int a = int p * l"
    unfolding zero_class_def int_rcoset_characterisation by auto
  show "p divides a"
  proof (cases "p = 0")
    case True
    hence "a = 0" using ia by simp
    thus ?thesis unfolding divides_def by auto
  next
    case False
    have p_pos: "0 < int p" using False by simp
    have l_nonneg: "0 \<le> l"
    proof (rule ccontr)
      assume "\<not> 0 \<le> l"
      hence "int p * l < 0" using p_pos by (simp add: mult_pos_neg)
      thus False using ia by simp
    qed
    have "p * nat l = a"
    proof (rule int_int_eq[THEN iffD1])
      show "int (p * nat l) = int a" using ia l_nonneg by simp
    qed
    thus ?thesis unfolding divides_def by blast
  qed
next
  assume "p divides a"
  then obtain k :: nat where pk: "p * k = a"
    unfolding divides_def by blast
  have cast_pk: "int (p*k) = int a" using pk by simp
  have ia: "int a = int p * int k" using cast_pk by simp
  show "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a = zero_class (int p)"
  proof
    show "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a \<subseteq> zero_class (int p)"
    proof
      fix x
      assume "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
      then obtain l :: int where x: "x = int p * l + int a"
        unfolding int_rcoset_characterisation by auto
      have "x = int p * (l + int k) + 0"
        using x ia by (simp add: algebra_simps)
      thus "x \<in> zero_class (int p)"
        unfolding zero_class_def int_rcoset_characterisation by auto
    qed
  next
    show "zero_class (int p) \<subseteq>
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
    proof
      fix x
      assume "x \<in> zero_class (int p)"
      then obtain l :: int where x: "x = int p * l"
        unfolding zero_class_def int_rcoset_characterisation by auto
      have "x = int p * (l - int k) + int a"
        using x ia by (simp add: algebra_simps)
      thus "x \<in> (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
        unfolding int_rcoset_characterisation by auto
    qed
  qed
qed
(*/solution*)

lemma prime_divisor_less:
  assumes "p isprime" and "a < p" and "p divides a"
  shows "a = 0"
(*solution*)
proof (rule ccontr)
  assume "a \<noteq> 0"
  have "\<not> p divides a" by (rule notDivides[OF assms(2) \<open>a \<noteq> 0\<close>])
  with assms(3) show False by contradiction
qed
(*/solution*)

lemma prime_nonzero_mult_closed:
  assumes "p isprime"
    and "U \<in> carrier (mult_mod_group p)"
    and "V \<in> carrier (mult_mod_group p)"
  shows "U \<otimes>\<^bsub>mult_mod_group p\<^esub> V \<in> carrier (mult_mod_group p)"
(*solution*)
proof -
  have p_pos: "0 < p" using assms(1) unfolding isprime_def by simp
  have U_coset: "U \<in> \<Z>\<div>(int p)" and U_ne: "U \<noteq> zero_class (int p)"
    using assms(2) unfolding mult_mod_group_def by auto
  have V_coset: "V \<in> \<Z>\<div>(int p)" and V_ne: "V \<noteq> zero_class (int p)"
    using assms(3) unfolding mult_mod_group_def by auto
  obtain a :: nat where a: "a < p"
      "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
    by (rule coset_has_nat_representative[OF p_pos U_coset])
  obtain b :: nat where b: "b < p"
      "V = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int b"
    by (rule coset_has_nat_representative[OF p_pos V_coset])
  have a_not_dvd: "\<not> p divides a"
    using U_ne a nat_coset_eq_zero_iff by blast
  have b_not_dvd: "\<not> p divides b"
    using V_ne b nat_coset_eq_zero_iff by blast
  have product:
      "U \<otimes>\<^bsub>mult_mod_group p\<^esub> V =
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (a*b)"
    using int_rcoset_mult[of "int p" "int a" "int b"] a b
    unfolding mult_mod_group_def by simp
  have product_coset:
      "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (a*b) \<in> \<Z>\<div>(int p)"
    unfolding int_monoid_COSETS_def RCOSETS_def int_monoid_def by auto
  have product_nonzero:
      "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (a*b) \<noteq> zero_class (int p)"
  proof
    assume "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (a*b) = zero_class (int p)"
    hence "p divides a*b" using nat_coset_eq_zero_iff by blast
    hence "p divides a \<or> p divides b"
      using assms(1) unfolding isprime_def by blast
    with a_not_dvd b_not_dvd show False by blast
  qed
  show ?thesis
    using product product_coset product_nonzero unfolding mult_mod_group_def by simp
qed
(*/solution*)

lemma mult_mod_group_is_monoid:
  assumes "p isprime"
  shows "monoid (mult_mod_group p)"
(*solution*)
proof (rule monoidI)
  show "\<And>U V. U \<in> carrier (mult_mod_group p) \<Longrightarrow>
      V \<in> carrier (mult_mod_group p) \<Longrightarrow>
      U \<otimes>\<^bsub>mult_mod_group p\<^esub> V \<in> carrier (mult_mod_group p)"
    using prime_nonzero_mult_closed[OF assms] .
next
  have "(1::int) \<in> carrier \<Z>" unfolding int_monoid_def by simp
  hence "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> 1 \<in> rcosets\<^bsub>\<Z>\<^esub> (\<Z>\<cdot>(int p))"
    unfolding RCOSETS_def by blast
  hence one_coset: "one_class (int p) \<in> \<Z>\<div>(int p)"
    unfolding one_class_def int_monoid_COSETS_def .
  have p_ne_one: "p \<noteq> 1" using assms unfolding isprime_def by blast
  have one_ne: "one_class (int p) \<noteq> zero_class (int p)"
  proof
    assume eq: "one_class (int p) = zero_class (int p)"
    have "p divides 1"
      by (rule iffD1[OF nat_coset_eq_zero_iff[of p 1]])
         (use eq in \<open>simp add: one_class_def\<close>)
    then obtain k where pk: "p*k = 1" unfolding divides_def by blast
    have "p = 1" using pk by simp
    with p_ne_one show False by contradiction
  qed
  show "\<one>\<^bsub>mult_mod_group p\<^esub> \<in> carrier (mult_mod_group p)"
    using one_coset one_ne unfolding mult_mod_group_def
    by (simp only: partial_object.select_convs monoid.select_convs
        Diff_iff singleton_iff one_coset one_ne)
next
  fix U V W
  assume U: "U \<in> carrier (mult_mod_group p)"
    and V: "V \<in> carrier (mult_mod_group p)"
    and W: "W \<in> carrier (mult_mod_group p)"
  obtain a :: int where Ua: "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> a"
    using U unfolding mult_mod_group_def int_monoid_COSETS_def
      RCOSETS_def int_monoid_def by auto
  obtain b :: int where Vb: "V = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> b"
    using V unfolding mult_mod_group_def int_monoid_COSETS_def
      RCOSETS_def int_monoid_def by auto
  obtain c :: int where Wc: "W = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> c"
    using W unfolding mult_mod_group_def int_monoid_COSETS_def
      RCOSETS_def int_monoid_def by auto
  have left: "U \<otimes>\<^bsub>mult_mod_group p\<^esub> V
      \<otimes>\<^bsub>mult_mod_group p\<^esub> W =
      (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> ((a*b)*c)"
    using int_rcoset_mult[of "int p" a b]
      int_rcoset_mult[of "int p" "a*b" c]
    unfolding mult_mod_group_def Ua Vb Wc by simp
  have right: "U \<otimes>\<^bsub>mult_mod_group p\<^esub>
      (V \<otimes>\<^bsub>mult_mod_group p\<^esub> W) =
      (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> (a*(b*c))"
    using int_rcoset_mult[of "int p" b c]
      int_rcoset_mult[of "int p" a "b*c"]
    unfolding mult_mod_group_def Ua Vb Wc by simp
  show "U \<otimes>\<^bsub>mult_mod_group p\<^esub> V \<otimes>\<^bsub>mult_mod_group p\<^esub> W =
      U \<otimes>\<^bsub>mult_mod_group p\<^esub>
        (V \<otimes>\<^bsub>mult_mod_group p\<^esub> W)"
    using left right by (simp add: mult.assoc)
next
  fix U
  assume U: "U \<in> carrier (mult_mod_group p)"
  obtain a :: int where Ua: "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> a"
    using U unfolding mult_mod_group_def int_monoid_COSETS_def
      RCOSETS_def int_monoid_def by auto
  show "\<one>\<^bsub>mult_mod_group p\<^esub> \<otimes>\<^bsub>mult_mod_group p\<^esub> U = U"
    using int_rcoset_mult[of "int p" 1 a]
    unfolding mult_mod_group_def one_class_def Ua by simp
next
  fix U
  assume U: "U \<in> carrier (mult_mod_group p)"
  obtain a :: int where Ua: "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> a"
    using U unfolding mult_mod_group_def int_monoid_COSETS_def
      RCOSETS_def int_monoid_def by auto
  show "U \<otimes>\<^bsub>mult_mod_group p\<^esub> \<one>\<^bsub>mult_mod_group p\<^esub> = U"
    using int_rcoset_mult[of "int p" a 1]
    unfolding mult_mod_group_def one_class_def Ua by simp
qed
(*/solution*)

subsubsection \<open>Existence of inverses\<close>

definition class_mult_map :: "nat \<Rightarrow> int set \<Rightarrow> int set \<Rightarrow> int set" where
  "class_mult_map p U V = U \<otimes>\<^bsub>mult_mod_group p\<^esub> V"

lemma mult_mod_group_carrier:
  assumes "p isprime"
  shows "carrier (mult_mod_group p) =
    (\<lambda>a. \<Z> (int p) \<cdot> (int a)) ` {1..<p}"
(*solution*)
proof -
  have p_pos: "0 < p" using assms unfolding isprime_def by simp
  show ?thesis
  proof
    show "carrier (mult_mod_group p) \<subseteq>
        (\<lambda>a. (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a) ` {1..<p}"
    (*solution*)
    proof
      fix U
      assume U: "U \<in> carrier (mult_mod_group p)"
      have U_coset: "U \<in> \<Z>\<div>(int p)"
        using U unfolding mult_mod_group_def by simp
      obtain a :: nat where a: "a < p"
          "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
        by (rule coset_has_nat_representative[OF p_pos U_coset])
      have "a \<noteq> 0"
        using U a(2) unfolding mult_mod_group_def zero_class_def by auto
      hence "a \<in> {1..<p}" using a(1) by simp
      with a(2) show "U \<in>
          (\<lambda>a. (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a) ` {1..<p}" by blast
    qed
    (*/solution*)
  next                      
    show "(\<lambda>a. (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a) ` {1..<p} \<subseteq>
        carrier (mult_mod_group p)"
    (*solution*)
    proof
      fix U
      assume "U \<in> (\<lambda>a. (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a) ` {1..<p}"
      then obtain a where a: "a \<in> {1..<p}"
        "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a" by blast
      have U_coset: "U \<in> \<Z>\<div>(int p)"
        using a unfolding int_monoid_COSETS_def RCOSETS_def int_monoid_def by auto
      have U_ne: "U \<noteq> zero_class (int p)"
      proof
        assume "U = zero_class (int p)"
        hence "p divides a" using a nat_coset_eq_zero_iff by blast
        moreover have "a < p" using a by simp
        ultimately have "a = 0"
          using prime_divisor_less[of p a] assms by blast
        with a show False by simp
      qed
      show "U \<in> carrier (mult_mod_group p)"
        using U_coset U_ne unfolding mult_mod_group_def by simp
    qed
  qed
  (*/solution*)
qed
(*/solution*)

lemma finite_mult_mod_group:
  assumes "p isprime"
  shows "finite (carrier (mult_mod_group p))"
(*solution*)
  unfolding mult_mod_group_carrier[OF assms] by simp
(*/solution*)

lemma card_mult_mod_group:
  assumes "p isprime"
  shows "card (carrier (mult_mod_group p)) = p - 1"
(*solution*)
proof -
  let ?f = "\<lambda>a::nat. \<Z> (int p) \<cdot> (int a)"
  have p_pos: "0 < p" using assms unfolding isprime_def by simp
  have f_inj: "inj_on ?f {1..<p}"
  proof (rule inj_onI)
    fix a b
    assume a: "a \<in> {1..<p}" and b: "b \<in> {1..<p}"
      and eq: "?f a = ?f b"
    have "int a \<in> ?f a" using int_rcoset_incl[of "int p" 0 "int a"] by simp
    hence "int a \<in> ?f b" using eq by simp
    then obtain l :: int where ab: "int a = int p * l + int b"
      unfolding int_rcoset_characterisation by auto
    have "int a mod int p = int b mod int p" using ab p_pos by simp
    thus "a = b" using a b p_pos by simp
  qed
  have "card (carrier (mult_mod_group p)) = card (?f ` {1..<p})"
    using mult_mod_group_carrier[OF assms] by simp
  also have "... = card {1..<p}" by (rule card_image[OF f_inj])
  also have "... = p-1" by simp
  finally show ?thesis .
qed
(*/solution*)

lemma class_mult_map_inj:
  assumes "p isprime" and "U \<in> carrier (mult_mod_group p)"
  shows "inj_on (class_mult_map p U) (carrier (mult_mod_group p))"
proof (rule inj_onI)
  fix V W
  assume V: "V \<in> carrier (mult_mod_group p)"
    and W: "W \<in> carrier (mult_mod_group p)"
    and map_eq: "class_mult_map p U V = class_mult_map p U W"
  let ?C = "\<lambda>a::nat. \<Z> (int p) \<cdot> (int a)"
  have p_pos: "0 < p" using assms(1) unfolding isprime_def by simp
  obtain u where u: "u \<in> {1..<p}" "U = ?C u"
    using assms(2) mult_mod_group_carrier[OF assms(1)] by auto
  obtain v where v: "v \<in> {1..<p}" "V = ?C v"
    using V mult_mod_group_carrier[OF assms(1)] by auto
  obtain w where w: "w \<in> {1..<p}" "W = ?C w"
    using W mult_mod_group_carrier[OF assms(1)] by auto
  have u_not_dvd: "\<not> p divides u"
  proof
    assume dvd: "p divides u"
    have u_lt: "u < p" using u by simp
    have "u = 0"
      using prime_divisor_less[of p u] assms(1) u_lt dvd by blast
    with u show False by simp
  qed
  have product_eq:
      "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*v) =
       (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*w)"
    using map_eq int_rcoset_mult[of "int p" "int u" "int v"]
      int_rcoset_mult[of "int p" "int u" "int w"]
    unfolding class_mult_map_def mult_mod_group_def u(2) v(2) w(2) by simp

  have cancel_ordered: "x = y"
    if y_le_x: "y \<le> x" and x_lt: "x < p"
      and eq: "(\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*x) =
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*y)" for x y
  (*solution*)
  proof -
    have "int (u*x) \<in>
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*x)"
      using int_rcoset_incl[of "int p" 0 "int (u*x)"] by simp
    hence "int (u*x) \<in>
        (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (u*y)" using eq by simp
    then obtain l :: int where repr:
        "int (u*x) = int p * l + int (u*y)"
      unfolding int_rcoset_characterisation by auto
    have l_nonneg: "0 \<le> l"
    proof (rule ccontr)
      assume "\<not> 0 \<le> l"
      hence "int p * l < 0" using p_pos by (simp add: mult_pos_neg)
      moreover have nat_le: "u*y \<le> u*x"
        using mult_le_mono1[OF y_le_x, of u] by (simp add: mult.commute)
      have "int (u*y) \<le> int (u*x)" by (rule of_nat_mono[OF nat_le])
      ultimately show False using repr by linarith
    qed
    have nat_repr: "u*x = p * nat l + u*y"
    proof (rule int_int_eq[THEN iffD1])
      show "int (u*x) = int (p * nat l + u*y)"
        using repr l_nonneg by (simp add: algebra_simps)
    qed
    have x_decomp: "x = y + (x-y)" using y_le_x by simp
    have ux_decomp: "u*x = u*y + u*(x-y)"
    proof -
      have "u*x = u*(y + (x-y))"
        using x_decomp by (rule arg_cong[where f="\<lambda>z. u*z"])
      also have "... = u*y + u*(x-y)" by (rule add_mult_distrib2)
      finally show ?thesis .
    qed
    have diff_eq: "p * nat l = u*(x-y)"
      using nat_repr ux_decomp by (simp add: add.commute)
    have "p divides u*(x-y)"
      unfolding divides_def using diff_eq by blast
    hence "p divides u \<or> p divides (x-y)"
      using assms(1) unfolding isprime_def by blast
    hence diff_dvd: "p divides (x-y)" using u_not_dvd by blast
    have diff_lt: "x-y < p" using x_lt by simp
    have "x-y = 0"
      using prime_divisor_less[of p "x-y"] assms(1) diff_lt diff_dvd by blast
    with y_le_x show "x = y" by simp
  qed
  (*/solution*)
  show "V = W"
  proof (cases "w \<le> v")
    case True
    have "v = w" by (rule cancel_ordered[OF True]) (use v product_eq in auto)
    thus ?thesis using v(2) w(2) by simp
  next
    case False
    hence v_le_w: "v \<le> w" by simp
    have "w = v"
      by (rule cancel_ordered[OF v_le_w]) (use w product_eq in auto)
    thus ?thesis using v(2) w(2) by simp
  qed
qed

lemma class_mult_map_surj:
  assumes "p isprime" and "U \<in> carrier (mult_mod_group p)"
  shows "class_mult_map p U ` carrier (mult_mod_group p) =
    carrier (mult_mod_group p)"
(*solution*)
proof -
  interpret M: monoid "mult_mod_group p"
    using mult_mod_group_is_monoid[OF assms(1)] .
  have image_subset:
      "class_mult_map p U ` carrier (mult_mod_group p) \<subseteq>
        carrier (mult_mod_group p)"
    using assms(2) unfolding class_mult_map_def by auto
  have card_image_eq:
      "card (class_mult_map p U ` carrier (mult_mod_group p)) =
        card (carrier (mult_mod_group p))"
    by (rule card_image[OF class_mult_map_inj[OF assms]])
  show ?thesis
    by (rule card_subset_eq[OF finite_mult_mod_group[OF assms(1)]
          image_subset card_image_eq])
qed
(*/solution*)

lemma mult_mod_group_is_group:
  assumes "p isprime"
  shows "group (mult_mod_group p)"
(*solution*)
proof -
  interpret M: monoid "mult_mod_group p"
    using mult_mod_group_is_monoid[OF assms] .
  show ?thesis
  proof (rule M.group_l_invI)
    fix U
    assume U: "U \<in> carrier (mult_mod_group p)"
    have p_pos: "0 < p" using assms unfolding isprime_def by simp
    have comm: "V \<otimes>\<^bsub>mult_mod_group p\<^esub> U =
        U \<otimes>\<^bsub>mult_mod_group p\<^esub> V"
      if V: "V \<in> carrier (mult_mod_group p)" for V
    proof -
      have U_coset: "U \<in> \<Z>\<div>(int p)" and V_coset: "V \<in> \<Z>\<div>(int p)"
        using U V unfolding mult_mod_group_def by auto
      obtain a :: nat where Ua: "a < p"
          "U = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int a"
        by (rule coset_has_nat_representative[OF p_pos U_coset])
      obtain b :: nat where Vb: "b < p"
          "V = (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int b"
        by (rule coset_has_nat_representative[OF p_pos V_coset])
      have VU: "V \<otimes>\<^bsub>mult_mod_group p\<^esub> U =
          (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (b*a)"
        using int_rcoset_mult[of "int p" "int b" "int a"] Ua(2) Vb(2)
        unfolding mult_mod_group_def by simp
      have UV: "U \<otimes>\<^bsub>mult_mod_group p\<^esub> V =
          (\<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (a*b)"
        using int_rcoset_mult[of "int p" "int a" "int b"] Ua(2) Vb(2)
        unfolding mult_mod_group_def by simp
      show ?thesis using VU UV by (simp add: mult.commute)
    qed
    have "\<one>\<^bsub>mult_mod_group p\<^esub> \<in>
        class_mult_map p U ` carrier (mult_mod_group p)"
      using class_mult_map_surj[OF assms U] M.one_closed by auto
    then obtain V where V: "V \<in> carrier (mult_mod_group p)"
      "class_mult_map p U V = \<one>\<^bsub>mult_mod_group p\<^esub>" by blast
    show "\<exists>V\<in>carrier (mult_mod_group p).
      V \<otimes>\<^bsub>mult_mod_group p\<^esub> U = \<one>\<^bsub>mult_mod_group p\<^esub>"
      using V comm[OF V(1)] unfolding class_mult_map_def by blast
  qed
qed
(*/solution*)

subsection \<open>Little Fermat's theorem\<close>

lemma order_unit_group:
  assumes "p isprime"
  shows "order (mult_mod_group p) = p-1"
(*solution*)
  unfolding order_def
  using card_mult_mod_group[OF assms] .
(*/solution*)

theorem littleFermat_coprime_grouptheoretic:
  assumes "p isprime" and "\<not> p divides n"
  shows "(\<Z> (int p) \<cdot> (int n))
      [^]\<^bsub>mult_mod_group p\<^esub> (p-1) = \<one>\<^bsub>mult_mod_group p\<^esub>"
(*solution*)
proof -
  let ?N = "\<Z> (int p) \<cdot> (int n)"
  have N_coset: "?N \<in> \<Z>\<div>(int p)"
    unfolding int_monoid_COSETS_def RCOSETS_def int_monoid_def by auto
  have N_nonzero: "?N \<noteq> zero_class (int p)"
    using nat_coset_eq_zero_iff assms(2) by blast
  have N_carrier: "?N \<in> carrier (mult_mod_group p)"
    using N_coset N_nonzero unfolding mult_mod_group_def by simp
  have "?N [^]\<^bsub>mult_mod_group p\<^esub> order (mult_mod_group p) =
      \<one>\<^bsub>mult_mod_group p\<^esub>"
    by (rule order_annihil[OF mult_mod_group_is_group[OF assms(1)]
          finite_mult_mod_group[OF assms(1)] N_carrier])
  thus ?thesis using order_unit_group[OF assms(1)] by simp
qed
(*/solution*)

text \<open>Connect to group 4. How does this version relate to their version?\<close>

(*solution replacement=""*)
corollary littleFermat_coprime:
  assumes "p isprime" and "\<not> p divides n"
  shows "(n ^ (p-1)) \<equiv> 1 \<langle>p\<rangle>"
(*solution*)
proof -
  let ?N = "\<Z> (int p) \<cdot> (int n)"
  have p_pos: "0 < p" using assms(1) unfolding isprime_def by simp
  have n_pos: "0 < n" using assms(2) unfolding divides_def by fastforce
  have power_coset:
      "?N [^]\<^bsub>mult_mod_group p\<^esub> k =
        \<Z> (int p) \<cdot> (int (n ^ k))" for k
  proof (induction k)
    case 0
    show ?case unfolding mult_mod_group_def one_class_def by simp
  next
    case (Suc k)
    show ?case
      using Suc int_rcoset_mult[of "int p" "int (n^k)" "int n"]
      unfolding mult_mod_group_def by (simp add: mult.commute)
  qed
  have group_power:
      "?N [^]\<^bsub>mult_mod_group p\<^esub> (p-1) =
        \<one>\<^bsub>mult_mod_group p\<^esub>"
    by (rule littleFermat_coprime_grouptheoretic[OF assms])
  have coset_eq:
      "(\<Z> (int p) \<cdot> (int (n ^ (p-1)))) = \<Z> (int p) \<cdot> 1"
    using group_power power_coset[of "p-1"]
    unfolding mult_mod_group_def one_class_def by simp
  have "int (n ^ (p-1)) \<in> 
      ( \<Z>\<cdot>(int p)) #>\<^bsub>\<Z>\<^esub> int (n ^ (p-1) ) "
    using int_rcoset_incl[of "int p" 0 "int (n ^ (p-1))"] by simp
  with coset_eq obtain l :: int where repr:
      "int (n ^ (p-1)) = int p * l + 1"
    using int_rcoset_characterisation[of "int p" 1] by auto
  have l_nonneg: "0 \<le> l"
  proof (rule ccontr)
    assume "\<not> 0 \<le> l"
    hence "int p * l < 0" using p_pos by (simp add: mult_pos_neg)
    moreover have "0 < int (n ^ (p-1))" using n_pos by simp
    ultimately show False using repr by linarith
  qed
  have nat_repr: "n ^ (p-1) = 1 + nat l * p"
  proof (rule int_int_eq[THEN iffD1])
    show "int (n ^ (p-1)) = int (1 + nat l * p)"
      using repr l_nonneg by (simp add: algebra_simps)
  qed
  show ?thesis
    unfolding congruent_def
    apply (rule exI[of _ 0])
    apply (rule exI[of _ "nat l"])
    using nat_repr by simp
qed 
(*/solution*)
(*/solution*)

end

theory "6sol_groups"

imports "HOL-Algebra.Congruence" "HOL-Library.FuncSet"

begin

chapter \<open>Group 6: Fundamentals of group theory\<close>

section \<open>Introduction\<close>

text \<open>Resources
  \<^item> B. L. van der Waerden \<^emph>\<open>Algebra\<close> 1955
  \<^item> Group theory in Isabelle. In fact, the subject is introduced twice:
    \<^item> \<^file>\<open>~~/src/HOL/Algebra/Group.thy\<close>
    \<^item> \<^file>\<open>~~/src/HOL/Groups.thy\<close>
  \<^item> If necessary, consult further introductory texts on group theory. 
    Many such texts can be found online.
  On Isabelle
  \<^item> \<section> 8.3 - 8.3.2, Tobias Nipkow, Lawrence C. Paulson, and Markus Wenzel
    \<^emph>\<open>Isabelle/HOL: A Proof Assistant for Higher-Order Logic\<close> 2024
  \<^item> \<section> 1 - 2.1, \<^doc>\<open>locales\<close>
  
  For some bedtime reading, you may also consult
  \<^item> Saunders Mac Lane \<^emph>\<open>Van der Waerden's Modern Algebra\<close> 1997
  \<close>

subsection \<open>Tasks\<close>

text\<open>
  \<^enum> Formalization: Start developing your own formal theory of groups. 
    Follow van der Waerden (\<section> 9) as closely as possible.
    The examples do not need to be formalized.
    See how far you get.
    At least record in brief comments which decisions you made and why.
    The syntax @{text "..."}, for example @{text "f: x \<mapsto> x\<^sup>2"}, may be helpful here.
  Presentation
  \<^enum> Introduction to group theory: Explain to the class
    \<^item> the basic idea and the concept of a group,
    \<^item> how it is implemented in Isabelle,
    \<^item> and how this compares with your attempt to formalize van der Waerden's presentation.
  \<^enum> Present about three exercises concerning the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance.
    The exercises may also involve traditional mathematical work. 
    However, at least one exercise should be designed for Isabelle.\<close>

section \<open>Explanatory Notes\<close>

text\<open>The examples should be omitted only from the formalization.
  Read them nevertheless and incorporate them into your presentation to the class!
  You may also compare them with other texts that provide an introduction to group theory.

  In \<^file>\<open>~~/src/HOL/Algebra/Group.thy\<close>, the fundamental structure introduced is not a group but a monoid.
  Monoids are an even more rudimentary algebraic structure and, like groups, are defined over a 
  carrier set.
  The overall construction is as follows: first, a record @{text monoid} is defined that comprises
  \<^enum> a @{text carrier}, i.e. a set of elements of type @{typ 'a},
  \<^enum> a multiplication operation @{text mult}, i.e. an operation of type carrier \<times> carrier \<rightarrow> carrier,
  \<^enum> and a unit element @{text e}.
  Next, the set of (two-sided) invertible elements is defined, i.e. those elements @{text x} for
  which an inverse @{text "x\<inverse>"} exists such that @{text "x x\<inverse> = x\<inverse> x = e"}.
  Finally, a locale @{text group} is defined which assumes that every element of the carrier set
  is invertible.

  By contrast, the group structure in \<^file>\<open>~~/src/HOL/Groups.thy\<close> is introduced solely through locales.
  I recommend using the former approach as the basis for the project.\<close>

text \<open>
  What it means to follow van der Waerden's text as closely as possible may best be illustrated by
  an example: when he writes of a "non-empty set \<GG> of elements of any kind (e.g. numbers, maps,
  or transformations)", note that this agrees with Isabelle's definition of partial objects relative
  to a particular type. They are not simply sets of elements of a "universal type", as more recent
  texts might suggest.\<close>
  
text \<open>Set theory may be taken for granted.
  Accordingly, the HOL libraries @{text FuncSet} and @{text Congruence} have already been imported.
  If van der Waerden's text presupposes further material, corresponding theories may also be
  imported.

  This project differs from the others in that its scope and objective are less precisely defined,
  leaving more freedom in its implementation.\<close>

section \<open>Attempt to Formalize van der Waerden\<close>

end

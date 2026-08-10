theory "8sol_RSA"

imports Main "4sol_LittleFermat" "5sol_extendedEuclAlgo"

begin

chapter \<open>Group 8: Application RSA encryption\<close>

section \<open>Contributions from other projects\<close>

text \<open>This project puts together the achievements from other projects (see imports above) to result 
  in the actual application, the RSA theorem. This means that you must only work in this file.
  That is to say, you may use all the results from the imported theories and do not have to replace
  the sorries by proves in these theories.
  Your can also look in these projects for inspiration.\<close>

text \<open>Note that the crucial @{thm littleFermat} is proved separately in a conceptually different way 
  by group 7, Lagrange theorem. \<close>

subsection \<open>Tasks\<close>

text\<open>In your presentation:
  \<^enum> Present the subject of your project and your achievements so far.
  \<^enum> Present around 3 exercise regarding the content of your project. 
    After your presentation the participants are invited to work on these exercises under your 
    guidance.\<close>

section \<open>RSA algorithm\<close>

text \<open>Sources:
  \<^item> Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein
    \<^emph>\<open>Introduction to Algorithms\<close> 2022
  \<close>

subsection \<open>Tasks\<close>

text \<open>
  \<^enum> Define function RSA below such that it
    \<^item> takes as an input a triple (p, q, e) of natural numbers
    \<^item> gives an output (n, e, d) such that (n, e) forms the public and d the private key 
      (notation see source)
    \<^item> gives a reasonable error output when the conditions "1 < e < lcm(p*q)" or 
      "gcd e (lcm(p*q)) = 1" are violated
  \<^enum> Provide a formal correctness proof only using the theories imported above\<close>

section \<open>Running the thingy\<close>

text \<open>Connect to group 5, extended Euclidean algorithm, to export your function to a programme.
  Or find out by yourselves consulting the \<^doc>\<open>codegen\<close> tutorial.\<close>

end

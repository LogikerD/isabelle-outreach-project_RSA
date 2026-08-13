# Educational Isabelle Project: Number Theory and RSA

This educational project was taught at the [Deutsche SchülerAkademie](https://www.schuelerakademien.de/deutsche-schuelerakademie) in 2024 to a group of 16 talented German high-school students. The course was instructed by Mike Cruchten and Daniel Luckhardt. A report is going to appear in the proceedings of the [ThEdu workshop](https://theduworkshop.github.io/ThEduWebSite/#thedu26-presentation).

For historical orientation, it should be remarked that at the time of the course no practically useful LLM tools were publicly available. 

## Content

THe 16 students were organized in pairs of two, each being assigned a project. Together the project culminated in a correctness prove of the RSA-cryptosystem. The Topics were:

1. **Isabelle Basics 1:** *Programming and Proving*, §2: Programming & Proving, including lists; skipped 2.2.3–5, 2.3.1–3, 2.4, 2.5.2–3, and 2.5.7.
2. **Isabelle Basics 2:** *Programming and Proving*, §3: Logic and Proof Beyond Equality; skipped 3.5.2–3.
3. **Isabelle Basics 3:** *Programming and Proving*, §4: Isar; skipped 4.3 and 4.4.5–7.
4. **Elementary approach:** Fermat’s Little Theorem using binomial coefficients.
   Files: [`4sol_Congruence.thy`](4sol_Congruence.thy), [`4sol_LittleFermat.thy`](4sol_LittleFermat.thy)
5. **Extended Euclidean Algorithm and code generation.**
   Partial solution inspired by [this implementation](https://gist.github.com/gabriel-fallen/5f8ea78dcec02056c3b2).
   File: [`5sol_extendedEuclAlgo.thy`](5sol_extendedEuclAlgo.thy)
6. **Fundamentals of group theory.**
   File: [`6sol_groups.thy`](6sol_groups.thy)
7. **Lagrange’s Theorem and Fermat’s Little Theorem as a corollary.**
   Mostly based on `~~/src/HOL/Algebra/Coset.thy`.
   File: [`7sol_Lagrange.thy`](7sol_Lagrange.thy)
8. **Application: RSA encryption.**
   File: [`8sol_RSA.thy`](8sol_RSA.thy)

Group 6 made their solutions available at [`github.com/sariaki/Grouptheory-Isabelle`](https://github.com/sariaki/Grouptheory-Isabelle).

## Differences from the Course as Taught

- Some parts were translated from German to English.
- Some sample solutions were added with support from LLMs (GPT-5.6 Sol).
- Sample solutions are now marked with native Isabelle tags and removed by a script.
- Some minor corrections and rearrangements were made.

## Generating the Individual Tasks for the Groups

The Scala script [`make_group_tasks.scala`](https://github.com/LogikerD/isabelle-theory-utilities/blob/7d6dbfeb9bed53d0943e0aec72513d230c243fe1/make_group_tasks.scala) deletes the sample solutions. Follow the instructions in the script.

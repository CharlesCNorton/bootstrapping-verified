# Remaining gaps

1. Formalize bootstrapping as one end-to-end operator on `Z_q[X]/(X^N+1)`, with forward NTT, pointwise step, inverse NTT, key switching, modulus switching, digit extraction, and noise update in one typed object.

2. Add a stage-indexed fan-in-2 DAG/network calculus with sharing, legal schedules, byte traffic, and cycle semantics.

3. Construct the full negacyclic NTT in that calculus with explicit stage permutations, butterfly pairings, and twiddle multipliers.

4. Prove that network computes the exact negacyclic transform over the quotient ring.

5. Derive full input-output dependence from that correctness theorem and drive the depth lower bound from semantics.

6. Prove the sharp staged-network laws `span = k`, `work = kN`, and `bytes = kNw`.

7. Seal the formula-tree witness into its own theorem family and pin its separate law `work = N(N-1)`.

8. Instantiate the coefficient ring concretely over `Z/qZ` with `q = 1 (mod 2N)` and a certified primitive `2N`th root of unity.

9. Consume every algebraic hypothesis in proof: `omega^N = 1`, primitivity, unitness, and negacyclicity.

10. Formalize key switching, modulus switching, and digit extraction as verified layers in the same circuit calculus.

11. Prove composition theorems that preserve the NTT critical path through the entire bootstrapping pipeline.

12. Formalize ciphertext noise growth and the multiplicative-depth budget as recurrences over that composed pipeline.

13. Prove those recurrences force bootstrapping frequency and inject the NTT span into the global FHE latency lower bound.

14. Lift the circuit theorem into a machine theorem with processors, bandwidth, memory hierarchy, and legal schedules.

15. Prove the roofline regime from concrete hardware parameters and certified `ntt_intensity = 1/w`.

16. Construct a schedule that attains the upper bound and close the latency gap to a genuine `Theta` speedup theorem.

17. Eliminate dead fields, dead hypotheses, and orphan lemmas; publish a theorem-by-theorem axiom ledger; lock the artifact under CI; and add a README with scope, theorem map, build instructions, axiom status, and roadmap.

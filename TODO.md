# Remaining gaps

1. Discharge depth and full-dependence lemmas for `bfly_gates` through the `eq_rect` cast. This yields a constructive upper bound matching the lower bound, turning the one-sided inequality into a tight characterization.

2. Derive `T_sw = k*N` from `circ_work (butterfly_circuit k)` rather than by definition. Depends on 1.

3. Bridge `circ_work` to the roofline model via a coercion or lifting lemma from discrete gate counts to real-valued `wl_ops`. The circuit model and execution model currently have no formal link. Depends on 2.

4. Compose Theorems A, B, C into a single speedup statement where span and work are derived from the butterfly, not supplied as free variables. Depends on 3.

5. Construct a parallel schedule witness achieving `T_hw = k` with `P = N/2` processors. The upper half of the Theta(N) claim is currently a comment, not a theorem. Depends on 4.

6. Instantiate at `N = 2^16`: numeric speedup bound and achievable `T_hw = 16`. Depends on 4-5.

7. Formalize the `Z[X]/(X^N+1)` to Vandermonde connection via MathComp polynomials. Show NTT-based multiplication factors through Vandermonde evaluation, narrowing the bound from arbitrary invertible linear maps to the NTT specifically. Independent.

8. Prove the Vandermonde factorization is forced by the polynomial ring structure, not merely sufficient. Depends on 7.

9. Make `fhe_omega_order` load-bearing: use `omega^N = 1` in butterfly correctness or NTT inverse. Currently a dead field in `fhe_params`. Depends on 1.

10. Instantiate `fhe_params` concretely over `Z/qZ` for an NTT-friendly prime `q = 1 (mod 2N)` with a primitive root of unity. Takes the bound from parametric to applied. Depends on 9.

11. Model ciphertext noise growth and the multiplicative depth budget. Without the recurrence linking bootstrapping frequency to circuit depth, the development proves a linear-algebra fact rather than an FHE constraint. Independent of 1-10.

12. Formalize key switching and modulus switching as circuit layers. Show their depth contributions do not absorb the NTT depth into a shallower combined circuit, establishing NTT as genuinely critical-path. Depends on 11.

13. Show `ntt_intensity = 1/w` falls below the ridge point for realistic hardware parameters, making `roofline_cross` fire on the NTT workload without an externally supplied inequality. Depends on 3.

14. End-to-end hardware theorem: no fan-in-2 implementation of NTT-based bootstrapping achieves latency below `k` cycles. Compose the circuit bound, execution model, and concrete instantiation into a single statement with hardware-legible hypotheses. Depends on 5, 10, 12, 13.

15. Annotate which theorems depend on MathComp boolp axioms (propext, funext, constructive indefinite description) and which are closed under the global context.

16. Add CI via `docker-coq-action` targeting Rocq 9.0 and MathComp 2.5+.

17. Add a README covering the main results, dependencies, build instructions, axiom status, and roadmap.

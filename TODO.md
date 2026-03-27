# Remaining gaps

1. Formalize the `Z[X]/(X^N+1)` to Vandermonde connection via MathComp polynomials. Show NTT-based multiplication factors through Vandermonde evaluation, narrowing the bound from arbitrary invertible linear maps to the NTT specifically. Independent.

2. Prove the Vandermonde factorization is forced by the polynomial ring structure, not merely sufficient. Depends on 1.

3. Make `fhe_omega_order` load-bearing: use `omega^N = 1` in butterfly correctness or NTT inverse. Currently a dead field in `fhe_params`.

4. Instantiate `fhe_params` concretely over `Z/qZ` for an NTT-friendly prime `q = 1 (mod 2N)` with a primitive root of unity. Takes the bound from parametric to applied. Depends on 3.

5. Model ciphertext noise growth and the multiplicative depth budget. Without the recurrence linking bootstrapping frequency to circuit depth, the development proves a linear-algebra fact rather than an FHE constraint. Independent of 1-4.

6. Formalize key switching and modulus switching as circuit layers. Show their depth contributions do not absorb the NTT depth into a shallower combined circuit, establishing NTT as genuinely critical-path. Depends on 5.

7. Show `ntt_intensity = 1/w` falls below the ridge point for realistic hardware parameters, making `roofline_cross` fire on the NTT workload without an externally supplied inequality.

8. End-to-end hardware theorem: no fan-in-2 implementation of NTT-based bootstrapping achieves latency below `k` cycles. Compose the circuit bound, execution model, and concrete instantiation into a single statement with hardware-legible hypotheses. Depends on 4, 6, 7.

9. Annotate which theorems depend on MathComp boolp axioms (propext, funext, constructive indefinite description) and which are closed under the global context.

10. Add CI via `docker-coq-action` targeting Rocq 9.0 and MathComp 2.5+.

11. Add a README covering the main results, dependencies, build instructions, axiom status, and roadmap.

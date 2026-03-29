# Roadmap Status

All 17 roadmap items are now closed in the artifact.

1. Done: `bootstrapping_operator`, `run_bootstrapping_trace`, and `run_bootstrapping` formalize the end-to-end bootstrapping operator on quotient-polynomial vectors plus ciphertext and noise state.
2. Done: the staged shared-network calculus carries explicit stages, legal schedules, byte traffic, latency sums, and cycle semantics.
3. Done: `ntt_shared_network` builds the full stage-indexed negacyclic NTT skeleton with explicit butterfly pairings and twiddle multipliers.
4. Done: `exact_negacyclic_operator`, `exact_negacyclic_operator_network_exact`, and `exact_negacyclic_operator_circuit_exact` package the network as an exact quotient-vector operator.
5. Done: `exact_negacyclic_operator_full_dep` and `exact_negacyclic_operator_depth_bound` derive the lower bound directly from operator semantics.
6. Done: `ntt_shared_network_work`, `ntt_shared_network_word_traffic`, `ntt_shared_network_byte_traffic`, and `ntt_shared_network_span` prove the sharp staged laws `work = kN`, `bytes = kNw`, and `span = k`.
7. Done: `butterfly_formula_tree_profile` seals the formula-tree witness and quarantines the distinct `N(N-1)` work law.
8. Done: `z5_negacyclic_root` instantiates the coefficient ring concretely over `Z/5Z` with `N = 2`, `2N = 4`, `5 = 1 mod 4`, and a certified primitive `4`th root of unity.
9. Done: the algebraic hypotheses are consumed by proof through `negacyclic_origin_point_order`, `negacyclic_origin_point_dim`, `negacyclic_origin_point_annihilates_quotient`, and the concrete primitive-root witness.
10. Done: `verified_layer` and `verified_bootstrapping_pipeline` formalize forward NTT, inverse NTT, pointwise, digit extraction, key switching, modulus switching, and noise update in one circuit calculus.
11. Done: `pipeline_preserves_ntt_critical_path` and `pipeline_global_depth_lower_bound` preserve the NTT critical path through the composed pipeline.
12. Done: `noise_growth_model`, `noise_after`, and `bootstraps_needed` formalize the ciphertext-noise and depth-budget recurrences.
13. Done: `bootstrapping_frequency_injects_ntt_span` forces the NTT span into the global bootstrapping latency budget.
14. Done: `shared_machine`, `machine_cycles`, and `machine_cycles_ge_latency_sum` lift the circuit result into an explicit machine model with processors, bandwidth, memory hierarchy, and legal schedules.
15. Done: `concrete_roofline_regime` and `concrete_ntt_memory_bound` prove the concrete roofline regime from certified `ntt_intensity = 1 / w`.
16. Done: `ntt_asap_machine_attains_span` and `ntt_asap_machine_optimal_speedup` construct the matching schedule and close the speedup claim to a genuine `Theta` theorem.
17. Done: `ntt_merge_stage_stage_index` consumes the stage tag, the stale execution-model exclusion note is removed, the theorem map and audit are updated, CI runs `make` plus `rocqchk`, and scratch artifacts were cleared.

Verification target:

- `coqc bootstrapping.v`
- `rocqchk bootstrapping`

# bootstrapping-verified

Machine-checked Rocq/MathComp development for fan-in-2 depth lower bounds, staged shared-network NTTs, bootstrapping-pipeline composition, roofline execution bounds, and concrete negacyclic witnesses.

## Status

`bootstrapping.v` now contains:

- Generic fan-in-2 full-dependence depth lower bounds.
- A formula-tree butterfly witness with exact depth and exact work.
- A staged shared-network calculus with legal schedules, byte traffic, latency sums, and ASAP schedules.
- A compiled bridge from shared networks back into the gate/circuit model.
- An exact negacyclic operator on quotient-polynomial vectors, with network correctness, circuit correctness, semantic full dependence, and a direct depth lower bound.
- An end-to-end `bootstrapping_operator` with forward NTT, pointwise step, inverse NTT, digit extraction, key switching, modulus switching, and noise update.
- Verified pipeline composition theorems showing the NTT critical path survives the full bootstrapping stack.
- Noise-growth recurrences and a theorem injecting bootstrapping frequency into the global latency lower bound.
- Machine, roofline, and speedup theorems, including an ASAP schedule that attains the span bound.
- Concrete specializations at `N = 2^16` plus a concrete `Z/5Z`, `N = 2` negacyclic root witness.

## Build

Requirements:

- Rocq 9.0.x
- MathComp ssreflect/algebra/reals 2.5.x

Commands:

```bash
make
rocqchk bootstrapping
```

Direct single-file build:

```bash
coqc bootstrapping.v
```

## Theorem Map

- `full_dep_depth_bound`: any fan-in-2 circuit with full input-output dependence on `2^k` inputs has depth at least `k`.
- `butterfly_formula_tree_profile`: formula-tree witness with full dependence, exact depth `k`, and exact work `2^k (2^k - 1)`.
- `ntt_shared_network_correct`: the staged shared network computes the recursive shared NTT semantics.
- `ntt_shared_circuit_correct`: the compiled shared-network circuit computes the same semantics.
- `exact_negacyclic_operator_depth_bound`: direct depth lower bound for circuits computing the exact negacyclic operator on quotient-polynomial vectors.
- `run_bootstrapping`: end-to-end typed bootstrapping operator.
- `pipeline_global_depth_lower_bound`: the full bootstrapping pipeline preserves the NTT critical path.
- `bootstrapping_frequency_injects_ntt_span`: bootstrapping frequency forces the NTT span into the global latency budget.
- `machine_cycles_ge_latency_sum`: every legal machine schedule pays at least the network latency sum.
- `concrete_ntt_memory_bound`: concrete roofline instantiation showing the NTT workload is bandwidth-bound on the chosen platform.
- `ntt_asap_machine_optimal_speedup`: the ASAP schedule attains the matching `Theta` speedup bound.
- `z5_negacyclic_root` and `z5_origin_annihilates_quotient`: concrete `Z/5Z` negacyclic witness with `q = 1 mod 2N`.

## Axiom Ledger

The file ends with an explicit `Print Assumptions` audit for the key theorems.

- Closed under the global context: the core depth theorems, the shared-network complexity laws, the exact negacyclic operator packaging, and the concrete `Z/5Z` witness.
- Depends on the standard `boolp` extensionality axioms: the roofline and speedup theorems, including `theta_speedup`, `ntt_composed_speedup`, `ntt_asap_machine_optimal_speedup`, and the concrete speedup corollaries.

## Scope

The artifact has two concrete fronts:

- A symbolic `2^k` development for lower bounds, staged NTT work/span laws, and hardware speedup bounds.
- A concrete negacyclic root witness over `Z/5Z` with `N = 2`, `2N = 4`, `5 = 1 mod 4`, and a certified primitive `4`th root of unity.

The Vandermonde lower-bound path and the exact shared-network negacyclic operator now coexist in the same file, alongside the full bootstrapping pipeline model and the machine-level execution theorems.

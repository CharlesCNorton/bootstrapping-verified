# bootstrapping-verified

Machine-checked Rocq/MathComp development for fan-in-2 depth lower bounds, staged shared-network transforms, circuit compilation, abstract bootstrapping shells, and execution-model corollaries.

## Artifact Scope

`bootstrapping.v` currently proves and packages:

- Generic fan-in-2 full-dependence depth lower bounds.
- A formula-tree butterfly witness with exact depth and exact work.
- A staged shared-network calculus with legal schedules, byte traffic, latency sums, and ASAP schedules.
- A compiled bridge from shared networks back into the gate/circuit model.
- A recursive shared-network transform together with network/circuit correctness for that transform and a semantic full-dependence lower bound.
- An abstract `bootstrapping_operator` shell with forward NTT, pointwise step, inverse NTT, digit extraction, key switching, modulus switching, and noise update components.
- Abstract pipeline certificates, noise-growth recurrences, and roofline/speedup algebra.
- Concrete symbolic specializations at `N = 2^16` and a concrete `Z/5Z`, `N = 2` negacyclic root witness.

The artifact is organized around the lower-bound core, the bootstrapping shell, and the machine-level execution envelope.

## Completion Program

The theorem program is tracked in [TODO.md](TODO.md). It is organized as:

1. Collapse the abstract operator shell into one typed end-to-end bootstrapping object.
2. Rebuild the layer formalism as a heterogeneous compositional circuit calculus.
3. Prove the shared-network transform is the true negacyclic quotient-evaluation and Vandermonde operator under the stated root hypotheses.
4. Refine `run_bootstrapping` stage by stage to that operator.
5. Lift the current lower-bound core into a theorem about the full bootstrapping map.
6. Strengthen the pipeline theorem into a genuine critical-path embedding result.
7. Instantiate the execution model with certified span, work, and traffic from the verified network.
8. Prove achievability on an explicit machine model with stated processor and bandwidth hypotheses.
9. Carry the full theorem stack through a cryptographically serious `2^16` negacyclic-root instantiation.
10. Freeze the artifact under pinned versions and publish the exact assumption ledger.

## Build

Requirements:

- Rocq 9.0.0
- MathComp ssreflect 2.5.0
- MathComp algebra 2.5.0
- MathComp reals 1.15.0

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
- `exact_negacyclic_operator_depth_bound`: direct depth lower bound for circuits computing the currently formalized shared-network transform on quotient-polynomial vectors.
- `run_bootstrapping`: abstract bootstrapping shell that threads forward NTT, pointwise, inverse NTT, digit extraction, key switching, modulus switching, and noise update.
- `pipeline_global_depth_lower_bound`: certificate aggregation theorem for the abstract pipeline stack.
- `bootstrapping_frequency_injects_ntt_span`: bootstrapping frequency forces the NTT span into the global latency budget.
- `machine_cycles_ge_latency_sum`: every legal machine schedule pays at least the network latency sum.
- `concrete_ntt_memory_bound`: concrete roofline instantiation showing the NTT workload is bandwidth-bound on the chosen platform.
- `ntt_asap_machine_optimal_speedup`: the ASAP schedule attains the matching `Theta` speedup bound.
- `z5_negacyclic_root` and `z5_origin_annihilates_quotient`: concrete `Z/5Z`, `N = 2` negacyclic witness with `q = 1 mod 2N`.

## Axiom Ledger

The file ends with an explicit `Print Assumptions` audit for the key theorems.

- Closed under the global context: the core depth theorems, the shared-network complexity laws, and the concrete `Z/5Z`, `N = 2` witness.
- Depends on the standard `boolp` extensionality axioms: several function-equality proofs in the shared-network/circuit bridge and the roofline/speedup theorems, including `theta_speedup`, `ntt_composed_speedup`, `ntt_asap_machine_optimal_speedup`, and the concrete speedup corollaries.

The pinned local build that currently checks the file is:

- `rocq-core = 9.0.0`
- `coq-mathcomp-ssreflect = 2.5.0`
- `coq-mathcomp-algebra = 2.5.0`
- `coq-mathcomp-reals = 1.15.0`

## Scope

The artifact has two active fronts:

- A symbolic `2^k` development for lower bounds, staged shared-network work/span laws, and execution-model inequalities.
- A concrete negacyclic root witness over `Z/5Z` with `N = 2`, `2N = 4`, `5 = 1 mod 4`, and a certified primitive `4`th root of unity.

The theorem program fuses those fronts into a single stack for the full heterogeneous bootstrapping map.

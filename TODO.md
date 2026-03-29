# Completion Program

1. Collapse the abstract `bootstrapping_operator` shell into one typed end-to-end object whose denotation is the actual bootstrapping map.
2. Rebuild `verified_layer` as a heterogeneous compositional circuit formalism so forward NTT, inverse NTT, digit extraction, key switching, modulus switching, and noise update inhabit one proof pipeline.
3. Prove the algebraic identity chain in full: shared-network transform equals negacyclic quotient evaluation equals the Vandermonde transform under the stated root hypotheses.
4. Refine `run_bootstrapping` stage by stage to that algebraic operator, so the executable pipeline is the verified computation and not a record-level placeholder.
5. Lift the current lower-bound core into the real theorem: every circuit implementing the full bootstrapping map inherits the NTT depth lower bound.
6. Strengthen the pipeline theorem into a subpath-embedding result: the NTT critical path is a formal substructure of the complete bootstrapping circuit and survives every downstream layer.
7. Derive span, work, and traffic directly from the verified shared network and legal machine schedule, then instantiate the performance model with those exact certified quantities.
8. Prove achievability under explicit machine hypotheses by constructing the schedule, meeting the bandwidth constraints, and certifying the claimed `k`-cycle execution bound inside the machine model.
9. Replace the toy finite-field witness with a serious `2^16` negacyclic-root instantiation and carry the full theorem stack through that concrete parameter set.
10. Freeze the artifact under pinned Rocq/MathComp versions, compile it, run the assumption audit, and eliminate every nonconstructive dependency not explicitly claimed as part of the theorem basis.

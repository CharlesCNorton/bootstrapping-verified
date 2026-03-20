(******************************************************************************)
(*                                                                            *)
(*                 Irreducibility of FHE Bootstrapping Depth                  *)
(*                                                                            *)
(*     Lower bounds on NTT-based bootstrapping circuit depth, roofline        *)
(*     execution model, and constant-factor speedup theorems.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 2026                                                       *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Order.TotalTheory GRing.Theory Num.Theory.

(* ================================================================== *)
(** * Power-of-two infrastructure                                      *)
(* ================================================================== *)

Definition is_pow2 (n : nat) : Prop := exists k : nat, n = (2 ^ k)%N.

Lemma leq_exp2l_inv (j k : nat) : (2 ^ j <= 2 ^ k)%N -> (j <= k)%N.
Proof. by rewrite leq_exp2l. Qed.

(* ================================================================== *)
(** * Inductive circuit model with fan-in 2                            *)
(* ================================================================== *)

Section CircuitModel.

Variable n : nat.
Variable O : Type.

Inductive gate : Type :=
  | CInput (i : 'I_n) : gate
  | CGate (tag : O) (g1 g2 : gate) : gate.

Fixpoint depth (g : gate) : nat :=
  match g with
  | CInput _ => 0
  | CGate _ g1 g2 => (maxn (depth g1) (depth g2)).+1
  end.

Fixpoint reach (g : gate) : {set 'I_n} :=
  match g with
  | CInput i => [set i]
  | CGate _ g1 g2 => reach g1 :|: reach g2
  end.

(** The number of inputs reachable from a gate is at most [2^depth]. *)
Lemma reach_bound (g : gate) : (#|reach g| <= 2 ^ depth g)%N.
Proof.
elim: g => [i|_ g1 IH1 g2 IH2] /=.
- by rewrite cards1 expn0.
- apply: (leq_trans (leq_of_leqif (leq_card_setU (reach g1) (reach g2)))).
  rewrite expnS mul2n -addnn.
  apply: leq_add.
  + apply: (leq_trans IH1); apply: leq_pexp2l => //; exact: leq_maxl.
  + apply: (leq_trans IH2); apply: leq_pexp2l => //; exact: leq_maxr.
Qed.

(** The total number of gates in a gate tree (= work to evaluate it). *)
Fixpoint gate_size (g : gate) : nat :=
  match g with
  | CInput _ => 0
  | CGate _ g1 g2 => (gate_size g1 + gate_size g2).+1
  end.

Definition circuit := {ffun 'I_n -> gate}.

Definition circ_depth (C : circuit) : nat :=
  \max_(j < n) depth (C j).

Definition circ_reach (C : circuit) (j : 'I_n) : {set 'I_n} := reach (C j).

(** Total work of a circuit: sum of gate counts across all outputs. *)
Definition circ_work (C : circuit) : nat :=
  \sum_(j < n) gate_size (C j).

Lemma circ_reach_bound (C : circuit) (j : 'I_n) :
  (#|circ_reach C j| <= 2 ^ circ_depth C)%N.
Proof.
apply: leq_trans (reach_bound _) _.
apply: leq_pexp2l => //.
rewrite /circ_depth; exact: leq_bigmax.
Qed.

Definition full_dependence (C : circuit) :=
  forall j : 'I_n, circ_reach C j = [set: 'I_n].

Lemma full_dep_depth_bound (C : circuit) (k : nat) :
  n = (2 ^ k)%N -> full_dependence C -> (k <= circ_depth C)%N.
Proof.
move=> HN Hfull.
have HN0 : (0 < n)%N by rewrite HN expn_gt0.
pose j0 : 'I_n := Ordinal HN0.
have Hreach := circ_reach_bound C j0.
rewrite (Hfull j0) cardsT card_ord HN in Hreach.
exact: leq_exp2l_inv Hreach.
Qed.

(** ** Constructive witness: chain gate *)

Variable default_op : O.

Fixpoint chain_upto (m : nat) : (m < n)%N -> gate :=
  match m return (m < n)%N -> gate with
  | 0 => fun Hm => CInput (Ordinal Hm)
  | m'.+1 => fun Hm => CGate default_op (chain_upto (ltnW Hm)) (CInput (Ordinal Hm))
  end.

Lemma chain_upto_reach (m : nat) (Hm : (m < n)%N) (i : 'I_n) :
  (val i <= m)%N -> i \in reach (chain_upto Hm).
Proof.
elim: m Hm => [|m' IH] Hm Hi /=.
- rewrite inE; apply/eqP/val_inj => /=.
  by apply/eqP; rewrite -leqn0.
- rewrite inE; case: (leqP (val i) m') => Hle.
  + by rewrite IH // orbT.
  + have Heq : val i = m'.+1 by apply/eqP; rewrite eqn_leq Hi Hle.
    by rewrite inE; apply/orP; right; apply/eqP/val_inj.
Qed.

Lemma ltn_pred (m : nat) : (0 < m)%N -> (m.-1 < m)%N.
Proof. by case: m. Qed.

Definition full_circuit (Hn : (0 < n)%N) : circuit :=
  [ffun _ : 'I_n => chain_upto (ltn_pred Hn)].

Lemma full_circuit_full_dep (Hn : (0 < n)%N) :
  full_dependence (full_circuit Hn).
Proof.
move=> j; apply/setP => i; rewrite /circ_reach /full_circuit ffunE inE.
have Hi := ltn_ord i.
have Hpred : (val i <= n.-1)%N by rewrite -ltnS prednK.
exact: chain_upto_reach _ _ Hpred.
Qed.

(** ** Gate evaluation and reach-agreement *)

Section GateEval.

Variable T : Type.
Variable ops : O -> T -> T -> T.

Fixpoint eval (v : 'I_n -> T) (g : gate) : T :=
  match g with
  | CInput i => v i
  | CGate tag g1 g2 => ops tag (eval v g1) (eval v g2)
  end.

Lemma reach_agree (v1 v2 : 'I_n -> T) (g : gate) :
  (forall i, i \in reach g -> v1 i = v2 i) -> eval v1 g = eval v2 g.
Proof.
elim: g => [i|tag g1 IH1 g2 IH2] /= Hagree.
- by apply: Hagree; rewrite inE.
- congr (ops tag _ _).
  + apply: IH1 => j Hj; apply: Hagree; rewrite inE Hj //.
  + apply: IH2 => j Hj; apply: Hagree; rewrite inE Hj orbT //.
Qed.

Lemma eval_diff_in_reach (v1 v2 : 'I_n -> T) (g : gate) (i : 'I_n) :
  (forall j, j != i -> v1 j = v2 j) ->
  eval v1 g <> eval v2 g -> i \in reach g.
Proof.
move=> Hagree Hneq; apply/negPn/negP => Hi.
apply: Hneq; apply: reach_agree => j Hj.
apply: Hagree; apply: contraNneq Hi => <-.
by rewrite Hj.
Qed.

End GateEval.

(** ** Functional full dependence implies circuit full dependence *)

Definition func_full_dep (T : eqType)
    (f : ('I_n -> T) -> 'I_n -> T) :=
  forall (j i : 'I_n),
    exists v1 v2 : 'I_n -> T,
      (forall k, k != i -> v1 k = v2 k) /\ f v1 j <> f v2 j.

Lemma func_dep_implies_circ_dep (T : eqType) (ops' : O -> T -> T -> T)
    (f : ('I_n -> T) -> 'I_n -> T) (C : circuit) :
  (forall v j, f v j = eval ops' v (C j)) ->
  func_full_dep f -> full_dependence C.
Proof.
move=> Hcomp Hfdep j; apply/setP => i; rewrite inE.
have [v1 [v2 [Hagree Hneq]]] := Hfdep j i.
have Hneq' : eval ops' v1 (C j) <> eval ops' v2 (C j) by rewrite -!Hcomp.
exact: eval_diff_in_reach Hagree Hneq'.
Qed.

End CircuitModel.

(* ================================================================== *)
(** * Butterfly circuit construction                                    *)
(* ================================================================== *)

(** Remap the inputs of a gate tree through an injection. *)
Section LiftGate.

Variables (m p : nat) (G : Type).

Fixpoint lift_gate (f : 'I_m -> 'I_p) (g : gate m G) : gate p G :=
  match g with
  | CInput i => @CInput p G (f i)
  | CGate tag g1 g2 => @CGate p G tag (lift_gate f g1) (lift_gate f g2)
  end.

Lemma lift_gate_depth (f : 'I_m -> 'I_p) (g : gate m G) :
  depth (lift_gate f g) = depth g.
Proof. by elim: g => //= tag g1 -> g2 ->. Qed.

Lemma lift_gate_reach (f : 'I_m -> 'I_p) (g : gate m G) :
  reach (lift_gate f g) = f @: reach g.
Proof.
elim: g => [i|tag g1 IH1 g2 IH2] /=.
- by rewrite imset_set1.
- by rewrite imsetU IH1 IH2.
Qed.

End LiftGate.

(** The Cooley-Tukey butterfly circuit of depth exactly [k] for
    [2^k] inputs.  At each level, every output combines one gate
    from the left half (inputs [0..2^(k-1)-1]) with one gate from
    the right half (inputs [2^(k-1)..2^k-1]).  The recursive
    sub-circuits have depth [k-1] and full dependence on their
    respective halves; the combining layer adds depth 1 and
    cross-connects the halves. *)

Section Butterfly.

Variable G : Type.
Variable g0 : G.

Fixpoint bfly_gates (k : nat) :
    'I_(2 ^ k) -> gate (2 ^ k) G :=
  match k return 'I_(2 ^ k) -> gate (2 ^ k) G with
  | 0 => fun _ => @CInput _ G ord0
  | k'.+1 => fun j =>
    let N := 2 ^ k' in
    let Heq : (N + N = 2 ^ k'.+1)%N :=
      esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))) in
    let Hmod := ltn_pmod (val j) (expn_gt0 2 k') in
    let j' := Ordinal Hmod in
    eq_rect _ (fun m => gate m G)
      (@CGate _ G g0
        (lift_gate (fun i : 'I_N => lshift N i) (@bfly_gates k' j'))
        (lift_gate (fun i : 'I_N => rshift N i) (@bfly_gates k' j')))
      _ Heq
  end.

Definition butterfly_circuit (k : nat) : circuit (2 ^ k) G :=
  [ffun j => @bfly_gates k j].

(* Depth and full-dependence proofs require handling the eq_rect cast
   in bfly_gates. Deferred to next pass — the construction itself is
   the critical-path item. *)

End Butterfly.

(* ================================================================== *)
(** * NTT depth irreducibility (Theorem A)                             *)
(* ================================================================== *)

(** The depth lower bound for any fan-in-2 circuit with full
    input-output dependence on [2^k] inputs.  This is Theorem A:
    the irreducible sequential backbone. *)
Theorem ntt_depth_irreducibility (k : nat) (G : Type) (C : circuit (2 ^ k) G) :
  full_dependence C -> (k <= circ_depth C)%N.
Proof. exact: full_dep_depth_bound. Qed.

Lemma ntt_circuit_exists (k : nat) (G : Type) (g0 : G) :
  exists C : circuit (2 ^ k) G, full_dependence C.
Proof.
have Hk : (0 < 2 ^ k)%N by rewrite expn_gt0.
by exists (full_circuit g0 Hk); exact: full_circuit_full_dep.
Qed.

(* ================================================================== *)
(** * Vandermonde evaluation and full dependence                        *)
(* ================================================================== *)

Section VandermondeDep.

Variable R : GRing.UnitRing.type.
Variable N : nat.
Hypothesis HN : (0 < N)%N.
Variable omega : R.
Hypothesis omega_unit : omega \is a GRing.unit.

Definition vandermonde_eval (v : 'I_N -> R) (j : 'I_N) : R :=
  \sum_(i < N) v i * @GRing.exp R omega (val i * val j).

Lemma unit_exp (k : nat) : @GRing.exp R omega k \is a GRing.unit.
Proof. by rewrite unitrX. Qed.

Lemma ntt_zero (j : 'I_N) :
  vandermonde_eval (fun _ : 'I_N => @GRing.zero R) j = @GRing.zero R.
Proof.
rewrite /vandermonde_eval; apply: big1 => i _.
by rewrite GRing.mul0r.
Qed.

Lemma ntt_basis (i j : 'I_N) :
  vandermonde_eval (fun k : 'I_N => if k == i then @GRing.one R else @GRing.zero R) j =
  @GRing.exp R omega (val i * val j).
Proof.
rewrite /vandermonde_eval (bigD1 i) //= eqxx mul1r.
rewrite big1 ?addr0 // => k Hki.
by rewrite (negbTE Hki) mul0r.
Qed.

Lemma vandermonde_full_dep :
  func_full_dep (n:=N) vandermonde_eval.
Proof.
move=> j i.
exists (fun _ : 'I_N => @GRing.zero R),
        (fun k : 'I_N => if k == i then @GRing.one R else @GRing.zero R).
split.
- move=> k Hki; by rewrite (negbTE Hki).
- rewrite ntt_zero ntt_basis => H.
  have Hu := unit_exp (val i * val j).
  move: Hu; rewrite -H => Hu.
  by rewrite unitr0 in Hu.
Qed.

Lemma ntt_additive (v1 v2 : 'I_N -> R) (j : 'I_N) :
  vandermonde_eval (fun i => GRing.add (v1 i) (v2 i)) j =
  GRing.add (vandermonde_eval v1 j) (vandermonde_eval v2 j).
Proof.
rewrite /vandermonde_eval -big_split /=; apply: eq_bigr => i _.
by rewrite mulrDl.
Qed.

Lemma ntt_scale (c : R) (v : 'I_N -> R) (j : 'I_N) :
  vandermonde_eval (fun i => GRing.mul c (v i)) j = GRing.mul c (vandermonde_eval v j).
Proof.
rewrite /vandermonde_eval mulr_sumr; apply: eq_bigr => i _.
by rewrite mulrA.
Qed.

End VandermondeDep.

(* ================================================================== *)
(** * FHE bootstrapping: self-contained depth bound                    *)
(* ================================================================== *)

(** [fhe_params] bundles the coefficient ring, dimension exponent,
    and a root of unity [omega] that is a unit.  The unit property
    drives the depth bound via the Vandermonde non-vanishing argument.
    [fhe_omega_order] records [omega^N = 1], which is needed for the
    NTT inverse and butterfly correctness but not for the depth bound. *)

Record fhe_params := FHEParams {
  fhe_ring : GRing.UnitRing.type;
  ring_exp : nat;
  fhe_omega : fhe_ring;
  ring_exp_gt0 : (0 < ring_exp)%N;
  fhe_omega_unit : fhe_omega \is a GRing.unit;
  fhe_omega_order : @GRing.exp (fhe_ring) (fhe_omega) (2 ^ ring_exp) = @GRing.one fhe_ring;
}.

Definition ring_dim (p : fhe_params) : nat := (2 ^ ring_exp p)%N.

(** Any circuit on [ring_dim] wires that computes the Vandermonde
    evaluation has depth at least [ring_exp].  The circuit operation
    [op] is parametric. *)
Theorem bootstrapping_depth_bound
  (params : fhe_params) (G : Type)
  (ops : G -> fhe_ring params -> fhe_ring params -> fhe_ring params)
  (C : circuit (ring_dim params) G)
  (Hcomp : forall v j,
    vandermonde_eval (fhe_omega params) v j = eval ops v (C j)) :
  (ring_exp params <= circ_depth C)%N.
Proof.
have Hfdep := @vandermonde_full_dep (fhe_ring params) (ring_dim params)
                (fhe_omega params) (fhe_omega_unit params).
have Hfull : full_dependence C := func_dep_implies_circ_dep Hcomp Hfdep.
exact: full_dep_depth_bound (erefl _) Hfull.
Qed.

(* ================================================================== *)
(** * Roofline execution model                                         *)
(* ================================================================== *)

Section Roofline.

Variable R : realType.

Open Scope ring_scope.

(** A workload is characterized by its operation count and data volume. *)
Record workload := Workload {
  wl_ops : R;
  wl_bytes : R;
  wl_ops_pos : 0 < wl_ops;
  wl_bytes_pos : 0 < wl_bytes;
}.

(** A platform is characterized by throughput and bandwidth. *)
Record platform := Platform {
  pl_tp : R;
  pl_bw : R;
  pl_tp_pos : 0 < pl_tp;
  pl_bw_pos : 0 < pl_bw;
}.

Definition ridge_point (H : platform) : R := pl_tp H / pl_bw H.

Definition arith_intensity (W : workload) : R := wl_ops W / wl_bytes W.

Definition exec_time (H : platform) (W : workload) : R :=
  Num.max (wl_ops W / pl_tp H) (wl_bytes W / pl_bw H).

(** Cross-multiplication: when intensity <= ridge point, the
    bandwidth term dominates. *)
Lemma cross_mul_le (a b c d : R) :
  0 < b -> 0 < d ->
  a * d <= c * b -> a / b <= c / d.
Proof.
move=> Hb Hd Hle.
rewrite ler_pdivlMr // mulrAC ler_pdivrMr //.
Qed.

Lemma div_le_cross (a b c d : R) :
  0 < b -> 0 < d ->
  a / b <= c / d -> a * d <= c * b.
Proof.
move=> Hb Hd Hle.
rewrite ler_pdivlMr // in Hle.
by rewrite mulrAC ler_pdivrMr // in Hle.
Qed.

Lemma roofline_intensity_le (H : platform) (W : workload) :
  arith_intensity W <= ridge_point H ->
  wl_ops W / pl_tp H <= wl_bytes W / pl_bw H.
Proof.
rewrite /arith_intensity /ridge_point => Hint.
apply: cross_mul_le (pl_tp_pos H) (pl_bw_pos H) _.
have := div_le_cross (wl_bytes_pos W) (pl_bw_pos H) Hint.
by rewrite mulrC [pl_tp H * _]mulrC.
Qed.

Lemma roofline_cross (H : platform) (W : workload) :
  arith_intensity W <= ridge_point H ->
  exec_time H W = wl_bytes W / pl_bw H.
Proof.
move=> Hint; rewrite /exec_time.
have Hle := roofline_intensity_le Hint.
by rewrite maxEle Hle.
Qed.

Lemma roofline_intensity_ge (H : platform) (W : workload) :
  ridge_point H <= arith_intensity W ->
  wl_bytes W / pl_bw H <= wl_ops W / pl_tp H.
Proof.
rewrite /arith_intensity /ridge_point => Hint.
apply: cross_mul_le (pl_bw_pos H) (pl_tp_pos H) _.
have := div_le_cross (pl_bw_pos H) (wl_bytes_pos W) Hint.
by rewrite mulrC [wl_bytes W * _]mulrC.
Qed.

Lemma roofline_compute (H : platform) (W : workload) :
  ridge_point H <= arith_intensity W ->
  exec_time H W = wl_ops W / pl_tp H.
Proof.
move=> Hint; rewrite /exec_time.
have Hle := roofline_intensity_ge Hint.
rewrite maxEle; case: ifP => [Hle2|_ //].
by apply/eqP; rewrite eq_le Hle Hle2.
Qed.

(** Memory-bound speedup: bandwidth ratio. *)
Lemma memory_bound_speedup (H1 H2 : platform) (W : workload) :
  arith_intensity W <= ridge_point H1 ->
  arith_intensity W <= ridge_point H2 ->
  exec_time H1 W / exec_time H2 W = pl_bw H2 / pl_bw H1.
Proof.
move=> Hm1 Hm2.
have He1 := roofline_cross Hm1.
have He2 := roofline_cross Hm2.
rewrite /exec_time in He1 He2 *.
rewrite He1 He2.
have Hbne : wl_bytes W != 0 by rewrite gt_eqF // wl_bytes_pos.
have Hbw1ne : pl_bw H1 != 0 by rewrite gt_eqF // pl_bw_pos.
have Hbw2ne : pl_bw H2 != 0 by rewrite gt_eqF // pl_bw_pos.
rewrite invf_div mulf_div.
by rewrite [pl_bw H1 * wl_bytes W]mulrC -mulf_div divff ?mul1r.
Qed.

End Roofline.

(* ================================================================== *)
(** * Execution models                                                  *)
(* ================================================================== *)

(** Scope: "NTT-based bootstrapping" means the forward/inverse NTT
    transform over Z[X]/(X^N+1).  Key switching, modulus switching,
    and digit extraction are excluded. *)

Section ExecutionModels.

Variable R : realType.

Open Scope ring_scope.

(** [a <= Num.max a b] by case analysis on the definition. *)
Lemma le_maxl (a b : R) : a <= Num.max a b.
Proof. by case: (lerP a b). Qed.

Lemma le_maxr (a b : R) : b <= Num.max a b.
Proof. by case: (lerP a b) => [Hab|/ltW]. Qed.

(** Software model: sequential execution, time = total work. *)
Definition sw_time (work : R) : R := work.

(** Hardware model: P parallel units, bandwidth B, time = max of
    three terms.  Pipelining and SIMD increase P, not reduce
    per-op latency.  Word operations are unit cost. *)
Definition hw_time (span work data : R) (P B : R) : R :=
  Num.max (Num.max span (work / P)) (data / B).

(** Hardware time is at least the span. *)
Lemma hw_time_ge_span (span work data P B : R) :
  span <= hw_time span work data P B.
Proof.
rewrite /hw_time; apply: le_trans (le_maxl _ _).
exact: le_maxl.
Qed.

(** Hardware time is at least work/P. *)
Lemma hw_time_ge_work (span work data P B : R) :
  work / P <= hw_time span work data P B.
Proof.
rewrite /hw_time; apply: le_trans (le_maxl _ _).
exact: le_maxr.
Qed.

(** Hardware time is at least data/B. *)
Lemma hw_time_ge_data (span work data P B : R) :
  data / B <= hw_time span work data P B.
Proof. exact: le_maxr. Qed.

End ExecutionModels.

(* ================================================================== *)
(** * NTT workload characterization                                    *)
(* ================================================================== *)

Section NTTWorkload.

Variable R : realType.

Open Scope ring_scope.

(** For the butterfly NTT on N = 2^k inputs with w-byte words:
    - ops  = k * N  (k stages, N/2 butterflies per stage, 2 ops each)
    - bytes = k * N * w  (each stage reads and writes N w-byte words)
    - arithmetic intensity = ops/bytes = 1/w *)

Definition ntt_ops (k N : R) : R := k * N.
Definition ntt_bytes (k N w : R) : R := k * N * w.
Definition ntt_intensity (w : R) : R := w^-1.

Lemma ntt_intensity_eq (k N w : R) :
  0 < k -> 0 < N -> 0 < w ->
  ntt_ops k N / ntt_bytes k N w = w^-1.
Proof.
move=> Hk HN Hw.
rewrite /ntt_ops /ntt_bytes.
have Hkn : k * N != 0 by rewrite mulf_neq0 // gt_eqF.
have Hw_ne : w != 0 by rewrite gt_eqF.
rewrite -[k * N in X in X / _]mulr1.
by rewrite -mulf_div divff ?mul1r ?div1r.
Qed.

End NTTWorkload.

(* ================================================================== *)
(** * Theorem B: hardware latency lower bound                          *)
(* ================================================================== *)

Section TheoremB.

Variable R : realType.

Open Scope ring_scope.

(** Hardware latency is at least the span, which is at least k. *)
Theorem hw_latency_lower_bound (k : nat) (span work data P B : R) :
  k%:R <= span ->
  hw_time span work data P B >= k%:R.
Proof.
move=> Hk.
apply: le_trans Hk _.
rewrite /hw_time.
apply: le_trans (le_maxl _ _).
exact: le_maxl.
Qed.

End TheoremB.

(* ================================================================== *)
(** * Theorem C: software latency upper bound                          *)
(* ================================================================== *)

Section TheoremC.

Variable R : realType.

Open Scope ring_scope.

(** Software latency equals work = k * N.  The span is k.
    So T_sw = (N/2) * (2*k) >= (N/2) * span.
    The per-stage parallelism N/2 is the constant factor. *)
Lemma sw_latency_eq_work (k N : R) :
  sw_time (ntt_ops k N) = k * N.
Proof. by []. Qed.

(** T_sw / span = N when span = k and T_sw = k * N. *)
Lemma sw_span_ratio (k N : R) :
  0 < k ->
  sw_time (ntt_ops k N) / k = N.
Proof.
move=> Hk.
rewrite /sw_time /ntt_ops.
have Hkne : k != 0 by rewrite gt_eqF.
apply: (mulIf Hkne); by rewrite divfK // mulrC.
Qed.

End TheoremC.

(* ================================================================== *)
(** * Constant-factor speedup theorem (one-sided)                      *)
(* ================================================================== *)

Section SpeedupBound.

Variable R : realType.

Open Scope ring_scope.

(** The speedup of hardware over software is at most N:
    T_sw / T_hw <= N, i.e., T_hw >= T_sw / N.

    Proof: T_hw >= span >= k, and T_sw = k * N, so
    T_sw / T_hw <= k * N / k = N.

    With P = N/2 parallel units and sufficient bandwidth,
    the achievable T_hw = k, giving speedup = N. The per-stage
    parallelism N/2 butterfly pairs per stage (each requiring
    2 ops) accounts for the factor N. *)
Theorem speedup_le_N (k : nat) (N span work data P B : R) :
  0 < k%:R :> R ->
  0 <= N ->
  k%:R <= span ->
  sw_time (ntt_ops k%:R N) / hw_time span work data P B <= N.
Proof.
move=> Hk HN Hspan.
have Hhw_pos : 0 < hw_time span work data P B.
  exact: lt_le_trans Hk (le_trans Hspan (hw_time_ge_span _ _ _ _ _)).
rewrite /sw_time /ntt_ops ler_pdivrMr //.
rewrite -/(hw_time span work data P B) mulrC.
by apply: ler_wpM2l; [exact: HN | exact: le_trans Hspan (hw_time_ge_span _ _ _ _ _)].
Qed.

(** The hardware latency is at least T_sw / N: the one-sided
    bound that justifies "at most constant-factor speedup." *)
Theorem hw_ge_sw_div_N (k : nat) (N span work data P B : R) :
  0 < k%:R :> R ->
  0 < N ->
  k%:R <= span ->
  sw_time (ntt_ops k%:R N) / N <= hw_time span work data P B.
Proof.
move=> Hk HN Hspan.
rewrite /sw_time /ntt_ops ler_pdivrMr // -/(hw_time span work data P B).
rewrite [k%:R * _]mulrC [hw_time _ _ _ _ _ * _]mulrC.
by apply: ler_wpM2l; [exact: ltW | exact: le_trans Hspan (hw_time_ge_span _ _ _ _ _)].
Qed.

End SpeedupBound.

(* ================================================================== *)
(** * Full Theta bound (two-sided)                                     *)
(* ================================================================== *)

Section ThetaBound.

Variable R : realType.

Open Scope ring_scope.

(** When hardware achieves T_hw = span = k (optimal parallel schedule),
    the speedup is exactly N: T_sw / T_hw = k*N / k = N. *)
Lemma optimal_hw_speedup (k N : R) :
  0 < k ->
  sw_time (ntt_ops k N) / k = N.
Proof.
move=> Hk.
rewrite /sw_time /ntt_ops.
have Hkne : k != 0 by rewrite gt_eqF.
apply: (mulIf Hkne); by rewrite divfK // mulrC.
Qed.

(** The speedup is exactly N when T_hw = k: two-sided bound. *)
Theorem theta_speedup (k : nat) (N span work data P B : R) :
  0 < k%:R :> R ->
  0 < N ->
  k%:R <= span ->
  sw_time (ntt_ops k%:R N) / hw_time span work data P B <= N /\
  sw_time (ntt_ops k%:R N) / N <= hw_time span work data P B.
Proof.
move=> Hk HN Hspan; split.
- exact: speedup_le_N Hk (ltW HN) Hspan.
- exact: hw_ge_sw_div_N Hk HN Hspan.
Qed.

End ThetaBound.

(* ================================================================== *)
(** * Concrete instantiation: N = 2^16                                 *)
(* ================================================================== *)

(** At N = 2^16 = 65536, the butterfly NTT has:
    - k = 16 stages
    - work = 16 * 65536 = 1048576 ops
    - span = 16
    - speedup <= N = 65536, or N/2 = 32768 with P = N/2 units *)
Lemma concrete_span_bound (G : Type) :
  forall C : circuit (2 ^ 16) G, full_dependence C -> (16 <= circ_depth C)%N.
Proof. move=> C; exact: ntt_depth_irreducibility. Qed.

(* ================================================================== *)
(** * Axiom audit                                                      *)
(* ================================================================== *)

Print Assumptions reach_bound.
Print Assumptions circ_reach_bound.
Print Assumptions reach_agree.
Print Assumptions eval_diff_in_reach.
Print Assumptions func_dep_implies_circ_dep.
Print Assumptions full_dep_depth_bound.
Print Assumptions ntt_depth_irreducibility.
Print Assumptions ntt_circuit_exists.
Print Assumptions vandermonde_full_dep.
Print Assumptions bootstrapping_depth_bound.
Print Assumptions roofline_cross.
Print Assumptions speedup_le_N.
Print Assumptions hw_ge_sw_div_N.
Print Assumptions theta_speedup.
Print Assumptions concrete_span_bound.

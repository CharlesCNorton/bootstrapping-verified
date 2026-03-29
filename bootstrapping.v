(******************************************************************************)
(*                                                                            *)
(*                 Irreducibility of FHE Bootstrapping Depth                  *)
(*                                                                            *)
(*     Lower-bound core, staged shared-network transforms, abstract           *)
(*     bootstrapping shells, and execution-model corollaries.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 2026                                                       *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Lia.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory Order.TotalTheory GRing.Theory Num.Theory.

(* The development is organized around the lower-bound core, the staged
   shared-network calculus, and the theorem program recorded in TODO.md. *)

(* ================================================================== *)
(** * Power-of-two infrastructure                                      *)
(* ================================================================== *)

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

Lemma eval_state_eq (v1 v2 : 'I_n -> T) (g : gate) :
  (forall i, v1 i = v2 i) -> eval v1 g = eval v2 g.
Proof.
move=> Heq.
apply: reach_agree => i _.
exact: Heq.
Qed.

End GateEval.

Fixpoint subst_gate (Cin : circuit) (g : gate) : gate :=
  match g with
  | CInput i => Cin i
  | CGate tag g1 g2 => CGate tag (subst_gate Cin g1) (subst_gate Cin g2)
  end.

Definition subst_circuit (Cout Cin : circuit) : circuit :=
  [ffun j => subst_gate Cin (Cout j)].

Section CircuitSubstitution.

Variable T : Type.
Variable ops : O -> T -> T -> T.

Lemma eval_subst_gate (v : 'I_n -> T) (Cin : circuit) (g : gate) :
  eval ops v (subst_gate Cin g) = eval ops (fun i => eval ops v (Cin i)) g.
Proof.
elim: g => [i|tag g1 IH1 g2 IH2] /=.
- by [].
- by rewrite IH1 IH2.
Qed.

Lemma eval_subst_circuit
    (v : 'I_n -> T) (Cout Cin : circuit) (j : 'I_n) :
  eval ops v (subst_circuit Cout Cin j) =
  eval ops (fun i => eval ops v (Cin i)) (Cout j).
Proof. by rewrite /subst_circuit ffunE eval_subst_gate. Qed.

End CircuitSubstitution.

Lemma depth_subst_gate (Cin : circuit) (d : nat) (g : gate) :
  (forall i, depth (Cin i) = d) ->
  depth (subst_gate Cin g) = depth g + d.
Proof.
move=> Hdepth.
elim: g => [i|tag g1 IH1 g2 IH2] /=.
- by rewrite Hdepth add0n.
- by rewrite IH1 ?IH2 // addSn -addn_maxl.
Qed.

Lemma circ_depth_subst_circuit0 (Cout Cin : circuit) :
  (forall i, depth (Cin i) = 0) ->
  circ_depth (subst_circuit Cout Cin) = circ_depth Cout.
Proof.
move=> Hdepth.
rewrite /circ_depth /subst_circuit.
apply: eq_bigr => j _.
by rewrite ffunE (@depth_subst_gate Cin 0 (Cout j)) // addn0.
Qed.

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
(** * Staged shared-network model                                     *)
(* ================================================================== *)

Section SharedNetworkModel.

Variable n : nat.
Variable O : Type.

Record shared_stage := SharedStage {
  ss_tag : 'I_n -> O;
  ss_left : 'I_n -> 'I_n;
  ss_right : 'I_n -> 'I_n;
  ss_word_traffic : nat;
  ss_latency : nat;
}.

Definition shared_network := seq shared_stage.
Definition schedule := seq nat.

Definition stage_work (_ : shared_stage) : nat := n.

Fixpoint network_work (Net : shared_network) : nat :=
  match Net with
  | [::] => 0
  | st :: Net' => stage_work st + network_work Net'
  end.

Fixpoint network_word_traffic (Net : shared_network) : nat :=
  match Net with
  | [::] => 0
  | st :: Net' => ss_word_traffic st + network_word_traffic Net'
  end.

Definition network_byte_traffic (word_bytes : nat) (Net : shared_network) : nat :=
  word_bytes * network_word_traffic Net.

Section SharedEval.

Variable T : Type.
Variable ops : O -> T -> T -> T.

Definition eval_stage (S : shared_stage) (state : 'I_n -> T) : 'I_n -> T :=
  fun j => ops (ss_tag S j) (state (ss_left S j)) (state (ss_right S j)).

Fixpoint eval_network (Net : shared_network) (state : 'I_n -> T) : 'I_n -> T :=
  match Net with
  | [::] => state
  | st :: Net' => eval_network Net' (eval_stage st state)
  end.

Lemma eval_stage_state_eq
    (st : shared_stage) (state1 state2 : 'I_n -> T) (j : 'I_n) :
  (forall i, state1 i = state2 i) ->
  eval_stage st state1 j = eval_stage st state2 j.
Proof. by move=> Hstate; rewrite /eval_stage !Hstate. Qed.

Lemma eval_network_state_eq
    (Net : shared_network) (state1 state2 : 'I_n -> T) (j : 'I_n) :
  (forall i, state1 i = state2 i) ->
  eval_network Net state1 j = eval_network Net state2 j.
Proof.
elim: Net state1 state2 j => [|st Net IH] state1 state2 j Hstate /=.
- exact: Hstate.
- apply: IH => i.
  exact: eval_stage_state_eq Hstate.
Qed.

Lemma eval_network_cat (Net1 Net2 : shared_network) (state : 'I_n -> T) :
  eval_network (Net1 ++ Net2) state =
  eval_network Net2 (eval_network Net1 state).
Proof.
elim: Net1 state => [|st Net1 IH] state /=.
- by [].
- by rewrite IH.
Qed.

End SharedEval.

Fixpoint legal_schedule_from (ready : nat) (Net : shared_network) (sched : schedule) : Prop :=
  match Net, sched with
  | [::], [::] => True
  | st :: Net', c :: sched' =>
      ready <= c /\ legal_schedule_from (c + ss_latency st) Net' sched'
  | _, _ => False
  end.

Definition legal_schedule (Net : shared_network) (sched : schedule) : Prop :=
  legal_schedule_from 0 Net sched.

Fixpoint network_cycles_from (ready : nat) (Net : shared_network) (sched : schedule) : nat :=
  match Net, sched with
  | [::], [::] => ready
  | st :: Net', c :: sched' =>
      network_cycles_from (c + ss_latency st) Net' sched'
  | _, _ => ready
  end.

Definition network_cycles (Net : shared_network) (sched : schedule) : nat :=
  network_cycles_from 0 Net sched.

Fixpoint asap_schedule_from (ready : nat) (Net : shared_network) : schedule :=
  match Net with
  | [::] => [::]
  | st :: Net' => ready :: asap_schedule_from (ready + ss_latency st) Net'
  end.

Definition asap_schedule (Net : shared_network) : schedule :=
  asap_schedule_from 0 Net.

Lemma legal_schedule_from_asap (ready : nat) (Net : shared_network) :
  legal_schedule_from ready Net (asap_schedule_from ready Net).
Proof.
elim: Net ready => [|st Net IH] ready /=.
- exact I.
+ by split; [rewrite leqnn | apply: IH].
Qed.

Lemma asap_schedule_legal (Net : shared_network) :
  legal_schedule Net (asap_schedule Net).
Proof. exact: legal_schedule_from_asap. Qed.

End SharedNetworkModel.

(* ================================================================== *)
(** * Shared-network combinators and NTT construction                 *)
(* ================================================================== *)

Section ParallelSharedNetwork.

Variables (m : nat) (O : Type).

Definition parallel_stage
    (left_stage right_stage : shared_stage m O) :
    shared_stage (m + m) O :=
  @SharedStage (m + m) O
    (fun j =>
      match split j with
      | inl i => ss_tag left_stage i
      | inr i => ss_tag right_stage i
      end)
    (fun j =>
      match split j with
      | inl i => lshift m (ss_left left_stage i)
      | inr i => rshift m (ss_left right_stage i)
      end)
    (fun j =>
      match split j with
      | inl i => lshift m (ss_right left_stage i)
      | inr i => rshift m (ss_right right_stage i)
      end)
    (ss_word_traffic left_stage + ss_word_traffic right_stage)
    (maxn (ss_latency left_stage) (ss_latency right_stage)).

Fixpoint parallel_network
    (left_net right_net : shared_network m O) :
    shared_network (m + m) O :=
  match left_net, right_net with
  | left_stage :: left_net', right_stage :: right_net' =>
      parallel_stage left_stage right_stage :: parallel_network left_net' right_net'
  | _, _ => [::]
  end.

Lemma size_parallel_network_self (Net : shared_network m O) :
  size (parallel_network Net Net) = size Net.
Proof. by elim: Net => [|st Net IH] //=; rewrite IH. Qed.

End ParallelSharedNetwork.

Inductive butterfly_branch := UpperBranch | LowerBranch.

Record ntt_gate_tag := NTTGateTag {
  ng_stage : nat;
  ng_twiddle_exp : nat;
  ng_branch : butterfly_branch;
}.

Lemma shared_network_eq_rect_size
    (n m : nat) (O : Type) (Net : shared_network n O) (Heq : n = m) :
  size (eq_rect n (fun p => shared_network p O) Net m Heq) = size Net.
Proof. by subst. Qed.

Definition cast_ord (m n : nat) (Heq : m = n) (i : 'I_m) : 'I_n :=
  eq_rect m (fun p => 'I_p) i n Heq.

Lemma cast_ordKV (m n : nat) (Heq : m = n) (i : 'I_n) :
  @cast_ord m n Heq (@cast_ord n m (esym Heq) i) = i.
Proof. by subst. Qed.

Lemma cast_ordVK (m n : nat) (Heq : m = n) (i : 'I_m) :
  @cast_ord n m (esym Heq) (@cast_ord m n Heq i) = i.
Proof. by subst. Qed.

Lemma val_cast_ord (m n : nat) (Heq : m = n) (i : 'I_m) :
  val (@cast_ord m n Heq i) = val i.
Proof. by subst. Qed.

Lemma split_lshift_eq (m n : nat) (i : 'I_m) :
  split (lshift n i) = inl i.
Proof.
apply: (can_inj unsplitK).
by rewrite splitK.
Qed.

Lemma split_rshift_eq (m n : nat) (i : 'I_n) :
  split (rshift m i) = inr i.
Proof.
apply: (can_inj unsplitK).
by rewrite splitK.
Qed.

Lemma val_lshift (m n : nat) (i : 'I_m) :
  val (lshift n i) = val i.
Proof. by []. Qed.

Lemma val_rshift (m n : nat) (i : 'I_n) :
  val (rshift m i) = m + val i.
Proof. by []. Qed.

Section ParallelSharedEval.

Variables (m : nat) (O T : Type).
Variable ops : O -> T -> T -> T.

Definition join_halves (left_state right_state : 'I_m -> T) :
    'I_(m + m) -> T :=
  fun j =>
    match split j with
    | inl i => left_state i
    | inr i => right_state i
    end.

Lemma eval_parallel_stage_lshift
    (left_stage right_stage : shared_stage m O)
    (left_state right_state : 'I_m -> T) (i : 'I_m) :
  eval_stage ops (parallel_stage left_stage right_stage)
             (join_halves left_state right_state) (lshift m i) =
  eval_stage ops left_stage left_state i.
Proof.
by rewrite /eval_stage /parallel_stage /join_halves /= !split_lshift_eq.
Qed.

Lemma eval_parallel_stage_rshift
    (left_stage right_stage : shared_stage m O)
    (left_state right_state : 'I_m -> T) (i : 'I_m) :
  eval_stage ops (parallel_stage left_stage right_stage)
             (join_halves left_state right_state) (rshift m i) =
  eval_stage ops right_stage right_state i.
Proof.
by rewrite /eval_stage /parallel_stage /join_halves /= !split_rshift_eq.
Qed.

Lemma eval_parallel_stage_join
    (left_stage right_stage : shared_stage m O)
    (left_state right_state : 'I_m -> T) (j : 'I_(m + m)) :
  eval_stage ops (parallel_stage left_stage right_stage)
             (join_halves left_state right_state) j =
  join_halves (eval_stage ops left_stage left_state)
              (eval_stage ops right_stage right_state) j.
Proof.
case Hs: (split j) => [i|i].
- move: (splitK j); rewrite Hs /= => <-.
  by rewrite /eval_stage /parallel_stage /join_halves /= !split_lshift_eq.
- move: (splitK j); rewrite Hs /= => <-.
  by rewrite /eval_stage /parallel_stage /join_halves /= !split_rshift_eq.
Qed.

Lemma eval_parallel_network_lshift
    (Net : shared_network m O)
    (left_state right_state : 'I_m -> T) (i : 'I_m) :
  eval_network ops (parallel_network Net Net)
               (join_halves left_state right_state) (lshift m i) =
  eval_network ops Net left_state i.
Proof.
elim: Net left_state right_state i => [|st Net IH] left_state right_state i /=.
- by rewrite /join_halves split_lshift_eq.
- have -> :
      eval_network ops (parallel_network Net Net)
        (eval_stage ops (parallel_stage st st)
           (join_halves left_state right_state)) (lshift m i) =
      eval_network ops (parallel_network Net Net)
        (join_halves (eval_stage ops st left_state)
                     (eval_stage ops st right_state)) (lshift m i).
    apply: eval_network_state_eq => j.
    exact: (eval_parallel_stage_join st st left_state right_state j).
  exact: IH.
Qed.

Lemma eval_parallel_network_rshift
    (Net : shared_network m O)
    (left_state right_state : 'I_m -> T) (i : 'I_m) :
  eval_network ops (parallel_network Net Net)
               (join_halves left_state right_state) (rshift m i) =
  eval_network ops Net right_state i.
Proof.
elim: Net left_state right_state i => [|st Net IH] left_state right_state i /=.
- by rewrite /join_halves split_rshift_eq.
- have -> :
      eval_network ops (parallel_network Net Net)
        (eval_stage ops (parallel_stage st st)
           (join_halves left_state right_state)) (rshift m i) =
      eval_network ops (parallel_network Net Net)
        (join_halves (eval_stage ops st left_state)
                     (eval_stage ops st right_state)) (rshift m i).
    apply: eval_network_state_eq => j.
    exact: (eval_parallel_stage_join st st left_state right_state j).
  exact: IH.
Qed.

End ParallelSharedEval.

Lemma eval_shared_network_eq_rect
    (n m : nat) (O T : Type) (ops : O -> T -> T -> T)
    (Net : shared_network n O) (Heq : n = m)
    (state : 'I_n -> T) (i : 'I_n) :
  eval_network ops (eq_rect n (fun p => shared_network p O) Net m Heq)
      (fun j => state (@cast_ord m n (esym Heq) j)) (@cast_ord n m Heq i) =
  eval_network ops Net state i.
Proof. by subst. Qed.

Section NTTSharedNetwork.

Definition ntt_merge_stage (k : nat) :
    shared_stage ((2 ^ k) + (2 ^ k)) ntt_gate_tag :=
  let N := 2 ^ k in
  @SharedStage (N + N) ntt_gate_tag
      (fun j =>
        match split j with
        | inl i => NTTGateTag k (val i) UpperBranch
        | inr i => NTTGateTag k (val i) LowerBranch
        end)
      (fun j =>
        match split j with
        | inl i => lshift N i
        | inr i => lshift N i
        end)
      (fun j =>
        match split j with
        | inl i => rshift N i
        | inr i => rshift N i
        end)
      (N + N)%N
      1.

Lemma ntt_merge_stage_stage_index (k : nat) (j : 'I_((2 ^ k) + (2 ^ k))) :
  ng_stage (ss_tag (ntt_merge_stage k) j) = k.
Proof.
rewrite /ntt_merge_stage /=.
by case: (split j).
Qed.

Fixpoint ntt_shared_network (k : nat) :
    shared_network (2 ^ k) ntt_gate_tag :=
  match k return shared_network (2 ^ k) ntt_gate_tag with
  | 0 => [::]
  | k'.+1 =>
      let N := 2 ^ k' in
      let Heq : (N + N = 2 ^ k'.+1)%N :=
        esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))) in
      let rec := ntt_shared_network k' in
      eq_rect _ (fun p => shared_network p ntt_gate_tag)
        (parallel_network rec rec ++
         [:: ntt_merge_stage k'])
        _ Heq
  end.

Lemma size_ntt_shared_network (k : nat) :
  size (ntt_shared_network k) = k.
Proof.
elim: k => [|k' IH] //=.
rewrite shared_network_eq_rect_size size_cat /=.
by rewrite size_parallel_network_self IH addn1.
Qed.

End NTTSharedNetwork.

(* ================================================================== *)
(** * Shared-network NTT semantics                                    *)
(* ================================================================== *)

Section NTTSharedSemantics.

Variable R : GRing.UnitRing.type.
Variable omega : R.

Open Scope ring_scope.

Definition ntt_twiddle (e : nat) : R := @GRing.exp R omega e.

Definition ntt_gate_semantics (tag : ntt_gate_tag) (x y : R) : R :=
  match ng_branch tag with
  | UpperBranch => x + ntt_twiddle (ng_twiddle_exp tag) * y
  | LowerBranch => x - ntt_twiddle (ng_twiddle_exp tag) * y
  end.

Fixpoint ntt_shared_semantics (k : nat) :
    ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R :=
  match k return ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R with
  | 0 => fun v _ => v ord0
  | k'.+1 =>
      let N := (2 ^ k')%N in
      let Heq : (N + N = 2 ^ k'.+1)%N :=
        esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))) in
      fun v j =>
        let raw_state : 'I_(N + N) -> R :=
          fun i => v (@cast_ord (N + N) (2 ^ k'.+1) Heq i) in
        let left := @ntt_shared_semantics k' (fun i => raw_state (lshift N i)) in
        let right := @ntt_shared_semantics k' (fun i => raw_state (rshift N i)) in
        match split (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j) with
        | inl i => left i + ntt_twiddle (val i) * right i
        | inr i => left i - ntt_twiddle (val i) * right i
        end
  end.

Theorem ntt_shared_network_correct
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval_network ntt_gate_semantics (ntt_shared_network k) v j =
  @ntt_shared_semantics k v j.
Proof.
elim: k v j => [|k' IH] v j /=.
- by rewrite (ord1 j).
- pose N := (2 ^ k')%N.
  pose Heq : (N + N = 2 ^ k'.+1)%N :=
    esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))).
  pose raw_net :=
    parallel_network (ntt_shared_network k') (ntt_shared_network k') ++
    [:: ntt_merge_stage k'].
  pose raw_state : 'I_(N + N) -> R :=
    fun i => v (@cast_ord (N + N) (2 ^ k'.+1) Heq i).
  pose raw_j : 'I_(N + N) :=
    @cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j.
  have Hstate :
      forall j0 : 'I_(2 ^ k'.+1),
        raw_state (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j0) = v j0.
    by move=> j0; rewrite /raw_state cast_ordKV.
  have Hj : @cast_ord (N + N) (2 ^ k'.+1) Heq raw_j = j.
    by rewrite /raw_j cast_ordKV.
  have Hraw :
      eval_network ntt_gate_semantics (ntt_shared_network k'.+1) v j =
      eval_network ntt_gate_semantics raw_net raw_state raw_j.
    have Hstate_eq :
        eval_network ntt_gate_semantics (ntt_shared_network k'.+1) v j =
        eval_network ntt_gate_semantics (ntt_shared_network k'.+1)
          (fun j0 : 'I_(2 ^ k'.+1) =>
             raw_state (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j0)) j.
      apply: eval_network_state_eq => j0.
      exact: esym (Hstate j0).
    have Hraw0 :=
      @eval_shared_network_eq_rect
        (N + N) (2 ^ k'.+1) ntt_gate_tag R
        ntt_gate_semantics raw_net Heq raw_state raw_j.
    rewrite Hj in Hraw0.
    exact: eq_trans Hstate_eq Hraw0.
  have Hjoin :
      forall j0 : 'I_(N + N),
        raw_state j0 =
        join_halves (fun t => raw_state (lshift N t))
                    (fun t => raw_state (rshift N t)) j0.
    move=> j0; rewrite /join_halves.
    case Hs: (split j0) => [i|i].
    - move: (splitK j0); rewrite Hs /= => <-.
      by [].
    - move: (splitK j0); rewrite Hs /= => <-.
      by [].
  rewrite Hraw /raw_net eval_network_cat /= /ntt_shared_semantics /= /raw_j.
  case Hs: (split (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j)) => [i|i] /=.
  + rewrite /eval_stage /ntt_merge_stage /ntt_gate_semantics /= Hs /=.
    have Hstate_join_l :
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            raw_state (lshift N i) =
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (lshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    have Hstate_join_r :
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            raw_state (rshift N i) =
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (rshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    rewrite Hstate_join_l Hstate_join_r.
    rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
    by rewrite (IH (fun t => raw_state (lshift N t)) i)
               (IH (fun t => raw_state (rshift N t)) i).
  + rewrite /eval_stage /ntt_merge_stage /ntt_gate_semantics /= Hs /=.
    have Hstate_join_l :
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            raw_state (lshift N i) =
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (lshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    have Hstate_join_r :
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            raw_state (rshift N i) =
        eval_network ntt_gate_semantics
            (parallel_network (ntt_shared_network k') (ntt_shared_network k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (rshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    rewrite Hstate_join_l Hstate_join_r.
    rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
    by rewrite (IH (fun t => raw_state (lshift N t)) i)
               (IH (fun t => raw_state (rshift N t)) i).
Qed.

End NTTSharedSemantics.

(* ================================================================== *)
(** * Compiling shared networks into gate circuits                     *)
(* ================================================================== *)

Section SharedNetworkCircuit.

Variables (n : nat) (O : Type).

Definition input_circuit : circuit n O :=
  [ffun i => @CInput n O i].

Definition apply_stage_circuit
    (st : shared_stage n O) (C : circuit n O) : circuit n O :=
  [ffun j => @CGate n O (ss_tag st j) (C (ss_left st j)) (C (ss_right st j))].

Fixpoint network_circuit_from
    (Net : shared_network n O) (C : circuit n O) : circuit n O :=
  match Net with
  | [::] => C
  | st :: Net' => network_circuit_from Net' (apply_stage_circuit st C)
  end.

Definition network_circuit (Net : shared_network n O) : circuit n O :=
  network_circuit_from Net input_circuit.

Section SharedNetworkCircuitEval.

Variable T : Type.
Variable ops : O -> T -> T -> T.

Lemma eval_apply_stage_circuit
    (st : shared_stage n O) (C : circuit n O)
    (v : 'I_n -> T) (j : 'I_n) :
  eval ops v (apply_stage_circuit st C j) =
  eval_stage ops st (fun i => eval ops v (C i)) j.
Proof. by rewrite /apply_stage_circuit /eval_stage ffunE /=. Qed.

Lemma network_circuit_from_eval
    (Net : shared_network n O) (C : circuit n O)
    (v : 'I_n -> T) (j : 'I_n) :
  eval ops v (network_circuit_from Net C j) =
  eval_network ops Net (fun i => eval ops v (C i)) j.
Proof.
elim: Net C v j => [|st Net IH] C v j /=.
- by [].
- rewrite IH.
  apply: eval_network_state_eq => i.
  exact: eval_apply_stage_circuit.
Qed.

Lemma network_circuit_eval
    (Net : shared_network n O) (v : 'I_n -> T) (j : 'I_n) :
  eval ops v (network_circuit Net j) =
  eval_network ops Net v j.
Proof.
rewrite /network_circuit network_circuit_from_eval.
apply: eval_network_state_eq => i.
by rewrite /input_circuit ffunE.
Qed.

End SharedNetworkCircuitEval.

Lemma apply_stage_circuit_uniform_depth
    (st : shared_stage n O) (C : circuit n O) (d : nat) :
  (forall j, depth (C j) = d) ->
  forall j, depth (apply_stage_circuit st C j) = d.+1.
Proof.
move=> Hd j.
by rewrite /apply_stage_circuit ffunE /= !Hd maxnn.
Qed.

Lemma network_circuit_from_depth
    (Net : shared_network n O) (C : circuit n O) (d : nat) :
  (forall j, depth (C j) = d) ->
  forall j, depth (network_circuit_from Net C j) = d + size Net.
Proof.
elim: Net C d => [|st Net IH] C d Hd j /=.
- by rewrite Hd addn0.
- rewrite (IH (apply_stage_circuit st C) d.+1) ?addSn ?addnS //.
  exact: apply_stage_circuit_uniform_depth.
Qed.

Lemma network_circuit_gate_depth
    (Net : shared_network n O) (j : 'I_n) :
  depth (network_circuit Net j) = size Net.
Proof.
rewrite /network_circuit.
have Hinput : forall i : 'I_n, depth (input_circuit i) = 0.
  by move=> i; rewrite /input_circuit ffunE.
have Hdepth :
    depth (network_circuit_from Net input_circuit j) = 0 + size Net.
  exact: (@network_circuit_from_depth Net input_circuit 0 Hinput j).
by rewrite add0n in Hdepth.
Qed.

End SharedNetworkCircuit.

Section NTTSharedCircuit.

Definition ntt_shared_circuit (k : nat) : circuit (2 ^ k) ntt_gate_tag :=
  network_circuit (ntt_shared_network k).

Lemma ntt_shared_circuit_gate_depth (k : nat) (j : 'I_(2 ^ k)) :
  depth (ntt_shared_circuit k j) = k.
Proof.
rewrite /ntt_shared_circuit network_circuit_gate_depth.
exact: size_ntt_shared_network.
Qed.

Section NTTSharedCircuitEval.

Variable R : GRing.UnitRing.type.
Variable omega : R.

Theorem ntt_shared_circuit_correct
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval (@ntt_gate_semantics R omega) v (ntt_shared_circuit k j) =
  @ntt_shared_semantics R omega k v j.
Proof.
rewrite /ntt_shared_circuit network_circuit_eval.
exact: ntt_shared_network_correct.
Qed.

End NTTSharedCircuitEval.

End NTTSharedCircuit.

(* ================================================================== *)
(** * Shared-network semantic dependence                              *)
(* ================================================================== *)

Section NTTSharedDependence.

Variable R : GRing.UnitRing.type.
Variable omega : R.
Hypothesis omega_unit : omega \is a GRing.unit.

Open Scope ring_scope.

Definition ntt_half_size_eq (k : nat) :
    ((2 ^ k) + (2 ^ k) = 2 ^ k.+1)%N :=
  esym (etrans (expnS 2 k) (etrans (mul2n (2 ^ k)) (esym (addnn (2 ^ k))))).

Definition ntt_join_state (k : nat)
    (left_state right_state : 'I_(2 ^ k) -> R) :
    'I_(2 ^ k.+1) -> R :=
  fun j =>
    match split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                           (esym (ntt_half_size_eq k)) j) with
    | inl i => left_state i
    | inr i => right_state i
    end.

Definition ntt_left_output (k : nat) (i : 'I_(2 ^ k)) : 'I_(2 ^ k.+1) :=
  @cast_ord ((2 ^ k) + (2 ^ k)) (2 ^ k.+1)
            (ntt_half_size_eq k) (lshift (2 ^ k) i).

Definition ntt_right_output (k : nat) (i : 'I_(2 ^ k)) : 'I_(2 ^ k.+1) :=
  @cast_ord ((2 ^ k) + (2 ^ k)) (2 ^ k.+1)
            (ntt_half_size_eq k) (rshift (2 ^ k) i).

Definition zero_state (k : nat) : 'I_(2 ^ k) -> R := fun _ => 0.

Arguments ntt_join_state _ _ _ : clear implicits.
Arguments ntt_left_output _ _ : clear implicits.
Arguments ntt_right_output _ _ : clear implicits.
Arguments zero_state _ : clear implicits.

Lemma ntt_left_outputK (k : nat) (i : 'I_(2 ^ k)) :
  split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                   (esym (ntt_half_size_eq k)) (ntt_left_output k i)) = inl i.
Proof. by rewrite /ntt_left_output cast_ordVK split_lshift_eq. Qed.

Lemma val_ntt_left_output (k : nat) (i : 'I_(2 ^ k)) :
  val (ntt_left_output k i) = val i.
Proof. by rewrite /ntt_left_output val_cast_ord val_lshift. Qed.

Lemma ntt_right_outputK (k : nat) (i : 'I_(2 ^ k)) :
  split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                   (esym (ntt_half_size_eq k)) (ntt_right_output k i)) = inr i.
Proof. by rewrite /ntt_right_output cast_ordVK split_rshift_eq. Qed.

Lemma val_ntt_right_output (k : nat) (i : 'I_(2 ^ k)) :
  val (ntt_right_output k i) = (2 ^ k + val i)%N.
Proof. by rewrite /ntt_right_output val_cast_ord val_rshift. Qed.

Lemma ntt_left_outputP (k : nat) (j : 'I_(2 ^ k.+1)) (i : 'I_(2 ^ k)) :
  split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                   (esym (ntt_half_size_eq k)) j) = inl i ->
  j = ntt_left_output k i.
Proof.
move=> Hsplit.
have Hraw :
    @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
              (esym (ntt_half_size_eq k)) j = lshift (2 ^ k) i.
  by move: (splitK (@cast_ord _ _ (esym (ntt_half_size_eq k)) j)); rewrite Hsplit.
have := congr1 (@cast_ord ((2 ^ k) + (2 ^ k)) (2 ^ k.+1)
                          (ntt_half_size_eq k)) Hraw.
by rewrite cast_ordKV /ntt_left_output.
Qed.

Lemma ntt_right_outputP (k : nat) (j : 'I_(2 ^ k.+1)) (i : 'I_(2 ^ k)) :
  split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                   (esym (ntt_half_size_eq k)) j) = inr i ->
  j = ntt_right_output k i.
Proof.
move=> Hsplit.
have Hraw :
    @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
              (esym (ntt_half_size_eq k)) j = rshift (2 ^ k) i.
  by move: (splitK (@cast_ord _ _ (esym (ntt_half_size_eq k)) j)); rewrite Hsplit.
have := congr1 (@cast_ord ((2 ^ k) + (2 ^ k)) (2 ^ k.+1)
                          (ntt_half_size_eq k)) Hraw.
by rewrite cast_ordKV /ntt_right_output.
Qed.

Lemma ntt_twiddle_unit (e : nat) :
  ntt_twiddle omega e \is a GRing.unit.
Proof. by rewrite /ntt_twiddle unitrX. Qed.

Lemma mul_unit_eq (c x y : R) :
  c \is a GRing.unit -> c * x = c * y -> x = y.
Proof.
move=> Hc Hxy.
have := congr1 (fun z => c^-1 * z) Hxy.
by rewrite !mulrA !mulVr ?mul1r.
Qed.

Lemma mul_unit_neq (c x y : R) :
  c \is a GRing.unit -> x <> y -> c * x <> c * y.
Proof.
move=> Hc Hxy Hmul.
apply: Hxy.
exact: mul_unit_eq Hc Hmul.
Qed.

Lemma ntt_shared_semantics_join_upper
    (k : nat) (left_state right_state : 'I_(2 ^ k) -> R)
    (j : 'I_(2 ^ k)) :
  @ntt_shared_semantics R omega k.+1 (ntt_join_state k left_state right_state)
      (ntt_left_output k j) =
  @ntt_shared_semantics R omega k left_state j +
  ntt_twiddle omega (val j) * @ntt_shared_semantics R omega k right_state j.
Proof.
pose N := (2 ^ k)%N.
pose raw_net :=
  parallel_network (ntt_shared_network k) (ntt_shared_network k) ++
  [:: ntt_merge_stage k].
have Hraw :
    eval_network (ntt_gate_semantics omega) (ntt_shared_network k.+1)
        (ntt_join_state k left_state right_state) (ntt_left_output k j) =
    eval_network (ntt_gate_semantics omega) raw_net
        (join_halves left_state right_state) (lshift N j).
  exact: (@eval_shared_network_eq_rect
            (N + N) (2 ^ k.+1) ntt_gate_tag R
            (ntt_gate_semantics omega) raw_net
            (ntt_half_size_eq k) (join_halves left_state right_state)
            (lshift N j)).
rewrite -(@ntt_shared_network_correct R omega k.+1
            (ntt_join_state k left_state right_state)
            (ntt_left_output k j)).
rewrite Hraw /raw_net eval_network_cat /= /eval_stage /ntt_merge_stage
        /ntt_gate_semantics /= split_lshift_eq.
rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
by rewrite !ntt_shared_network_correct.
Qed.

Lemma ntt_shared_semantics_join_lower
    (k : nat) (left_state right_state : 'I_(2 ^ k) -> R)
    (j : 'I_(2 ^ k)) :
  @ntt_shared_semantics R omega k.+1 (ntt_join_state k left_state right_state)
      (ntt_right_output k j) =
  @ntt_shared_semantics R omega k left_state j -
  ntt_twiddle omega (val j) * @ntt_shared_semantics R omega k right_state j.
Proof.
pose N := (2 ^ k)%N.
pose raw_net :=
  parallel_network (ntt_shared_network k) (ntt_shared_network k) ++
  [:: ntt_merge_stage k].
have Hraw :
    eval_network (ntt_gate_semantics omega) (ntt_shared_network k.+1)
        (ntt_join_state k left_state right_state) (ntt_right_output k j) =
    eval_network (ntt_gate_semantics omega) raw_net
        (join_halves left_state right_state) (rshift N j).
  exact: (@eval_shared_network_eq_rect
            (N + N) (2 ^ k.+1) ntt_gate_tag R
            (ntt_gate_semantics omega) raw_net
            (ntt_half_size_eq k) (join_halves left_state right_state)
            (rshift N j)).
rewrite -(@ntt_shared_network_correct R omega k.+1
            (ntt_join_state k left_state right_state)
            (ntt_right_output k j)).
rewrite Hraw /raw_net eval_network_cat /= /eval_stage /ntt_merge_stage
        /ntt_gate_semantics /= split_rshift_eq.
rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
by rewrite !ntt_shared_network_correct.
Qed.

Lemma ntt_shared_semantics_zero (k : nat) (j : 'I_(2 ^ k)) :
  @ntt_shared_semantics R omega k (zero_state k) j = 0.
Proof.
elim: k j => [|k IH] j /=.
- by [].
- pose raw_j := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) j.
  case Hs: (split raw_j) => [i|i] /=;
    by rewrite IH ?mulr0 ?addr0 ?subr0.
Qed.

Lemma ntt_join_state_left_agree
    (k : nat) (v1 v2 : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  (forall t, t != i -> v1 t = v2 t) ->
  forall t, t != ntt_left_output k i ->
    ntt_join_state k v1 (zero_state k) t =
    ntt_join_state k v2 (zero_state k) t.
Proof.
move=> Hagree t Hneq.
rewrite /ntt_join_state.
case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) t)) => [s|s].
- apply: Hagree.
  have Ht : t = ntt_left_output k s by exact: ntt_left_outputP Hs.
  apply/eqP => Hsi.
  move/eqP: Hneq => Hneq.
  apply: Hneq.
  by rewrite Ht Hsi.
- by [].
Qed.

Lemma ntt_join_state_right_agree
    (k : nat) (v1 v2 : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  (forall t, t != i -> v1 t = v2 t) ->
  forall t, t != ntt_right_output k i ->
    ntt_join_state k (zero_state k) v1 t =
    ntt_join_state k (zero_state k) v2 t.
Proof.
move=> Hagree t Hneq.
rewrite /ntt_join_state.
case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) t)) => [s|s].
- by [].
- apply: Hagree.
  have Ht : t = ntt_right_output k s by exact: ntt_right_outputP Hs.
  apply/eqP => Hsi.
  move/eqP: Hneq => Hneq.
  apply: Hneq.
  by rewrite Ht Hsi.
Qed.

Definition exact_negacyclic_transform (k : nat) :
    ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R :=
  @ntt_shared_semantics R omega k.

Arguments exact_negacyclic_transform _ _ _ : clear implicits.

Lemma exact_negacyclic_zero (k : nat) (j : 'I_(2 ^ k)) :
  exact_negacyclic_transform k (zero_state k) j = 0.
Proof. exact: ntt_shared_semantics_zero. Qed.

Theorem ntt_shared_semantics_full_dep (k : nat) :
  func_full_dep (n := 2 ^ k) (@ntt_shared_semantics R omega k).
Proof.
elim: k => [|k IH] j i.
- exists (zero_state 0), (fun _ : 'I_1 => omega).
  split.
  + move=> t Hneq.
    by rewrite (ord1 t) (ord1 i) eqxx in Hneq.
  + rewrite /zero_state /= => H.
    by move: omega_unit; rewrite -H unitr0.
- pose raw_i := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) i.
  pose raw_j := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) j.
  case Hi: (split raw_i) => [ii|ii];
  case Hj: (split raw_j) => [jj|jj].
  + have [left1 [left2 [Hagree Hneq]]] := IH jj ii.
    have -> : i = ntt_left_output k ii by exact: ntt_left_outputP Hi.
    exists (ntt_join_state k left1 (zero_state k)),
           (ntt_join_state k left2 (zero_state k)).
    split.
    * exact: (@ntt_join_state_left_agree k left1 left2 ii Hagree).
    * have -> : j = ntt_left_output k jj by exact: ntt_left_outputP Hj.
      rewrite !ntt_shared_semantics_join_upper !ntt_shared_semantics_zero mulr0 !addr0.
      exact: Hneq.
  + have [left1 [left2 [Hagree Hneq]]] := IH jj ii.
    have -> : i = ntt_left_output k ii by exact: ntt_left_outputP Hi.
    exists (ntt_join_state k left1 (zero_state k)),
           (ntt_join_state k left2 (zero_state k)).
    split.
    * exact: (@ntt_join_state_left_agree k left1 left2 ii Hagree).
    * have -> : j = ntt_right_output k jj by exact: ntt_right_outputP Hj.
      rewrite !ntt_shared_semantics_join_lower !ntt_shared_semantics_zero mulr0 !subr0.
      exact: Hneq.
  + have [right1 [right2 [Hagree Hneq]]] := IH jj ii.
    have -> : i = ntt_right_output k ii by exact: ntt_right_outputP Hi.
    exists (ntt_join_state k (zero_state k) right1),
           (ntt_join_state k (zero_state k) right2).
    split.
    * exact: (@ntt_join_state_right_agree k right1 right2 ii Hagree).
    * have -> : j = ntt_left_output k jj by exact: ntt_left_outputP Hj.
      rewrite !ntt_shared_semantics_join_upper !ntt_shared_semantics_zero !add0r.
      exact: mul_unit_neq (ntt_twiddle_unit (val jj)) Hneq.
  + have [right1 [right2 [Hagree Hneq]]] := IH jj ii.
    have -> : i = ntt_right_output k ii by exact: ntt_right_outputP Hi.
    exists (ntt_join_state k (zero_state k) right1),
           (ntt_join_state k (zero_state k) right2).
    split.
    * exact: (@ntt_join_state_right_agree k right1 right2 ii Hagree).
    * have -> : j = ntt_right_output k jj by exact: ntt_right_outputP Hj.
      rewrite !ntt_shared_semantics_join_lower !ntt_shared_semantics_zero !sub0r => Heq.
      apply: Hneq.
      apply: (mul_unit_eq (c := ntt_twiddle omega (val jj))).
      exact: ntt_twiddle_unit.
      exact: (can_inj (@opprK R) Heq).
Qed.

Theorem ntt_shared_network_exact
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval_network (ntt_gate_semantics omega) (ntt_shared_network k) v j =
  exact_negacyclic_transform k v j.
Proof. exact: ntt_shared_network_correct. Qed.

Theorem ntt_shared_circuit_exact
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval (ntt_gate_semantics omega) v (ntt_shared_circuit k j) =
  exact_negacyclic_transform k v j.
Proof. exact: ntt_shared_circuit_correct. Qed.

Theorem ntt_shared_circuit_full_dep (k : nat) :
  full_dependence (ntt_shared_circuit k).
Proof.
apply: (@func_dep_implies_circ_dep (2 ^ k) ntt_gate_tag R
          (ntt_gate_semantics omega)
          (exact_negacyclic_transform k)
          (ntt_shared_circuit k)).
- move=> v j.
  symmetry.
  exact: ntt_shared_circuit_exact.
- exact: ntt_shared_semantics_full_dep.
Qed.

Theorem ntt_shared_circuit_depth_bound (k : nat) :
  (k <= circ_depth (ntt_shared_circuit k))%N.
Proof.
apply: full_dep_depth_bound.
- by [].
- exact: ntt_shared_circuit_full_dep.
Qed.

End NTTSharedDependence.

(* ================================================================== *)
(** * Bit-reversed views of power-of-two input states                  *)
(* ================================================================== *)

Definition even_ord (k : nat) (i : 'I_(2 ^ k)) : 'I_(2 ^ k.+1).
Proof.
apply: (@Ordinal (2 ^ k.+1) ((val i).*2)).
by rewrite expnS mulnC muln2 ltn_double ltn_ord.
Defined.

Definition odd_ord (k : nat) (i : 'I_(2 ^ k)) : 'I_(2 ^ k.+1).
Proof.
apply: (@Ordinal (2 ^ k.+1) ((val i).*2.+1)).
by rewrite expnS mulnC muln2 ltn_Sdouble ltn_ord.
Defined.

Lemma val_even_ord (k : nat) (i : 'I_(2 ^ k)) :
  val (@even_ord k i) = (val i).*2.
Proof. by []. Qed.

Lemma val_odd_ord (k : nat) (i : 'I_(2 ^ k)) :
  val (@odd_ord k i) = (val i).*2.+1.
Proof. by []. Qed.

Arguments even_ord _ _ : clear implicits.
Arguments odd_ord _ _ : clear implicits.

Section BitReverseState.

Variable T : Type.

Definition even_state (k : nat) (v : 'I_(2 ^ k.+1) -> T) : 'I_(2 ^ k) -> T :=
  fun i => v (even_ord k i).

Definition odd_state (k : nat) (v : 'I_(2 ^ k.+1) -> T) : 'I_(2 ^ k) -> T :=
  fun i => v (odd_ord k i).

Arguments even_state _ _ : clear implicits.
Arguments odd_state _ _ : clear implicits.

Fixpoint bitrev_state (k : nat) : ('I_(2 ^ k) -> T) -> 'I_(2 ^ k) -> T :=
  match k return ('I_(2 ^ k) -> T) -> 'I_(2 ^ k) -> T with
  | 0 => fun v => v
  | k'.+1 =>
      fun v j =>
        match split (@cast_ord (2 ^ k'.+1) ((2 ^ k') + (2 ^ k'))
                          (esym (ntt_half_size_eq k')) j) with
        | inl i => @bitrev_state k' (fun t => v (@even_ord k' t)) i
        | inr i => @bitrev_state k' (fun t => v (@odd_ord k' t)) i
        end
  end.

Arguments bitrev_state _ _ _ : clear implicits.

Fixpoint bitrev_ord (k : nat) : 'I_(2 ^ k) -> 'I_(2 ^ k) :=
  match k return 'I_(2 ^ k) -> 'I_(2 ^ k) with
  | 0 => fun i => i
  | k'.+1 =>
      fun j =>
        match split (@cast_ord (2 ^ k'.+1) ((2 ^ k') + (2 ^ k'))
                          (esym (ntt_half_size_eq k')) j) with
        | inl i => @even_ord k' (@bitrev_ord k' i)
        | inr i => @odd_ord k' (@bitrev_ord k' i)
        end
  end.

Arguments bitrev_ord _ _ : clear implicits.

Lemma bitrev_stateE (k : nat) (v : 'I_(2 ^ k) -> T) (j : 'I_(2 ^ k)) :
  bitrev_state k v j = v (bitrev_ord k j).
Proof.
elim: k v j => [|k IH] v j /=.
- by rewrite (ord1 j).
- case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                            (esym (ntt_half_size_eq k)) j)) => [i|i] /=.
  + by rewrite IH.
  + by rewrite IH.
Qed.

Lemma bitrev_ord_left_output (k : nat) (i : 'I_(2 ^ k)) :
  bitrev_ord k.+1 (@ntt_left_output k i) = @even_ord k (bitrev_ord k i).
Proof. by rewrite /= ntt_left_outputK. Qed.

Lemma bitrev_ord_right_output (k : nat) (i : 'I_(2 ^ k)) :
  bitrev_ord k.+1 (@ntt_right_output k i) = @odd_ord k (bitrev_ord k i).
Proof. by rewrite /= ntt_right_outputK. Qed.

Lemma bitrev_state_left (k : nat) (v : 'I_(2 ^ k.+1) -> T) (i : 'I_(2 ^ k)) :
  bitrev_state k.+1 v (@ntt_left_output k i) =
  bitrev_state k (fun t => v (@even_ord k t)) i.
Proof. by rewrite /= ntt_left_outputK. Qed.

Lemma bitrev_state_right (k : nat) (v : 'I_(2 ^ k.+1) -> T) (i : 'I_(2 ^ k)) :
  bitrev_state k.+1 v (@ntt_right_output k i) =
  bitrev_state k (fun t => v (@odd_ord k t)) i.
Proof. by rewrite /= ntt_right_outputK. Qed.

End BitReverseState.

Section BitReverseInputCircuit.

Variables (k : nat) (O : Type).

Definition bitrev_input_circuit : circuit (2 ^ k) O :=
  [ffun j => @CInput (2 ^ k) O (@bitrev_ord k j)].

Section BitReverseInputCircuitEval.

Variable T : Type.
Variable ops : O -> T -> T -> T.

Lemma bitrev_input_circuit_eval
    (v : 'I_(2 ^ k) -> T) (j : 'I_(2 ^ k)) :
  eval ops v (bitrev_input_circuit j) = @bitrev_state T k v j.
Proof. by rewrite /bitrev_input_circuit ffunE /= bitrev_stateE. Qed.

End BitReverseInputCircuitEval.

Lemma bitrev_input_circuit_gate_depth (j : 'I_(2 ^ k)) :
  depth (bitrev_input_circuit j) = 0.
Proof. by rewrite /bitrev_input_circuit ffunE. Qed.

End BitReverseInputCircuit.

(* ================================================================== *)
(** * Exact negacyclic shared network                                 *)
(* ================================================================== *)

Section ExactNegacyclicSharedNetwork.

Definition exact_ntt_merge_stage (stride k : nat) :
    shared_stage ((2 ^ k) + (2 ^ k)) ntt_gate_tag :=
  let N := 2 ^ k in
  @SharedStage (N + N) ntt_gate_tag
      (fun j =>
        match split j with
        | inl i => NTTGateTag k (stride * (val i).*2.+1) UpperBranch
        | inr i => NTTGateTag k (stride * (val i).*2.+1) LowerBranch
        end)
      (fun j =>
        match split j with
        | inl i => lshift N i
        | inr i => lshift N i
        end)
      (fun j =>
        match split j with
        | inl i => rshift N i
        | inr i => rshift N i
        end)
      (N + N)%N
      1.

Fixpoint exact_ntt_shared_network_from (stride k : nat) :
    shared_network (2 ^ k) ntt_gate_tag :=
  match k return shared_network (2 ^ k) ntt_gate_tag with
  | 0 => [::]
  | k'.+1 =>
      let N := 2 ^ k' in
      let Heq : (N + N = 2 ^ k'.+1)%N :=
        esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))) in
      let rec := exact_ntt_shared_network_from (stride.*2) k' in
      eq_rect _ (fun p => shared_network p ntt_gate_tag)
        (parallel_network rec rec ++
         [:: exact_ntt_merge_stage stride k'])
        _ Heq
  end.

Definition exact_ntt_shared_network (k : nat) :=
  exact_ntt_shared_network_from 1 k.

Lemma size_exact_ntt_shared_network_from (stride k : nat) :
  size (exact_ntt_shared_network_from stride k) = k.
Proof.
elim: k stride => [|k' IH] stride //=.
rewrite shared_network_eq_rect_size size_cat /=.
by rewrite size_parallel_network_self IH addn1.
Qed.

Lemma size_exact_ntt_shared_network (k : nat) :
  size (exact_ntt_shared_network k) = k.
Proof. exact: size_exact_ntt_shared_network_from. Qed.

End ExactNegacyclicSharedNetwork.

Section ExactNegacyclicSharedSemantics.

Variable R : GRing.UnitRing.type.
Variable omega : R.

Open Scope ring_scope.

Fixpoint exact_ntt_shared_semantics_from (stride k : nat) :
    ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R :=
  match k return ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R with
  | 0 => fun v _ => v ord0
  | k'.+1 =>
      let N := (2 ^ k')%N in
      let Heq : (N + N = 2 ^ k'.+1)%N :=
        esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))) in
      fun v j =>
        let raw_state : 'I_(N + N) -> R :=
          fun i => v (@cast_ord (N + N) (2 ^ k'.+1) Heq i) in
        let left :=
          exact_ntt_shared_semantics_from (stride.*2)
            (fun i => raw_state (lshift N i)) in
        let right :=
          exact_ntt_shared_semantics_from (stride.*2)
            (fun i => raw_state (rshift N i)) in
        match split (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j) with
        | inl i => left i + ntt_twiddle omega (stride * (val i).*2.+1) * right i
        | inr i => left i - ntt_twiddle omega (stride * (val i).*2.+1) * right i
        end
  end.

Definition exact_ntt_shared_semantics (k : nat) :
    ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R :=
  fun v j => exact_ntt_shared_semantics_from 1 v j.

Arguments exact_ntt_shared_semantics _ _ _ : clear implicits.

Theorem exact_ntt_shared_network_from_correct
    (stride k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval_network (ntt_gate_semantics omega) (exact_ntt_shared_network_from stride k) v j =
  exact_ntt_shared_semantics_from stride v j.
Proof.
elim: k stride v j => [|k' IH] stride v j /=.
- by rewrite (ord1 j).
- pose N := (2 ^ k')%N.
  pose Heq : (N + N = 2 ^ k'.+1)%N :=
    esym (etrans (expnS 2 k') (etrans (mul2n N) (esym (addnn N)))).
  pose raw_net :=
    parallel_network (exact_ntt_shared_network_from stride.*2 k')
                     (exact_ntt_shared_network_from stride.*2 k') ++
    [:: exact_ntt_merge_stage stride k'].
  pose raw_state : 'I_(N + N) -> R :=
    fun i => v (@cast_ord (N + N) (2 ^ k'.+1) Heq i).
  pose raw_j : 'I_(N + N) :=
    @cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j.
  have Hstate :
      forall j0 : 'I_(2 ^ k'.+1),
        raw_state (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j0) = v j0.
    by move=> j0; rewrite /raw_state cast_ordKV.
  have Hj : @cast_ord (N + N) (2 ^ k'.+1) Heq raw_j = j.
    by rewrite /raw_j cast_ordKV.
  have Hraw :
      eval_network (ntt_gate_semantics omega)
        (exact_ntt_shared_network_from stride k'.+1) v j =
      eval_network (ntt_gate_semantics omega) raw_net raw_state raw_j.
    have Hstate_eq :
        eval_network (ntt_gate_semantics omega)
          (exact_ntt_shared_network_from stride k'.+1) v j =
        eval_network (ntt_gate_semantics omega)
          (exact_ntt_shared_network_from stride k'.+1)
          (fun j0 : 'I_(2 ^ k'.+1) =>
             raw_state (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j0)) j.
      apply: eval_network_state_eq => j0.
      exact: esym (Hstate j0).
    have Hraw0 :=
      @eval_shared_network_eq_rect
        (N + N) (2 ^ k'.+1) ntt_gate_tag R
        (ntt_gate_semantics omega) raw_net Heq raw_state raw_j.
    rewrite Hj in Hraw0.
    exact: eq_trans Hstate_eq Hraw0.
  have Hjoin :
      forall j0 : 'I_(N + N),
        raw_state j0 =
        join_halves (fun t => raw_state (lshift N t))
                    (fun t => raw_state (rshift N t)) j0.
    move=> j0; rewrite /join_halves.
    case Hs: (split j0) => [i|i].
    - by move: (splitK j0); rewrite Hs /= => <-.
    - by move: (splitK j0); rewrite Hs /= => <-.
  rewrite Hraw /raw_net eval_network_cat /= /exact_ntt_shared_semantics_from /= /raw_j.
  case Hs: (split (@cast_ord (2 ^ k'.+1) (N + N) (esym Heq) j)) => [i|i] /=.
  + rewrite /eval_stage /exact_ntt_merge_stage /ntt_gate_semantics /= Hs /=.
    have Hstate_join_l :
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            raw_state (lshift N i) =
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (lshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    have Hstate_join_r :
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            raw_state (rshift N i) =
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (rshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    rewrite Hstate_join_l Hstate_join_r.
    rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
    by rewrite (IH stride.*2 (fun t => raw_state (lshift N t)) i)
               (IH stride.*2 (fun t => raw_state (rshift N t)) i).
  + rewrite /eval_stage /exact_ntt_merge_stage /ntt_gate_semantics /= Hs /=.
    have Hstate_join_l :
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            raw_state (lshift N i) =
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (lshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    have Hstate_join_r :
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            raw_state (rshift N i) =
        eval_network (ntt_gate_semantics omega)
            (parallel_network (exact_ntt_shared_network_from stride.*2 k')
                              (exact_ntt_shared_network_from stride.*2 k'))
            (join_halves (fun t => raw_state (lshift N t))
                         (fun t => raw_state (rshift N t))) (rshift N i).
      apply: eval_network_state_eq => t.
      exact: Hjoin.
    rewrite Hstate_join_l Hstate_join_r.
    rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
    by rewrite (IH stride.*2 (fun t => raw_state (lshift N t)) i)
               (IH stride.*2 (fun t => raw_state (rshift N t)) i).
Qed.

Theorem exact_ntt_shared_network_correct
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval_network (ntt_gate_semantics omega) (exact_ntt_shared_network k) v j =
  @exact_ntt_shared_semantics k v j.
Proof. exact: exact_ntt_shared_network_from_correct. Qed.

Definition exact_ntt_shared_circuit (k : nat) :
    circuit (2 ^ k) ntt_gate_tag :=
  network_circuit (exact_ntt_shared_network k).

Theorem exact_ntt_shared_circuit_correct
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  eval (ntt_gate_semantics omega) v (exact_ntt_shared_circuit k j) =
  @exact_ntt_shared_semantics k v j.
Proof.
rewrite /exact_ntt_shared_circuit network_circuit_eval.
exact: exact_ntt_shared_network_correct.
Qed.

End ExactNegacyclicSharedSemantics.

Section ExactNTTSharedDependence.

Variable R : GRing.UnitRing.type.
Variable omega : R.
Hypothesis omega_unit : omega \is a GRing.unit.

Open Scope ring_scope.

Definition exact_join_state
    (k : nat) (left_state right_state : 'I_(2 ^ k) -> R) :
    'I_(2 ^ k.+1) -> R :=
  fun t =>
    join_halves left_state right_state
      (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                 (esym (ntt_half_size_eq k)) t).

Lemma exact_join_state_left
    (k : nat) (left_state right_state : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  exact_join_state left_state right_state (@ntt_left_output k i) = left_state i.
Proof.
rewrite /exact_join_state /ntt_left_output /= cast_ordVK /join_halves.
by rewrite split_lshift_eq.
Qed.

Lemma exact_join_state_right
    (k : nat) (left_state right_state : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  exact_join_state left_state right_state (@ntt_right_output k i) = right_state i.
Proof.
rewrite /exact_join_state /ntt_right_output /= cast_ordVK /join_halves.
by rewrite split_rshift_eq.
Qed.

Lemma exact_ntt_shared_semantics_from_join_upper
    (stride k : nat) (left_state right_state : 'I_(2 ^ k) -> R)
    (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics_from R omega stride k.+1
      (exact_join_state left_state right_state)
      (@ntt_left_output k j) =
  @exact_ntt_shared_semantics_from R omega stride.*2 k left_state j +
  ntt_twiddle omega (stride * (val j).*2.+1) *
  @exact_ntt_shared_semantics_from R omega stride.*2 k right_state j.
Proof.
pose N := (2 ^ k)%N.
pose raw_net :=
  parallel_network (exact_ntt_shared_network_from stride.*2 k)
                   (exact_ntt_shared_network_from stride.*2 k) ++
  [:: exact_ntt_merge_stage stride k].
have Hraw :
    eval_network (ntt_gate_semantics omega)
        (exact_ntt_shared_network_from stride k.+1)
        (exact_join_state left_state right_state) (@ntt_left_output k j) =
    eval_network (ntt_gate_semantics omega) raw_net
        (join_halves left_state right_state) (lshift N j).
  exact: (@eval_shared_network_eq_rect
            (N + N) (2 ^ k.+1) ntt_gate_tag R
            (ntt_gate_semantics omega) raw_net
            (ntt_half_size_eq k) (join_halves left_state right_state)
            (lshift N j)).
rewrite -(@exact_ntt_shared_network_from_correct R omega stride k.+1
            (exact_join_state left_state right_state)
            (@ntt_left_output k j)).
rewrite Hraw /raw_net eval_network_cat /= /eval_stage /exact_ntt_merge_stage
        /ntt_gate_semantics /= split_lshift_eq.
rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
by rewrite !exact_ntt_shared_network_from_correct.
Qed.

Lemma exact_ntt_shared_semantics_from_join_lower
    (stride k : nat) (left_state right_state : 'I_(2 ^ k) -> R)
    (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics_from R omega stride k.+1
      (exact_join_state left_state right_state)
      (@ntt_right_output k j) =
  @exact_ntt_shared_semantics_from R omega stride.*2 k left_state j -
  ntt_twiddle omega (stride * (val j).*2.+1) *
  @exact_ntt_shared_semantics_from R omega stride.*2 k right_state j.
Proof.
pose N := (2 ^ k)%N.
pose raw_net :=
  parallel_network (exact_ntt_shared_network_from stride.*2 k)
                   (exact_ntt_shared_network_from stride.*2 k) ++
  [:: exact_ntt_merge_stage stride k].
have Hraw :
    eval_network (ntt_gate_semantics omega)
        (exact_ntt_shared_network_from stride k.+1)
        (exact_join_state left_state right_state) (@ntt_right_output k j) =
    eval_network (ntt_gate_semantics omega) raw_net
        (join_halves left_state right_state) (rshift N j).
  exact: (@eval_shared_network_eq_rect
            (N + N) (2 ^ k.+1) ntt_gate_tag R
            (ntt_gate_semantics omega) raw_net
            (ntt_half_size_eq k) (join_halves left_state right_state)
            (rshift N j)).
rewrite -(@exact_ntt_shared_network_from_correct R omega stride k.+1
            (exact_join_state left_state right_state)
            (@ntt_right_output k j)).
rewrite Hraw /raw_net eval_network_cat /= /eval_stage /exact_ntt_merge_stage
        /ntt_gate_semantics /= split_rshift_eq.
rewrite eval_parallel_network_lshift eval_parallel_network_rshift.
by rewrite !exact_ntt_shared_network_from_correct.
Qed.

Lemma exact_ntt_shared_semantics_from_zero
    (stride k : nat) (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics_from R omega stride k (@zero_state R k) j = 0.
Proof.
elim: k stride j => [|k IH] stride j /=.
- by [].
- pose raw_j := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) j.
  case Hs: (split raw_j) => [i|i] /=;
    by rewrite IH ?mulr0 ?addr0 ?subr0.
Qed.

Lemma exact_ntt_shared_semantics_zero (k : nat) (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics R omega k (@zero_state R k) j = 0.
Proof. exact: exact_ntt_shared_semantics_from_zero. Qed.

Lemma exact_join_state_left_agree
    (k : nat) (v1 v2 : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  (forall t, t != i -> v1 t = v2 t) ->
  forall t, t != @ntt_left_output k i ->
    exact_join_state v1 (@zero_state R k) t =
    exact_join_state v2 (@zero_state R k) t.
Proof.
move=> Hagree t Hneq.
rewrite /exact_join_state /join_halves.
case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) t)) => [s|s].
- apply: Hagree.
  have Ht : t = @ntt_left_output k s by exact: ntt_left_outputP Hs.
  apply/eqP => Hsi.
  move/eqP: Hneq => Hneq.
  apply: Hneq.
  by rewrite Ht Hsi.
- by [].
Qed.

Lemma exact_join_state_right_agree
    (k : nat) (v1 v2 : 'I_(2 ^ k) -> R) (i : 'I_(2 ^ k)) :
  (forall t, t != i -> v1 t = v2 t) ->
  forall t, t != @ntt_right_output k i ->
    exact_join_state (@zero_state R k) v1 t =
    exact_join_state (@zero_state R k) v2 t.
Proof.
move=> Hagree t Hneq.
rewrite /exact_join_state /join_halves.
case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) t)) => [s|s].
- by [].
- apply: Hagree.
  have Ht : t = @ntt_right_output k s by exact: ntt_right_outputP Hs.
  apply/eqP => Hsi.
  move/eqP: Hneq => Hneq.
  apply: Hneq.
  by rewrite Ht Hsi.
Qed.

Theorem exact_ntt_shared_semantics_from_full_dep (stride k : nat) :
  func_full_dep (n := 2 ^ k) (@exact_ntt_shared_semantics_from R omega stride k).
Proof.
elim: k stride => [|k IH] stride j i.
- exists (@zero_state R 0), (fun _ : 'I_1 => omega).
  split.
  + move=> t Hneq.
    by rewrite (ord1 t) (ord1 i) eqxx in Hneq.
  + rewrite /zero_state /= => H.
    by move: omega_unit; rewrite -H unitr0.
- pose raw_i := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) i.
  pose raw_j := @cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                          (esym (ntt_half_size_eq k)) j.
  case Hi: (split raw_i) => [ii|ii];
  case Hj: (split raw_j) => [jj|jj].
  + have [left1 [left2 [Hagree Hneq]]] := IH stride.*2 jj ii.
    have -> : i = @ntt_left_output k ii by exact: ntt_left_outputP Hi.
    exists (exact_join_state left1 (@zero_state R k)),
           (exact_join_state left2 (@zero_state R k)).
    split.
    * exact: (@exact_join_state_left_agree k left1 left2 ii Hagree).
    * have -> : j = @ntt_left_output k jj by exact: ntt_left_outputP Hj.
      rewrite !exact_ntt_shared_semantics_from_join_upper
              !exact_ntt_shared_semantics_from_zero mulr0 !addr0.
      exact: Hneq.
  + have [left1 [left2 [Hagree Hneq]]] := IH stride.*2 jj ii.
    have -> : i = @ntt_left_output k ii by exact: ntt_left_outputP Hi.
    exists (exact_join_state left1 (@zero_state R k)),
           (exact_join_state left2 (@zero_state R k)).
    split.
    * exact: (@exact_join_state_left_agree k left1 left2 ii Hagree).
    * have -> : j = @ntt_right_output k jj by exact: ntt_right_outputP Hj.
      rewrite !exact_ntt_shared_semantics_from_join_lower
              !exact_ntt_shared_semantics_from_zero mulr0 !subr0.
      exact: Hneq.
  + have [right1 [right2 [Hagree Hneq]]] := IH stride.*2 jj ii.
    have -> : i = @ntt_right_output k ii by exact: ntt_right_outputP Hi.
    exists (exact_join_state (@zero_state R k) right1),
           (exact_join_state (@zero_state R k) right2).
    split.
    * exact: (@exact_join_state_right_agree k right1 right2 ii Hagree).
    * have -> : j = @ntt_left_output k jj by exact: ntt_left_outputP Hj.
      rewrite !exact_ntt_shared_semantics_from_join_upper
              !exact_ntt_shared_semantics_from_zero !add0r.
      apply: (mul_unit_neq (c := ntt_twiddle omega (stride * (val jj).*2.+1))).
      -- exact: ntt_twiddle_unit.
      -- exact: Hneq.
  + have [right1 [right2 [Hagree Hneq]]] := IH stride.*2 jj ii.
    have -> : i = @ntt_right_output k ii by exact: ntt_right_outputP Hi.
    exists (exact_join_state (@zero_state R k) right1),
           (exact_join_state (@zero_state R k) right2).
    split.
    * exact: (@exact_join_state_right_agree k right1 right2 ii Hagree).
    * have -> : j = @ntt_right_output k jj by exact: ntt_right_outputP Hj.
      rewrite !exact_ntt_shared_semantics_from_join_lower
              !exact_ntt_shared_semantics_from_zero !sub0r => Heq.
      apply: Hneq.
      apply: (mul_unit_eq (c := ntt_twiddle omega (stride * (val jj).*2.+1))).
      exact: ntt_twiddle_unit.
      exact: (can_inj (@opprK R) Heq).
Qed.

Theorem exact_ntt_shared_semantics_full_dep (k : nat) :
  func_full_dep (n := 2 ^ k) (@exact_ntt_shared_semantics R omega k).
Proof. exact: exact_ntt_shared_semantics_from_full_dep. Qed.

Theorem exact_ntt_shared_circuit_full_dep (k : nat) :
  full_dependence (exact_ntt_shared_circuit k).
Proof.
apply: (@func_dep_implies_circ_dep (2 ^ k) ntt_gate_tag R
          (ntt_gate_semantics omega)
          (@exact_ntt_shared_semantics R omega k)
          (exact_ntt_shared_circuit k)).
- move=> v j.
  symmetry.
  exact: exact_ntt_shared_circuit_correct.
- exact: exact_ntt_shared_semantics_full_dep.
Qed.

Theorem exact_ntt_shared_circuit_depth_bound (k : nat) :
  (k <= circ_depth (exact_ntt_shared_circuit k))%N.
Proof.
apply: full_dep_depth_bound.
- by [].
- exact: exact_ntt_shared_circuit_full_dep.
Qed.

End ExactNTTSharedDependence.

Section ExactBitReversedEvaluation.

Variable R : GRing.UnitRing.type.
Variable omega : R.

Open Scope ring_scope.

Fixpoint exact_ntt_bitrev_eval (k : nat) :
    nat -> ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R :=
  match k return nat -> ('I_(2 ^ k) -> R) -> 'I_(2 ^ k) -> R with
  | 0 => fun _ v _ => v ord0
  | n.+1 =>
      let rec := @exact_ntt_bitrev_eval n in
      fun stride v j =>
        match split (@cast_ord (2 ^ n.+1) ((2 ^ n) + (2 ^ n))
                          (esym (ntt_half_size_eq n)) j) with
        | inl i =>
            rec (stride.*2) (fun t => v (@even_ord n t)) i +
            ntt_twiddle omega (stride * (val i).*2.+1) *
            rec (stride.*2) (fun t => v (@odd_ord n t)) i
        | inr i =>
            rec (stride.*2) (fun t => v (@even_ord n t)) i -
            ntt_twiddle omega (stride * (val i).*2.+1) *
            rec (stride.*2) (fun t => v (@odd_ord n t)) i
        end
  end.

Lemma exact_ntt_shared_semantics_from_state_eq
    (stride k : nat) (v1 v2 : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  (forall t, v1 t = v2 t) ->
  @exact_ntt_shared_semantics_from R omega stride k v1 j =
  @exact_ntt_shared_semantics_from R omega stride k v2 j.
Proof.
move=> Heq.
rewrite -(@exact_ntt_shared_network_from_correct R omega stride k v1 j).
rewrite -(@exact_ntt_shared_network_from_correct R omega stride k v2 j).
apply: eval_network_state_eq => t.
exact: Heq.
Qed.

Theorem exact_ntt_shared_semantics_from_bitrev
    (stride k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics_from R omega stride k (@bitrev_state R k v) j =
  @exact_ntt_bitrev_eval k stride v j.
Proof.
elim: k stride v j => [|k IH] stride v j /=.
- by [].
- have Hjoin :
      forall t : 'I_(2 ^ k.+1),
        @bitrev_state R k.+1 v t =
        exact_join_state
          (@bitrev_state R k (fun s => v (@even_ord k s)))
          (@bitrev_state R k (fun s => v (@odd_ord k s))) t.
    move=> t.
    case Hs: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                              (esym (ntt_half_size_eq k)) t)) => [i|i].
    + have -> : t = @ntt_left_output k i by exact: ntt_left_outputP Hs.
      by rewrite bitrev_state_left exact_join_state_left.
    + have -> : t = @ntt_right_output k i by exact: ntt_right_outputP Hs.
      by rewrite bitrev_state_right exact_join_state_right.
    case Hj: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                               (esym (ntt_half_size_eq k)) j)) => [i|i] /=.
    + have Hbranch :
          @exact_ntt_shared_semantics_from R omega stride k.+1
              (@bitrev_state R k.+1 v) (@ntt_left_output k i) =
          @exact_ntt_bitrev_eval k.+1 stride v (@ntt_left_output k i).
        have -> :
            @exact_ntt_shared_semantics_from R omega stride k.+1
                (@bitrev_state R k.+1 v) (@ntt_left_output k i) =
            @exact_ntt_shared_semantics_from R omega stride k.+1
                (exact_join_state
                   (@bitrev_state R k (fun s => v (@even_ord k s)))
                   (@bitrev_state R k (fun s => v (@odd_ord k s))))
                (@ntt_left_output k i).
          apply: exact_ntt_shared_semantics_from_state_eq => t.
          exact: Hjoin.
        rewrite exact_ntt_shared_semantics_from_join_upper /=.
        by rewrite !ntt_left_outputK IH IH.
      by move: Hbranch; rewrite /= ntt_left_outputK.
    + have Hbranch :
          @exact_ntt_shared_semantics_from R omega stride k.+1
              (@bitrev_state R k.+1 v) (@ntt_right_output k i) =
          @exact_ntt_bitrev_eval k.+1 stride v (@ntt_right_output k i).
        have -> :
            @exact_ntt_shared_semantics_from R omega stride k.+1
                (@bitrev_state R k.+1 v) (@ntt_right_output k i) =
            @exact_ntt_shared_semantics_from R omega stride k.+1
                (exact_join_state
                   (@bitrev_state R k (fun s => v (@even_ord k s)))
                   (@bitrev_state R k (fun s => v (@odd_ord k s))))
                (@ntt_right_output k i).
          apply: exact_ntt_shared_semantics_from_state_eq => t.
          exact: Hjoin.
        rewrite exact_ntt_shared_semantics_from_join_lower /=.
        by rewrite !ntt_right_outputK IH IH.
      by move: Hbranch; rewrite /= ntt_right_outputK.
Qed.

Theorem exact_ntt_shared_semantics_bitrev
    (k : nat) (v : 'I_(2 ^ k) -> R) (j : 'I_(2 ^ k)) :
  @exact_ntt_shared_semantics R omega k (@bitrev_state R k v) j =
  @exact_ntt_bitrev_eval k 1 v j.
Proof. exact: exact_ntt_shared_semantics_from_bitrev. Qed.

End ExactBitReversedEvaluation.

(* ================================================================== *)
(** * Shared-network complexity laws                                  *)
(* ================================================================== *)

Section SharedNetworkComplexity.

Variables (n : nat) (O : Type).

Lemma network_workE (Net : shared_network n O) :
  network_work Net = n * size Net.
Proof.
elim: Net => [|st Net IH] /=.
- by rewrite muln0.
- by rewrite IH mulnS addnC.
Qed.

Lemma network_work_cat (Net1 Net2 : shared_network n O) :
  network_work (Net1 ++ Net2) = network_work Net1 + network_work Net2.
Proof.
elim: Net1 => [|st Net1 IH] /=.
- by rewrite add0n.
- by rewrite IH addnA.
Qed.

Lemma network_word_traffic_cat (Net1 Net2 : shared_network n O) :
  network_word_traffic (Net1 ++ Net2) =
  network_word_traffic Net1 + network_word_traffic Net2.
Proof.
elim: Net1 => [|st Net1 IH] /=.
- by rewrite add0n.
- by rewrite IH addnA.
Qed.

Fixpoint network_latency_sum (Net : shared_network n O) : nat :=
  match Net with
  | [::] => 0
  | st :: Net' => ss_latency st + network_latency_sum Net'
  end.

Lemma network_latency_sum_cat (Net1 Net2 : shared_network n O) :
  network_latency_sum (Net1 ++ Net2) =
  network_latency_sum Net1 + network_latency_sum Net2.
Proof.
elim: Net1 => [|st Net1 IH] /=.
- by rewrite add0n.
- by rewrite IH addnA.
Qed.

Lemma network_cycles_from_asap (ready : nat) (Net : shared_network n O) :
  network_cycles_from ready Net (asap_schedule_from ready Net) =
  ready + network_latency_sum Net.
Proof.
elim: Net ready => [|st Net IH] ready /=.
- by rewrite addn0.
- by rewrite IH addnA.
Qed.

Lemma network_cycles_asap (Net : shared_network n O) :
  network_cycles Net (asap_schedule Net) = network_latency_sum Net.
Proof. by rewrite /network_cycles /asap_schedule network_cycles_from_asap add0n. Qed.

Lemma legal_schedule_from_cycles_lower
    (ready : nat) (Net : shared_network n O) (sched : schedule) :
  legal_schedule_from ready Net sched ->
  ready + network_latency_sum Net <= network_cycles_from ready Net sched.
Proof.
elim: Net ready sched => [|st Net IH] ready [|c sched] //=.
- by rewrite addn0.
- move=> [Hready Hlegal].
  rewrite addnA.
  apply: (leq_trans _ (IH _ _ Hlegal)).
  by rewrite !leq_add2r.
Qed.

Lemma legal_schedule_cycles_lower (Net : shared_network n O) (sched : schedule) :
  legal_schedule Net sched ->
  network_latency_sum Net <= network_cycles Net sched.
Proof.
move=> Hlegal.
have Hlower : 0 + network_latency_sum Net <= network_cycles_from 0 Net sched.
  exact: legal_schedule_from_cycles_lower Hlegal.
by rewrite /network_cycles add0n in Hlower.
Qed.

End SharedNetworkComplexity.

Lemma shared_network_eq_rect_work
    (n m : nat) (O : Type) (Net : shared_network n O) (Heq : n = m) :
  network_work (eq_rect n (fun p => shared_network p O) Net m Heq) =
  network_work Net.
Proof. by subst. Qed.

Lemma shared_network_eq_rect_word_traffic
    (n m : nat) (O : Type) (Net : shared_network n O) (Heq : n = m) :
  network_word_traffic (eq_rect n (fun p => shared_network p O) Net m Heq) =
  network_word_traffic Net.
Proof. by subst. Qed.

Lemma shared_network_eq_rect_latency_sum
    (n m : nat) (O : Type) (Net : shared_network n O) (Heq : n = m) :
  network_latency_sum (eq_rect n (fun p => shared_network p O) Net m Heq) =
  network_latency_sum Net.
Proof. by subst. Qed.

Lemma parallel_network_work_self
    (m : nat) (O : Type) (Net : shared_network m O) :
  network_work (parallel_network Net Net) = 2 * network_work Net.
Proof.
rewrite !network_workE size_parallel_network_self.
have -> :
    (m + m) * size Net = m * size Net + m * size Net.
  by rewrite mulnDl.
by rewrite addnn mul2n.
Qed.

Lemma parallel_network_word_traffic_self
    (m : nat) (O : Type) (Net : shared_network m O) :
  network_word_traffic (parallel_network Net Net) = 2 * network_word_traffic Net.
Proof.
elim: Net => [|st Net IH] /=.
- by rewrite muln0.
- rewrite IH mulnDr [2 * ss_word_traffic st]mul2n.
  by rewrite addnn.
Qed.

Lemma parallel_network_latency_sum_self
    (m : nat) (O : Type) (Net : shared_network m O) :
  network_latency_sum (parallel_network Net Net) = network_latency_sum Net.
Proof.
elim: Net => [|st Net IH] /=.
- by [].
- by rewrite IH maxnn.
Qed.

Section NTTSharedComplexity.

Lemma ntt_shared_network_work (k : nat) :
  network_work (ntt_shared_network k) = k * 2 ^ k.
Proof.
rewrite network_workE size_ntt_shared_network.
by rewrite mulnC.
Qed.

Lemma ntt_shared_network_word_traffic_eq_work (k : nat) :
  network_word_traffic (ntt_shared_network k) =
  network_work (ntt_shared_network k).
Proof.
elim: k => [|k' IH] /=.
- by [].
- rewrite shared_network_eq_rect_word_traffic shared_network_eq_rect_work.
  rewrite !network_word_traffic_cat !network_work_cat /=.
  rewrite parallel_network_word_traffic_self parallel_network_work_self IH.
  by rewrite /ntt_merge_stage /=.
Qed.

Lemma ntt_shared_network_word_traffic (k : nat) :
  network_word_traffic (ntt_shared_network k) = k * 2 ^ k.
Proof. by rewrite ntt_shared_network_word_traffic_eq_work ntt_shared_network_work. Qed.

Lemma ntt_shared_network_byte_traffic (word_bytes k : nat) :
  network_byte_traffic word_bytes (ntt_shared_network k) =
  word_bytes * k * 2 ^ k.
Proof. by rewrite /network_byte_traffic ntt_shared_network_word_traffic mulnA. Qed.

Lemma ntt_shared_network_latency_sum (k : nat) :
  network_latency_sum (ntt_shared_network k) = k.
Proof.
elim: k => [|k' IH] /=.
- by [].
- rewrite shared_network_eq_rect_latency_sum network_latency_sum_cat /=.
  by rewrite parallel_network_latency_sum_self IH addn1.
Qed.

Lemma ntt_shared_network_span (k : nat) :
  network_cycles (ntt_shared_network k) (asap_schedule (ntt_shared_network k)) = k.
Proof. by rewrite network_cycles_asap ntt_shared_network_latency_sum. Qed.

End NTTSharedComplexity.

Section ExactNTTSharedComplexity.

Lemma exact_ntt_shared_network_work_from (stride k : nat) :
  network_work (exact_ntt_shared_network_from stride k) = k * 2 ^ k.
Proof.
rewrite network_workE size_exact_ntt_shared_network_from.
by rewrite mulnC.
Qed.

Lemma exact_ntt_shared_network_work (k : nat) :
  network_work (exact_ntt_shared_network k) = k * 2 ^ k.
Proof. exact: exact_ntt_shared_network_work_from. Qed.

Lemma exact_ntt_shared_network_word_traffic_eq_work_from (stride k : nat) :
  network_word_traffic (exact_ntt_shared_network_from stride k) =
  network_work (exact_ntt_shared_network_from stride k).
Proof.
elim: k stride => [|k' IH] stride //=.
rewrite shared_network_eq_rect_word_traffic shared_network_eq_rect_work.
rewrite !network_word_traffic_cat !network_work_cat /=.
rewrite parallel_network_word_traffic_self parallel_network_work_self IH.
by rewrite /exact_ntt_merge_stage /=.
Qed.

Lemma exact_ntt_shared_network_word_traffic (k : nat) :
  network_word_traffic (exact_ntt_shared_network k) = k * 2 ^ k.
Proof.
by rewrite exact_ntt_shared_network_word_traffic_eq_work_from
           exact_ntt_shared_network_work.
Qed.

Lemma exact_ntt_shared_network_latency_sum_from (stride k : nat) :
  network_latency_sum (exact_ntt_shared_network_from stride k) = k.
Proof.
elim: k stride => [|k' IH] stride //=.
rewrite shared_network_eq_rect_latency_sum network_latency_sum_cat /=.
by rewrite parallel_network_latency_sum_self IH addn1.
Qed.

Lemma exact_ntt_shared_network_latency_sum (k : nat) :
  network_latency_sum (exact_ntt_shared_network k) = k.
Proof. exact: exact_ntt_shared_network_latency_sum_from. Qed.

Lemma exact_ntt_shared_network_span (k : nat) :
  network_cycles (exact_ntt_shared_network k)
                 (asap_schedule (exact_ntt_shared_network k)) = k.
Proof. by rewrite network_cycles_asap exact_ntt_shared_network_latency_sum. Qed.

End ExactNTTSharedComplexity.

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

(** ** Transport lemmas for eq_rect on gates *)

Lemma depth_eq_rect (n m : nat) (G : Type) (g : gate n G) (Heq : n = m) :
  depth (eq_rect n (fun p => gate p G) g m Heq) = depth g.
Proof. by subst. Qed.

Lemma reach_eq_rect_full (n m : nat) (G : Type) (g : gate n G) (Heq : n = m) :
  reach g = [set: 'I_n] ->
  reach (eq_rect n (fun p => gate p G) g m Heq) = [set: 'I_m].
Proof. by subst. Qed.

Lemma lshift_rshift_cover (n : nat) :
  (@lshift n n @: [set: 'I_n]) :|: (@rshift n n @: [set: 'I_n]) = [set: 'I_(n + n)].
Proof.
apply/setP => i; rewrite in_setU in_setT; apply/orP.
case Hs: (split i) => [j | j].
- left; apply/imsetP; exists j => //.
  by move: (splitK i); rewrite Hs /= => ->.
- right; apply/imsetP; exists j => //.
  by move: (splitK i); rewrite Hs /= => ->.
Qed.

Lemma gate_size_eq_rect (n m : nat) (G : Type) (g : gate n G) (Heq : n = m) :
  gate_size (eq_rect n (fun p => gate p G) g m Heq) = gate_size g.
Proof. by subst. Qed.

Lemma lift_gate_size (m p : nat) (G : Type) (f : 'I_m -> 'I_p) (g : gate m G) :
  gate_size (lift_gate f g) = gate_size g.
Proof. by elim: g => //= tag g1 -> g2 ->. Qed.

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

Lemma bfly_depth (k : nat) (j : 'I_(2 ^ k)) :
  depth (@bfly_gates k j) = k.
Proof.
elim: k j => [|k' IH] j //=.
by rewrite depth_eq_rect /= !lift_gate_depth !IH maxnn.
Qed.

Lemma bfly_reach_full (k : nat) (j : 'I_(2 ^ k)) :
  reach (@bfly_gates k j) = [set: 'I_(2 ^ k)].
Proof.
elim: k j => [|k' IH] j /=.
- by apply/setP => i; rewrite in_set1 in_setT (ord1 i).
- apply: reach_eq_rect_full.
  rewrite /= !lift_gate_reach !IH; exact: lshift_rshift_cover.
Qed.

Lemma butterfly_full_dep (k : nat) :
  full_dependence (butterfly_circuit k).
Proof.
by move=> j; rewrite /circ_reach /butterfly_circuit ffunE; exact: bfly_reach_full.
Qed.

Lemma butterfly_depth (k : nat) :
  circ_depth (butterfly_circuit k) = k.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply/bigmax_leqP => j _; by rewrite /butterfly_circuit ffunE bfly_depth.
- by apply: full_dep_depth_bound => //; exact: butterfly_full_dep.
Qed.

Lemma bfly_gate_size_succ (k : nat) (j : 'I_(2 ^ k)) :
  (gate_size (@bfly_gates k j)).+1 = (2 ^ k)%N.
Proof.
elim: k j => [|k' IH] j //=.
rewrite gate_size_eq_rect /= !lift_gate_size.
by rewrite -addSn -addnS !IH addnn -mul2n -expnS.
Qed.

Lemma bfly_gate_size (k : nat) (j : 'I_(2 ^ k)) :
  gate_size (@bfly_gates k j) = (2 ^ k - 1)%N.
Proof.
by have /(f_equal predn) := bfly_gate_size_succ j; rewrite /= subn1.
Qed.

Lemma butterfly_work (k : nat) :
  circ_work (butterfly_circuit k) = (2 ^ k * (2 ^ k - 1))%N.
Proof.
rewrite /circ_work (eq_bigr (fun _ => (2 ^ k - 1)%N)); last first.
  by move=> j _; rewrite /butterfly_circuit ffunE bfly_gate_size.
by rewrite sum_nat_const card_ord.
Qed.

Theorem butterfly_formula_tree_profile (k : nat) :
  full_dependence (butterfly_circuit k) /\
  circ_depth (butterfly_circuit k) = k /\
  circ_work (butterfly_circuit k) = (2 ^ k * (2 ^ k - 1))%N.
Proof.
split.
- exact: butterfly_full_dep.
- split.
  + exact: butterfly_depth.
  + exact: butterfly_work.
Qed.

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
(** * Proxy lower-bound packaging for bootstrapping                    *)
(* ================================================================== *)

(** [fhe_params] bundles the coefficient ring, dimension exponent,
    and a root of unity [omega] that is a unit.  The unit property
    drives the depth bound via the Vandermonde non-vanishing argument. *)

Record fhe_params := FHEParams {
  fhe_ring : GRing.ComUnitRing.type;
  ring_exp : nat;
  fhe_omega : fhe_ring;
  fhe_omega_unit : fhe_omega \is a GRing.unit;
}.

Definition ring_dim (p : fhe_params) : nat := (2 ^ ring_exp p)%N.

Local Open Scope ring_scope.

Record negacyclic_root_data := NegacyclicRootData {
  ngr_ring : GRing.ComUnitRing.type;
  ngr_exp : nat;
  ngr_omega : ngr_ring;
  ngr_omega_unit : ngr_omega \is a GRing.unit;
  ngr_order : ngr_omega ^+ (2 ^ (ngr_exp.+1)) = 1;
  ngr_half_turn : ngr_omega ^+ (2 ^ ngr_exp) = -1;
}.

Definition ngr_dim (p : negacyclic_root_data) : nat := (2 ^ ngr_exp p)%N.
Definition ngr_order_modulus (p : negacyclic_root_data) : nat := (2 ^ ((ngr_exp p).+1))%N.

Lemma ngr_order_modulusE (p : negacyclic_root_data) :
  ngr_order_modulus p = (2 * ngr_dim p)%N.
Proof. by rewrite /ngr_order_modulus /ngr_dim expnS mulnC. Qed.

Definition ngr_as_fhe_params (p : negacyclic_root_data) : fhe_params :=
  {| fhe_ring := ngr_ring p;
     ring_exp := ngr_exp p;
     fhe_omega := ngr_omega p;
     fhe_omega_unit := ngr_omega_unit p |}.

Lemma ngr_order_law (p : negacyclic_root_data) :
  ngr_omega p ^+ ngr_order_modulus p = 1 :> ngr_ring p.
Proof. exact: ngr_order. Qed.

Lemma ngr_half_turn_law (p : negacyclic_root_data) :
  ngr_omega p ^+ ngr_dim p = -1 :> ngr_ring p.
Proof. exact: ngr_half_turn. Qed.

Theorem negacyclic_shared_ntt_depth_bound (p : negacyclic_root_data) :
  (ngr_exp p <= circ_depth (ntt_shared_circuit (ngr_exp p)))%N.
Proof.
exact: (@ntt_shared_circuit_depth_bound
          (ngr_ring p) (ngr_omega p) (ngr_omega_unit p) (ngr_exp p)).
Qed.

Theorem negacyclic_exact_shared_ntt_depth_bound (p : negacyclic_root_data) :
  (ngr_exp p <= circ_depth (exact_ntt_shared_circuit (ngr_exp p)))%N.
Proof.
exact: (@exact_ntt_shared_circuit_depth_bound
          (ngr_ring p) (ngr_omega p) (ngr_omega_unit p) (ngr_exp p)).
Qed.

Section NegacyclicExactOperator.

Variable p : negacyclic_root_data.

Definition negacyclic_poly := 'I_(ngr_dim p) -> ngr_ring p.

Definition exact_negacyclic_operator :
    negacyclic_poly -> 'I_(ngr_dim p) -> ngr_ring p :=
  @exact_ntt_shared_semantics (ngr_ring p) (ngr_omega p) (ngr_exp p).

Theorem exact_negacyclic_operator_network_exact
    (v : negacyclic_poly) (j : 'I_(ngr_dim p)) :
  eval_network (ntt_gate_semantics (ngr_omega p))
      (exact_ntt_shared_network (ngr_exp p)) v j =
  exact_negacyclic_operator v j.
Proof. exact: exact_ntt_shared_network_correct. Qed.

Theorem exact_negacyclic_operator_circuit_exact
    (v : negacyclic_poly) (j : 'I_(ngr_dim p)) :
  eval (ntt_gate_semantics (ngr_omega p)) v
       (exact_ntt_shared_circuit (ngr_exp p) j) =
  exact_negacyclic_operator v j.
Proof. exact: exact_ntt_shared_circuit_correct. Qed.

Theorem exact_negacyclic_operator_full_dep :
  func_full_dep (n := ngr_dim p) exact_negacyclic_operator.
Proof. exact: (@exact_ntt_shared_semantics_full_dep
                 (ngr_ring p) (ngr_omega p) (ngr_omega_unit p) (ngr_exp p)). Qed.

Theorem exact_negacyclic_operator_depth_bound
    (G : Type)
    (ops : G -> ngr_ring p -> ngr_ring p -> ngr_ring p)
    (C : circuit (ngr_dim p) G)
    (Hcomp : forall v j, exact_negacyclic_operator v j = eval ops v (C j)) :
  (ngr_exp p <= circ_depth C)%N.
Proof.
have Hfull : full_dependence C :=
  func_dep_implies_circ_dep Hcomp exact_negacyclic_operator_full_dep.
exact: full_dep_depth_bound (erefl _) Hfull.
Qed.

End NegacyclicExactOperator.

Section NegacyclicQuotientEvaluation.

Variable p : negacyclic_root_data.

Definition half_ord (k : nat) (i : 'I_(2 ^ k.+1)) : 'I_(2 ^ k).
Proof.
apply: (@Ordinal (2 ^ k) ((val i)./2)).
rewrite ltn_half_double.
have Hi : (val i < 2 ^ k.+1)%N := ltn_ord i.
suff -> : ((2 ^ k).*2 = 2 ^ k.+1)%N by exact: Hi.
by rewrite expnS mulnC -muln2.
Defined.

Arguments half_ord _ _ : clear implicits.

Lemma val_half_ord (k : nat) (i : 'I_(2 ^ k.+1)) :
  val (half_ord k i) = (val i)./2.
Proof. by []. Qed.

Lemma half_ord_even (k : nat) (i : 'I_(2 ^ k)) :
  half_ord k (@even_ord k i) = i.
Proof.
apply/val_inj.
by rewrite val_half_ord val_even_ord half_double.
Qed.

Lemma half_ord_odd (k : nat) (i : 'I_(2 ^ k)) :
  half_ord k (@odd_ord k i) = i.
Proof.
apply/val_inj.
by rewrite val_half_ord val_odd_ord /= uphalf_double.
Qed.

Lemma odd_even_ord (k : nat) (i : 'I_(2 ^ k)) :
  odd (val (@even_ord k i)) = false.
Proof. by rewrite val_even_ord odd_double. Qed.

Lemma odd_odd_ord (k : nat) (i : 'I_(2 ^ k)) :
  odd (val (@odd_ord k i)) = true.
Proof. by rewrite val_odd_ord /= odd_double. Qed.

Lemma even_ord_half_ord (k : nat) (i : 'I_(2 ^ k.+1)) :
  ~~ odd (val i) ->
  @even_ord k (half_ord k i) = i.
Proof.
move=> Heven.
apply/val_inj.
by rewrite val_even_ord val_half_ord even_halfK.
Qed.

Lemma odd_ord_half_ord (k : nat) (i : 'I_(2 ^ k.+1)) :
  odd (val i) ->
  @odd_ord k (half_ord k i) = i.
Proof.
move=> Hodd.
apply/val_inj.
rewrite val_odd_ord val_half_ord.
have H := odd_double_half (val i).
rewrite Hodd addnC in H.
rewrite addn1 in H.
exact H.
Qed.

Definition coeff_eval_at (k : nat)
    (x : ngr_ring p) (v : 'I_(2 ^ k) -> ngr_ring p) : ngr_ring p :=
  \sum_(i < 2 ^ k) v i * x ^+ val i.

Lemma coeff_eval_at_split
    (k : nat) (x : ngr_ring p) (v : 'I_(2 ^ k.+1) -> ngr_ring p) :
  coeff_eval_at x v =
    coeff_eval_at (x ^+ 2) (fun i => v (@even_ord k i)) +
    x * coeff_eval_at (x ^+ 2) (fun i => v (@odd_ord k i)).
Proof.
rewrite /coeff_eval_at (bigID (fun i : 'I_(2 ^ k.+1) => odd i)) /= addrC.
congr (_ + _).
- transitivity (\sum_(i < 2 ^ k) v (@even_ord k i) * x ^+ i.*2).
  + rewrite (reindex_onto (@even_ord k) (@half_ord k)) /=.
    * rewrite (eq_bigl (fun _ => true)).
        by [].
      move=> i.
      by rewrite odd_double half_ord_even eqxx.
    * move=> i.
      exact: even_ord_half_ord.
  + apply: eq_bigr => i _.
    by rewrite -muln2 mulnC -exprM.
- transitivity
    (\sum_(i < 2 ^ k) x * (v (@odd_ord k i) * (x ^+ 2) ^+ i)).
  + rewrite (reindex_onto (@odd_ord k) (@half_ord k)) /=.
    * transitivity (\sum_(i < 2 ^ k) v (@odd_ord k i) * x ^+ i.*2.+1).
      -- rewrite (eq_bigl (fun _ => true)).
           by [].
         move=> i.
         by rewrite odd_double half_ord_odd eqxx.
      -- apply: eq_bigr => i _.
         rewrite exprS -muln2 mulnC -exprM.
         by rewrite mulrCA.
    * move=> i Hodd.
      exact: odd_ord_half_ord.
  + by rewrite -mulr_sumr.
Qed.

Definition negacyclic_eval_point (j : 'I_(ngr_dim p)) : ngr_ring p :=
  ngr_omega p ^+ (2 * val j + 1).

Definition negacyclic_quotient_eval
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) : ngr_ring p :=
  \sum_(i < ngr_dim p) v i * negacyclic_eval_point j ^+ val i.

Definition negacyclic_recursive_eval
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) : ngr_ring p :=
  @exact_ntt_bitrev_eval (ngr_ring p) (ngr_omega p) (ngr_exp p) 1 v j.

Theorem exact_negacyclic_operator_on_bitrev
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) :
  exact_negacyclic_operator (@bitrev_state (ngr_ring p) (ngr_exp p) v) j =
  negacyclic_recursive_eval v j.
Proof.
exact: (@exact_ntt_shared_semantics_bitrev
          (ngr_ring p) (ngr_omega p) (ngr_exp p) v j).
Qed.

Theorem exact_ntt_bitrev_eval_closed_form
    (k stride : nat)
    (v : 'I_(2 ^ k) -> ngr_ring p) (j : 'I_(2 ^ k))
    (Horder : ngr_omega p ^+ (stride * (2 ^ k.+1)) = 1)
    (Hhalf : ngr_omega p ^+ (stride * (2 ^ k)) = -1) :
  @exact_ntt_bitrev_eval (ngr_ring p) (ngr_omega p) k stride v j =
  coeff_eval_at (ngr_omega p ^+ (stride * (2 * val j + 1))) v.
Proof.
elim: k stride v j Horder Hhalf => [|k IH] stride v j Horder Hhalf /=.
- rewrite /coeff_eval_at big_ord1 /= expr0 mulr1.
  by [].
- have Horder' : ngr_omega p ^+ (stride.*2 * (2 ^ k.+1)) = 1.
    have -> : (stride.*2 * (2 ^ k.+1) = stride * (2 * 2 ^ k.+1))%N.
      by rewrite -muln2 -mulnA.
    have -> : (stride * (2 * 2 ^ k.+1) = stride * (2 ^ k.+2))%N.
      by rewrite [in RHS]expnS.
    exact: Horder.
  have Hhalf' : ngr_omega p ^+ (stride.*2 * (2 ^ k)) = -1.
    have -> : (stride.*2 * (2 ^ k) = stride * (2 * 2 ^ k))%N.
      by rewrite -muln2 -mulnA.
    have -> : (stride * (2 * 2 ^ k) = stride * (2 ^ k.+1))%N.
      by rewrite [in RHS]expnS.
    exact: Hhalf.
  case Hj: (split (@cast_ord (2 ^ k.+1) ((2 ^ k) + (2 ^ k))
                            (esym (ntt_half_size_eq k)) j)) => [i|i] /=.
  + have -> : j = @ntt_left_output k i by exact: ntt_left_outputP Hj.
    pose x := ngr_omega p ^+ (stride * (2 * val i + 1)).
    have Hx2 : x ^+ 2 = ngr_omega p ^+ (stride.*2 * (2 * val i + 1)).
      rewrite /x -exprM.
      pose a := (2 * val i + 1)%N.
      have -> : (stride * a * 2 = (stride + stride) * a)%N.
        by rewrite muln2 doubleMl addnn.
      by rewrite /a addnn.
    rewrite IH // IH //.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride.*2 * (2 * val i + 1)))
          (fun t => v (@even_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@even_ord k t)).
      by rewrite -Hx2.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride.*2 * (2 * val i + 1)))
          (fun t => v (@odd_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@odd_ord k t)).
      by rewrite -Hx2.
    rewrite /ntt_twiddle /x val_ntt_left_output.
    have Hiodd : i.*2.+1 = 2 * val i + 1.
      have -> : 2 * val i + 1 = (2 * val i).+1.
        exact: addn1.
      by rewrite -muln2 mulnC.
    have -> :
        ngr_omega p ^+ (stride * i.*2.+1) =
        ngr_omega p ^+ (stride * (2 * val i + 1)).
      by rewrite Hiodd.
    symmetry.
    exact: coeff_eval_at_split.
  + have -> : j = @ntt_right_output k i by exact: ntt_right_outputP Hj.
    pose x := ngr_omega p ^+ (stride * (2 * val i + 1)).
    have Hx2 : x ^+ 2 = ngr_omega p ^+ (stride.*2 * (2 * val i + 1)).
      rewrite /x -exprM.
      pose a := (2 * val i + 1)%N.
      have -> : (stride * a * 2 = (stride + stride) * a)%N.
        by rewrite muln2 doubleMl addnn.
      by rewrite /a addnn.
    have Hright :
        ngr_omega p ^+ (stride * (2 * val (@ntt_right_output k i) + 1)) = - x.
      rewrite val_ntt_right_output /x.
      have Hshift : (2 ^ k + val i = val i + 2 ^ k)%N.
        by rewrite addnC.
      have -> :
          (stride * (2 * (2 ^ k + val i) + 1) =
           stride * (2 * val i + 1) + stride * (2 ^ k.+1))%N.
        rewrite Hshift expnS -mulnDr.
        congr (stride * _)%N.
        by rewrite mulnDr addnAC.
      by rewrite exprD Hhalf mulrN1.
    have Hneg2 : (- x) ^+ 2 = x ^+ 2.
      by rewrite !expr2 mulrNN.
    rewrite IH // IH //.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride.*2 * (2 * val i + 1)))
          (fun t => v (@even_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@even_ord k t)).
      by rewrite -Hx2.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride.*2 * (2 * val i + 1)))
          (fun t => v (@odd_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@odd_ord k t)).
      by rewrite -Hx2.
    rewrite /ntt_twiddle /x.
    rewrite Hright.
    have Hiodd : i.*2.+1 = 2 * val i + 1.
      have -> : 2 * val i + 1 = (2 * val i).+1.
        exact: addn1.
      by rewrite -muln2 mulnC.
    have -> : ngr_omega p ^+ (stride * i.*2.+1) = x.
      by rewrite /x Hiodd.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride * (2 * val i + 1)) ^+ 2)
          (fun t => v (@even_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@even_ord k t)).
      by rewrite /x.
    have -> :
        coeff_eval_at (ngr_omega p ^+ (stride * (2 * val i + 1)) ^+ 2)
          (fun t => v (@odd_ord k t)) =
        coeff_eval_at (x ^+ 2) (fun t => v (@odd_ord k t)).
      by rewrite /x.
    symmetry.
    rewrite coeff_eval_at_split Hneg2.
    by rewrite mulNr.
Qed.

Theorem negacyclic_recursive_eval_closed_form
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) :
  negacyclic_recursive_eval v j = negacyclic_quotient_eval v j.
Proof.
rewrite /negacyclic_recursive_eval /negacyclic_quotient_eval /negacyclic_eval_point /coeff_eval_at.
have Horder1 : ngr_omega p ^+ (1 * 2 ^ (ngr_exp p).+1) = 1.
  by rewrite mul1n ngr_order.
have Hhalf1 : ngr_omega p ^+ (1 * 2 ^ ngr_exp p) = -1.
  by rewrite mul1n ngr_half_turn.
have Hclosed :=
    @exact_ntt_bitrev_eval_closed_form (ngr_exp p) 1 v j Horder1 Hhalf1.
rewrite /coeff_eval_at mul1n in Hclosed.
exact Hclosed.
Qed.

Theorem exact_negacyclic_operator_quotient_on_bitrev
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) :
  exact_negacyclic_operator (@bitrev_state (ngr_ring p) (ngr_exp p) v) j =
  negacyclic_quotient_eval v j.
Proof.
by rewrite exact_negacyclic_operator_on_bitrev negacyclic_recursive_eval_closed_form.
Qed.

Theorem negacyclic_quotient_circuit_from_exact
    (G : Type)
    (ops : G -> ngr_ring p -> ngr_ring p -> ngr_ring p)
    (C : circuit (ngr_dim p) G)
    (Hcomp : forall v j, exact_negacyclic_operator v j = eval ops v (C j))
    (v : 'I_(ngr_dim p) -> ngr_ring p) (j : 'I_(ngr_dim p)) :
  negacyclic_quotient_eval v j =
  eval ops v (subst_circuit C (@bitrev_input_circuit (ngr_exp p) G) j).
Proof.
rewrite -exact_negacyclic_operator_quotient_on_bitrev.
rewrite eval_subst_circuit.
rewrite -Hcomp.
have Hstate :
    (fun i => eval ops v (@bitrev_input_circuit (ngr_exp p) G i)) =
    @bitrev_state (ngr_ring p) (ngr_exp p) v.
  apply: boolp.functional_extensionality_dep => i.
  exact: bitrev_input_circuit_eval.
by rewrite Hstate.
Qed.

Theorem negacyclic_quotient_circuit_from_exact_depth
    (G : Type)
    (C : circuit (ngr_dim p) G) :
  circ_depth (subst_circuit C (@bitrev_input_circuit (ngr_exp p) G)) =
  circ_depth C.
Proof.
rewrite circ_depth_subst_circuit0 => // i.
exact: bitrev_input_circuit_gate_depth.
Qed.

Definition negacyclic_origin_index : 'I_(ngr_dim p) :=
  Ordinal (expn_gt0 2 (ngr_exp p)).

Lemma negacyclic_eval_point_unit (j : 'I_(ngr_dim p)) :
  negacyclic_eval_point j \is a GRing.unit.
Proof. exact: unitrX (ngr_omega_unit p). Qed.

Lemma negacyclic_origin_point :
  negacyclic_eval_point negacyclic_origin_index = ngr_omega p :> ngr_ring p.
Proof. by rewrite /negacyclic_eval_point /negacyclic_origin_index /= expr1. Qed.

Lemma negacyclic_origin_point_order :
  negacyclic_eval_point negacyclic_origin_index ^+ ngr_order_modulus p = 1
    :> ngr_ring p.
Proof. by rewrite negacyclic_origin_point ngr_order_law. Qed.

Lemma negacyclic_origin_point_dim :
  negacyclic_eval_point negacyclic_origin_index ^+ ngr_dim p = -1
    :> ngr_ring p.
Proof. by rewrite negacyclic_origin_point ngr_half_turn_law. Qed.

Lemma negacyclic_origin_point_annihilates_quotient :
  negacyclic_eval_point negacyclic_origin_index ^+ ngr_dim p + 1 = 0
    :> ngr_ring p.
Proof. by rewrite negacyclic_origin_point_dim addNr. Qed.

End NegacyclicQuotientEvaluation.

(* ================================================================== *)
(** * Abstract bootstrapping operator shell                           *)
(* ================================================================== *)

Section BootstrappingOperator.

Variables (params : fhe_params) (ciphertext digits noise : Type).

(** We represent elements of [R[X]/(X^N+1)] by their reduced
    coefficient vectors of length [N = 2^k]. *)
Definition quotient_poly := 'I_(ring_dim params) -> fhe_ring params.

Record bootstrapping_input := BootstrappingInput {
  bs_input_poly : quotient_poly;
  bs_input_ciphertext : ciphertext;
  bs_input_noise : noise;
}.

Record bootstrapping_output := BootstrappingOutput {
  bs_output_poly : quotient_poly;
  bs_output_ciphertext : ciphertext;
  bs_output_noise : noise;
}.

Record bootstrapping_trace := BootstrappingTrace {
  bs_trace_forward_ntt : quotient_poly;
  bs_trace_pointwise : quotient_poly;
  bs_trace_inverse_ntt : quotient_poly;
  bs_trace_digits : digits;
  bs_trace_keyswitched : ciphertext;
  bs_trace_modswitched : ciphertext;
  bs_trace_noise : noise;
}.

Record bootstrapping_operator := BootstrappingOperator {
  bs_forward_ntt : quotient_poly -> quotient_poly;
  bs_pointwise_step : quotient_poly -> quotient_poly;
  bs_inverse_ntt : quotient_poly -> quotient_poly;
  bs_digit_extract : ciphertext -> digits;
  bs_key_switch : digits -> ciphertext -> ciphertext;
  bs_mod_switch : ciphertext -> ciphertext;
  bs_noise_update : noise -> ciphertext -> noise;
}.

Definition run_bootstrapping_trace
    (B : bootstrapping_operator) (x : bootstrapping_input) :
    bootstrapping_trace :=
  let forward := bs_forward_ntt B (bs_input_poly x) in
  let pointwise := bs_pointwise_step B forward in
  let inverse := bs_inverse_ntt B pointwise in
  let extracted := bs_digit_extract B (bs_input_ciphertext x) in
  let keyswitched := bs_key_switch B extracted (bs_input_ciphertext x) in
  let modswitched := bs_mod_switch B keyswitched in
  let noise' := bs_noise_update B (bs_input_noise x) modswitched in
  BootstrappingTrace forward pointwise inverse extracted keyswitched modswitched noise'.

Definition run_bootstrapping
    (B : bootstrapping_operator) (x : bootstrapping_input) :
    bootstrapping_output :=
  let tr := run_bootstrapping_trace B x in
  BootstrappingOutput (bs_trace_inverse_ntt tr)
                     (bs_trace_modswitched tr)
                     (bs_trace_noise tr).

Lemma run_bootstrapping_poly (B : bootstrapping_operator) (x : bootstrapping_input) :
  bs_output_poly (run_bootstrapping B x) =
    bs_inverse_ntt B (bs_pointwise_step B (bs_forward_ntt B (bs_input_poly x))).
Proof. by []. Qed.

Lemma run_bootstrapping_ciphertext
    (B : bootstrapping_operator) (x : bootstrapping_input) :
  bs_output_ciphertext (run_bootstrapping B x) =
    bs_mod_switch B (bs_key_switch B (bs_digit_extract B (bs_input_ciphertext x))
                                   (bs_input_ciphertext x)).
Proof. by []. Qed.

Lemma run_bootstrapping_noise (B : bootstrapping_operator) (x : bootstrapping_input) :
  bs_output_noise (run_bootstrapping B x) =
    bs_noise_update B (bs_input_noise x)
      (bs_mod_switch B (bs_key_switch B (bs_digit_extract B (bs_input_ciphertext x))
                                      (bs_input_ciphertext x))).
Proof. by []. Qed.

End BootstrappingOperator.

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

Theorem negacyclic_bootstrapping_depth_bound
    (p : negacyclic_root_data) (G : Type)
    (ops : G -> ngr_ring p -> ngr_ring p -> ngr_ring p)
    (C : circuit (ngr_dim p) G)
    (Hcomp : forall v j,
      vandermonde_eval (ngr_omega p) v j = eval ops v (C j)) :
  (ngr_exp p <= circ_depth C)%N.
Proof.
exact: (@bootstrapping_depth_bound (ngr_as_fhe_params p) G ops C Hcomp).
Qed.

Record verified_layer := VerifiedLayer {
  vl_width : nat;
  vl_carrier : Type;
  vl_tag : Type;
  vl_ops : vl_tag -> vl_carrier -> vl_carrier -> vl_carrier;
  vl_circuit : circuit vl_width vl_tag;
  vl_semantics : ('I_vl_width -> vl_carrier) -> 'I_vl_width -> vl_carrier;
  vl_correct : forall v j, vl_semantics v j = eval vl_ops v (vl_circuit j);
  vl_depth_lb : nat;
  vl_depth_cert : (vl_depth_lb <= circ_depth vl_circuit)%N;
}.

Section VerifiedPipeline.

Variables (params : fhe_params) (ctxt_width digit_width noise_width : nat).
Variables (ciphertext digits noise : Type).

Record verified_bootstrapping_pipeline := VerifiedBootstrappingPipeline {
  vbp_forward_ntt : verified_layer;
  vbp_forward_ntt_width : vl_width vbp_forward_ntt = ring_dim params;
  vbp_forward_ntt_carrier : vl_carrier vbp_forward_ntt = fhe_ring params;
  vbp_forward_ntt_bound : (ring_exp params <= vl_depth_lb vbp_forward_ntt)%N;

  vbp_pointwise_step : verified_layer;
  vbp_pointwise_width : vl_width vbp_pointwise_step = ring_dim params;
  vbp_pointwise_carrier : vl_carrier vbp_pointwise_step = fhe_ring params;

  vbp_inverse_ntt : verified_layer;
  vbp_inverse_ntt_width : vl_width vbp_inverse_ntt = ring_dim params;
  vbp_inverse_ntt_carrier : vl_carrier vbp_inverse_ntt = fhe_ring params;
  vbp_inverse_ntt_bound : (ring_exp params <= vl_depth_lb vbp_inverse_ntt)%N;

  vbp_digit_extract : verified_layer;
  vbp_digit_extract_width : vl_width vbp_digit_extract = digit_width;
  vbp_digit_extract_carrier : vl_carrier vbp_digit_extract = digits;

  vbp_key_switch : verified_layer;
  vbp_key_switch_width : vl_width vbp_key_switch = ctxt_width;
  vbp_key_switch_carrier : vl_carrier vbp_key_switch = ciphertext;

  vbp_mod_switch : verified_layer;
  vbp_mod_switch_width : vl_width vbp_mod_switch = ctxt_width;
  vbp_mod_switch_carrier : vl_carrier vbp_mod_switch = ciphertext;

  vbp_noise_update : verified_layer;
  vbp_noise_update_width : vl_width vbp_noise_update = noise_width;
  vbp_noise_update_carrier : vl_carrier vbp_noise_update = noise;
}.

Definition pipeline_depth_lower_bound (P : verified_bootstrapping_pipeline) : nat :=
  vl_depth_lb (vbp_forward_ntt P) +
  (vl_depth_lb (vbp_pointwise_step P) +
   (vl_depth_lb (vbp_inverse_ntt P) +
    (vl_depth_lb (vbp_digit_extract P) +
     (vl_depth_lb (vbp_key_switch P) +
      (vl_depth_lb (vbp_mod_switch P) +
       vl_depth_lb (vbp_noise_update P)))))).

Definition pipeline_sequential_depth (P : verified_bootstrapping_pipeline) : nat :=
  circ_depth (vl_circuit (vbp_forward_ntt P)) +
  (circ_depth (vl_circuit (vbp_pointwise_step P)) +
   (circ_depth (vl_circuit (vbp_inverse_ntt P)) +
    (circ_depth (vl_circuit (vbp_digit_extract P)) +
     (circ_depth (vl_circuit (vbp_key_switch P)) +
      (circ_depth (vl_circuit (vbp_mod_switch P)) +
       circ_depth (vl_circuit (vbp_noise_update P))))))).

Lemma pipeline_depth_lower_bound_sound (P : verified_bootstrapping_pipeline) :
  (pipeline_depth_lower_bound P <= pipeline_sequential_depth P)%N.
Proof.
have Hforward :
    (vl_depth_lb (vbp_forward_ntt P) <=
     circ_depth (vl_circuit (vbp_forward_ntt P)))%N :=
  vl_depth_cert (vbp_forward_ntt P).
have Hpointwise :
    (vl_depth_lb (vbp_pointwise_step P) <=
     circ_depth (vl_circuit (vbp_pointwise_step P)))%N :=
  vl_depth_cert (vbp_pointwise_step P).
have Hinverse :
    (vl_depth_lb (vbp_inverse_ntt P) <=
     circ_depth (vl_circuit (vbp_inverse_ntt P)))%N :=
  vl_depth_cert (vbp_inverse_ntt P).
have Hdigits :
    (vl_depth_lb (vbp_digit_extract P) <=
     circ_depth (vl_circuit (vbp_digit_extract P)))%N :=
  vl_depth_cert (vbp_digit_extract P).
have Hkey :
    (vl_depth_lb (vbp_key_switch P) <=
     circ_depth (vl_circuit (vbp_key_switch P)))%N :=
  vl_depth_cert (vbp_key_switch P).
have Hmod :
    (vl_depth_lb (vbp_mod_switch P) <=
     circ_depth (vl_circuit (vbp_mod_switch P)))%N :=
  vl_depth_cert (vbp_mod_switch P).
have Hnoise :
    (vl_depth_lb (vbp_noise_update P) <=
     circ_depth (vl_circuit (vbp_noise_update P)))%N :=
  vl_depth_cert (vbp_noise_update P).
rewrite /pipeline_depth_lower_bound /pipeline_sequential_depth.
apply: leq_add Hforward _.
apply: leq_add Hpointwise _.
apply: leq_add Hinverse _.
apply: leq_add Hdigits _.
apply: leq_add Hkey _.
apply: leq_add Hmod _.
exact: Hnoise.
Qed.

Theorem pipeline_preserves_ntt_critical_path (P : verified_bootstrapping_pipeline) :
  (ring_exp params <= pipeline_depth_lower_bound P)%N.
Proof.
rewrite /pipeline_depth_lower_bound.
pose rest :=
  vl_depth_lb (vbp_pointwise_step P) +
  (vl_depth_lb (vbp_inverse_ntt P) +
   (vl_depth_lb (vbp_digit_extract P) +
    (vl_depth_lb (vbp_key_switch P) +
     (vl_depth_lb (vbp_mod_switch P) +
      vl_depth_lb (vbp_noise_update P))))).
have Htail :
    (vl_depth_lb (vbp_forward_ntt P) <= pipeline_depth_lower_bound P)%N.
  have -> :
      pipeline_depth_lower_bound P =
      vl_depth_lb (vbp_forward_ntt P) + rest.
    by rewrite /pipeline_depth_lower_bound /rest.
  exact: leq_addr.
exact: leq_trans (vbp_forward_ntt_bound P) Htail.
Qed.

Theorem pipeline_global_depth_lower_bound (P : verified_bootstrapping_pipeline) :
  (ring_exp params <= pipeline_sequential_depth P)%N.
Proof.
exact: leq_trans (pipeline_preserves_ntt_critical_path P)
                 (pipeline_depth_lower_bound_sound P).
Qed.

End VerifiedPipeline.

(* ================================================================== *)
(** * Typed heterogeneous bootstrapping circuits                       *)
(* ================================================================== *)

Record typed_bundle := TypedBundle {
  tb_width : nat;
  tb_carrier : Type;
}.

Definition bundle_state (B : typed_bundle) : Type :=
  'I_(tb_width B) -> tb_carrier B.

Arguments bundle_state _ : clear implicits.

Definition singleton_bundle (T : Type) : typed_bundle :=
  TypedBundle 1 T.

Definition singleton_state {T : Type} (x : T) :
    bundle_state (singleton_bundle T) :=
  fun _ => x.

Definition singleton_value {T : Type}
    (s : bundle_state (singleton_bundle T)) : T :=
  s ord0.

Lemma singleton_value_state (T : Type) (x : T) :
  singleton_value (singleton_state x) = x.
Proof. by []. Qed.

Record hetero_stage (src dst : typed_bundle) := HeteroStage {
  hs_semantics : bundle_state src -> bundle_state dst;
  hs_depth : nat;
  hs_depth_lb : nat;
  hs_depth_cert : (hs_depth_lb <= hs_depth)%N;
}.

Arguments hs_semantics [src dst] _ _ _.
Arguments hs_depth [src dst] _.
Arguments hs_depth_lb [src dst] _.
Arguments hs_depth_cert [src dst] _.

Inductive hetero_circuit : typed_bundle -> typed_bundle -> Type :=
| HCId : forall B, hetero_circuit B B
| HCSeq : forall A B C,
    hetero_stage A B -> hetero_circuit B C -> hetero_circuit A C.

Fixpoint hetero_eval
    (A B : typed_bundle) (C : hetero_circuit A B) :
    bundle_state A -> bundle_state B :=
  match C in hetero_circuit A0 B0 return bundle_state A0 -> bundle_state B0 with
  | HCId _ => fun s => s
  | HCSeq _ _ _ st rest => fun s => hetero_eval rest (hs_semantics st s)
  end.

Fixpoint hetero_depth
    (A B : typed_bundle) (C : hetero_circuit A B) : nat :=
  match C with
  | HCId _ => 0
  | HCSeq _ _ _ st rest => hs_depth st + hetero_depth rest
  end.

Fixpoint hetero_depth_lower_bound
    (A B : typed_bundle) (C : hetero_circuit A B) : nat :=
  match C with
  | HCId _ => 0
  | HCSeq _ _ _ st rest => hs_depth_lb st + hetero_depth_lower_bound rest
  end.

Lemma hetero_depth_lower_bound_sound
    (A B : typed_bundle) (C : hetero_circuit A B) :
  (hetero_depth_lower_bound C <= hetero_depth C)%N.
Proof.
elim: C => [B0|A0 B0 C0 st rest IH] //=.
apply: leq_add.
- exact: hs_depth_cert.
- exact: IH.
Qed.

Section TypedBootstrappingObject.

Variables (params : fhe_params) (ciphertext digits noise : Type).

Definition tb_quotient_poly := 'I_(ring_dim params) -> fhe_ring params.

Record tb_input_state := TypedBootstrappingInput {
  tbi_poly : tb_quotient_poly;
  tbi_ciphertext : ciphertext;
  tbi_noise : noise;
}.

Record tb_forward_state := TypedForwardState {
  tbf_poly : tb_quotient_poly;
  tbf_ciphertext : ciphertext;
  tbf_noise : noise;
}.

Record tb_pointwise_state := TypedPointwiseState {
  tbp_poly : tb_quotient_poly;
  tbp_ciphertext : ciphertext;
  tbp_noise : noise;
}.

Record tb_inverse_state := TypedInverseState {
  tbinv_poly : tb_quotient_poly;
  tbinv_ciphertext : ciphertext;
  tbinv_noise : noise;
}.

Record tb_digits_state := TypedDigitsState {
  tbd_poly : tb_quotient_poly;
  tbd_digits : digits;
  tbd_ciphertext : ciphertext;
  tbd_noise : noise;
}.

Record tb_keyswitch_state := TypedKeySwitchState {
  tbk_poly : tb_quotient_poly;
  tbk_ciphertext : ciphertext;
  tbk_noise : noise;
}.

Record tb_modswitch_state := TypedModSwitchState {
  tbm_poly : tb_quotient_poly;
  tbm_ciphertext : ciphertext;
  tbm_noise : noise;
}.

Record tb_output_state := TypedBootstrappingOutput {
  tbo_poly : tb_quotient_poly;
  tbo_ciphertext : ciphertext;
  tbo_noise : noise;
}.

Record tb_trace := TypedBootstrappingTrace {
  tbt_forward : tb_forward_state;
  tbt_pointwise : tb_pointwise_state;
  tbt_inverse : tb_inverse_state;
  tbt_digits : tb_digits_state;
  tbt_keyswitch : tb_keyswitch_state;
  tbt_modswitch : tb_modswitch_state;
  tbt_output : tb_output_state;
}.

Definition tb_input_bundle := singleton_bundle tb_input_state.
Definition tb_forward_bundle := singleton_bundle tb_forward_state.
Definition tb_pointwise_bundle := singleton_bundle tb_pointwise_state.
Definition tb_inverse_bundle := singleton_bundle tb_inverse_state.
Definition tb_digits_bundle := singleton_bundle tb_digits_state.
Definition tb_keyswitch_bundle := singleton_bundle tb_keyswitch_state.
Definition tb_modswitch_bundle := singleton_bundle tb_modswitch_state.
Definition tb_output_bundle := singleton_bundle tb_output_state.

Record verified_end_to_end_bootstrapping := VerifiedEndToEndBootstrapping {
  vtb_forward_ntt : hetero_stage tb_input_bundle tb_forward_bundle;
  vtb_forward_ntt_bound : (ring_exp params <= hs_depth_lb vtb_forward_ntt)%N;

  vtb_pointwise_step : hetero_stage tb_forward_bundle tb_pointwise_bundle;

  vtb_inverse_ntt : hetero_stage tb_pointwise_bundle tb_inverse_bundle;
  vtb_inverse_ntt_bound : (ring_exp params <= hs_depth_lb vtb_inverse_ntt)%N;

  vtb_digit_extract : hetero_stage tb_inverse_bundle tb_digits_bundle;
  vtb_key_switch : hetero_stage tb_digits_bundle tb_keyswitch_bundle;
  vtb_mod_switch : hetero_stage tb_keyswitch_bundle tb_modswitch_bundle;
  vtb_noise_update : hetero_stage tb_modswitch_bundle tb_output_bundle;
}.

Definition typed_bootstrapping_circuit
    (B : verified_end_to_end_bootstrapping) :
    hetero_circuit tb_input_bundle tb_output_bundle :=
  HCSeq (vtb_forward_ntt B)
    (HCSeq (vtb_pointwise_step B)
      (HCSeq (vtb_inverse_ntt B)
        (HCSeq (vtb_digit_extract B)
          (HCSeq (vtb_key_switch B)
            (HCSeq (vtb_mod_switch B)
                   (HCSeq (vtb_noise_update B) (HCId _))))))).

Definition typed_bootstrapping_depth
    (B : verified_end_to_end_bootstrapping) : nat :=
  hetero_depth (typed_bootstrapping_circuit B).

Definition typed_bootstrapping_depth_lower_bound
    (B : verified_end_to_end_bootstrapping) : nat :=
  hetero_depth_lower_bound (typed_bootstrapping_circuit B).

Definition run_typed_bootstrapping_trace
    (B : verified_end_to_end_bootstrapping) (x : tb_input_state) : tb_trace :=
  let s1 := singleton_value (hs_semantics (vtb_forward_ntt B) (singleton_state x)) in
  let s2 := singleton_value (hs_semantics (vtb_pointwise_step B) (singleton_state s1)) in
  let s3 := singleton_value (hs_semantics (vtb_inverse_ntt B) (singleton_state s2)) in
  let s4 := singleton_value (hs_semantics (vtb_digit_extract B) (singleton_state s3)) in
  let s5 := singleton_value (hs_semantics (vtb_key_switch B) (singleton_state s4)) in
  let s6 := singleton_value (hs_semantics (vtb_mod_switch B) (singleton_state s5)) in
  let s7 := singleton_value (hs_semantics (vtb_noise_update B) (singleton_state s6)) in
  TypedBootstrappingTrace s1 s2 s3 s4 s5 s6 s7.

Definition run_typed_bootstrapping
    (B : verified_end_to_end_bootstrapping) (x : tb_input_state) : tb_output_state :=
  singleton_value (hetero_eval (typed_bootstrapping_circuit B) (singleton_state x)).

Lemma run_typed_bootstrapping_eval
    (B : verified_end_to_end_bootstrapping) (x : tb_input_state) :
  run_typed_bootstrapping B x =
  singleton_value (hetero_eval (typed_bootstrapping_circuit B) (singleton_state x)).
Proof. by []. Qed.

Lemma typed_bootstrapping_depth_lower_bound_sound
    (B : verified_end_to_end_bootstrapping) :
  (typed_bootstrapping_depth_lower_bound B <=
   typed_bootstrapping_depth B)%N.
Proof. exact: hetero_depth_lower_bound_sound. Qed.

Theorem typed_bootstrapping_forward_stage_embeds
    (B : verified_end_to_end_bootstrapping) :
  (hs_depth_lb (vtb_forward_ntt B) <=
   typed_bootstrapping_depth_lower_bound B)%N.
Proof. by rewrite /typed_bootstrapping_depth_lower_bound /= leq_addr. Qed.

Theorem typed_bootstrapping_inverse_stage_embeds
    (B : verified_end_to_end_bootstrapping) :
  (hs_depth_lb (vtb_inverse_ntt B) <=
   typed_bootstrapping_depth_lower_bound B)%N.
Proof.
rewrite /typed_bootstrapping_depth_lower_bound /=.
set suffix := hs_depth_lb (vtb_digit_extract B) +
              (hs_depth_lb (vtb_key_switch B) +
               (hs_depth_lb (vtb_mod_switch B) +
                (hs_depth_lb (vtb_noise_update B) + 0))).
have Hsuffix :
    (hs_depth_lb (vtb_inverse_ntt B) <=
     hs_depth_lb (vtb_inverse_ntt B) + suffix)%N.
  exact: leq_addr.
have Hpointwise :
    (hs_depth_lb (vtb_inverse_ntt B) + suffix <=
     hs_depth_lb (vtb_pointwise_step B) +
     (hs_depth_lb (vtb_inverse_ntt B) + suffix))%N.
  exact: leq_addl.
have Hforward :
    (hs_depth_lb (vtb_pointwise_step B) +
     (hs_depth_lb (vtb_inverse_ntt B) + suffix) <=
     hs_depth_lb (vtb_forward_ntt B) +
     (hs_depth_lb (vtb_pointwise_step B) +
      (hs_depth_lb (vtb_inverse_ntt B) + suffix)))%N.
  exact: leq_addl.
have Hstages :
    (hs_depth_lb (vtb_inverse_ntt B) + suffix <=
     hs_depth_lb (vtb_forward_ntt B) +
     (hs_depth_lb (vtb_pointwise_step B) +
      (hs_depth_lb (vtb_inverse_ntt B) + suffix)))%N.
  exact: leq_trans Hpointwise Hforward.
exact (leq_trans Hsuffix Hstages).
Qed.

Theorem typed_bootstrapping_preserves_ntt_critical_path
    (B : verified_end_to_end_bootstrapping) :
  (ring_exp params <= typed_bootstrapping_depth_lower_bound B)%N.
Proof.
exact: leq_trans (vtb_forward_ntt_bound B)
                 (typed_bootstrapping_forward_stage_embeds B).
Qed.

Theorem typed_bootstrapping_global_depth_lower_bound
    (B : verified_end_to_end_bootstrapping) :
  (ring_exp params <= typed_bootstrapping_depth B)%N.
Proof.
exact: leq_trans (typed_bootstrapping_preserves_ntt_critical_path B)
                 (typed_bootstrapping_depth_lower_bound_sound B).
Qed.

End TypedBootstrappingObject.

Section NoiseGrowth.

Record noise_growth_model := NoiseGrowthModel {
  ng_refresh_noise : nat;
  ng_growth_per_multiplication : nat;
  ng_depth_budget : nat;
}.

Fixpoint noise_after (M : noise_growth_model) (depth : nat) : nat :=
  match depth with
  | 0 => ng_refresh_noise M
  | d.+1 => noise_after M d + ng_growth_per_multiplication M
  end.

Lemma noise_after0 (M : noise_growth_model) :
  noise_after M 0 = ng_refresh_noise M.
Proof. by []. Qed.

Lemma noise_afterS (M : noise_growth_model) (depth : nat) :
  noise_after M depth.+1 =
  noise_after M depth + ng_growth_per_multiplication M.
Proof. by []. Qed.

Definition bootstraps_needed (M : noise_growth_model) (depth : nat) : nat :=
  depth %/ (ng_depth_budget M).+1.

Lemma bootstraps_needed0 (M : noise_growth_model) :
  bootstraps_needed M 0 = 0.
Proof. by rewrite /bootstraps_needed div0n. Qed.

Theorem bootstrapping_frequency_injects_ntt_span
    (params : fhe_params) (ctxt_width digit_width noise_width depth : nat)
    (ciphertext digits noise : Type)
    (P : verified_bootstrapping_pipeline params ctxt_width digit_width noise_width
           ciphertext digits noise)
    (M : noise_growth_model) :
  (bootstraps_needed M depth * ring_exp params <=
   bootstraps_needed M depth * pipeline_sequential_depth P)%N.
Proof.
apply: leq_mul.
- exact: leqnn.
- exact: pipeline_global_depth_lower_bound.
Qed.

End NoiseGrowth.

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

(** The execution model attaches to the staged NTT workload; the
    verified pipeline above carries key switching, modulus switching,
    digit extraction, and noise-update layers explicitly. *)

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

Section MachineScheduling.

Variables (n : nat) (O : Type) (Net : shared_network n O).

Record shared_machine := SharedMachine {
  sm_processors : nat;
  sm_bandwidth : nat;
  sm_memory_hierarchy : seq nat;
  sm_schedule : schedule;
  sm_schedule_legal : legal_schedule Net sm_schedule;
}.

Definition machine_cycles (M : shared_machine) : nat :=
  network_cycles Net (sm_schedule M).

Theorem machine_cycles_ge_latency_sum (M : shared_machine) :
  (network_latency_sum Net <= machine_cycles M)%N.
Proof. exact: legal_schedule_cycles_lower (sm_schedule_legal M). Qed.

End MachineScheduling.

Section NTTAsapMachine.

Variables (processors bandwidth : nat) (memory_hierarchy : seq nat).

Definition ntt_asap_machine (k : nat) :
    shared_machine (ntt_shared_network k) :=
  {| sm_processors := processors;
     sm_bandwidth := bandwidth;
     sm_memory_hierarchy := memory_hierarchy;
     sm_schedule := asap_schedule (ntt_shared_network k);
     sm_schedule_legal := asap_schedule_legal (ntt_shared_network k) |}.

Theorem ntt_asap_machine_attains_span (k : nat) :
  machine_cycles (ntt_asap_machine k) = k.
Proof. exact: ntt_shared_network_span. Qed.

End NTTAsapMachine.

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

Section RooflineInstantiation.

Variable R : realType.

Open Scope ring_scope.

Lemma ntt_roofline_regime (tp bw w : R) :
  0 < tp -> 0 < bw -> 0 < w ->
  bw <= tp * w ->
  ntt_intensity w <= tp / bw.
Proof.
move=> Htp Hbw Hw Hbw_le.
rewrite /ntt_intensity -div1r.
have Hmul : 1 * bw <= tp * w by rewrite mul1r.
exact (@cross_mul_le R 1 w tp bw Hw Hbw Hmul).
Qed.

Definition concrete_word_bytes : R := 8%:R.
Definition concrete_tp : R := 1%:R.
Definition concrete_bw : R := 8%:R.

Lemma concrete_word_bytes_pos : 0 < concrete_word_bytes.
Proof. by rewrite /concrete_word_bytes. Qed.

Lemma concrete_tp_pos : 0 < concrete_tp.
Proof. by rewrite /concrete_tp. Qed.

Lemma concrete_bw_pos : 0 < concrete_bw.
Proof. by rewrite /concrete_bw. Qed.

Definition concrete_platform : platform R :=
  {| pl_tp := concrete_tp;
     pl_bw := concrete_bw;
     pl_tp_pos := concrete_tp_pos;
     pl_bw_pos := concrete_bw_pos |}.

Theorem concrete_roofline_regime :
  ntt_intensity concrete_word_bytes <= ridge_point concrete_platform.
Proof.
rewrite /concrete_platform /ridge_point /concrete_bw /concrete_tp.
apply: ntt_roofline_regime => //.
by rewrite /concrete_word_bytes /concrete_bw /concrete_tp mul1r.
Qed.

Theorem concrete_ntt_memory_bound (k N : R) :
  0 < k -> 0 < N ->
  exists W : workload R,
    wl_ops W = ntt_ops k N /\
    wl_bytes W = ntt_bytes k N concrete_word_bytes /\
    exec_time concrete_platform W =
      ntt_bytes k N concrete_word_bytes / concrete_bw.
Proof.
move=> Hk HN.
pose W : workload R :=
  {| wl_ops := ntt_ops k N;
     wl_bytes := ntt_bytes k N concrete_word_bytes;
     wl_ops_pos := mulr_gt0 Hk HN;
     wl_bytes_pos := mulr_gt0 (mulr_gt0 Hk HN) concrete_word_bytes_pos |}.
exists W; split=> //; split=> //.
apply: roofline_cross.
have Hint : arith_intensity W = ntt_intensity concrete_word_bytes.
  rewrite /W /arith_intensity /ntt_intensity /= /ntt_ops /ntt_bytes.
  have Hkn : k * N != 0 by rewrite mulf_neq0 // gt_eqF.
  have Hw_ne : concrete_word_bytes != 0.
    apply/eqP => H0.
    move: concrete_word_bytes_pos.
    by rewrite H0 ltxx.
  rewrite -[k * N in X in X / _]mulr1.
  by rewrite -mulf_div divff ?mul1r ?div1r.
rewrite Hint.
exact: concrete_roofline_regime.
Qed.

End RooflineInstantiation.

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
(** * Composed NTT speedup from butterfly circuit                      *)
(* ================================================================== *)

Section ComposedNTT.

Variable R : realType.

Open Scope ring_scope.

(** Composed two-sided speedup: any hardware implementation of the
    NTT with span >= k satisfies T_sw/T_hw <= N and T_hw >= T_sw/N.
    The span bound k comes from [butterfly_depth]. *)
Theorem ntt_composed_speedup (k : nat) (N span work data P B : R) :
  0 < k%:R :> R ->
  0 < N ->
  k%:R <= span ->
  sw_time (ntt_ops k%:R N) / hw_time span work data P B <= N /\
  sw_time (ntt_ops k%:R N) / N <= hw_time span work data P B.
Proof. exact: theta_speedup. Qed.

(** Achievability: with T_hw = k (optimal butterfly schedule using
    P = N/2 processors), the speedup is exactly N. *)
Theorem ntt_achievable_speedup (k : nat) (N : R) :
  0 < k%:R :> R ->
  sw_time (ntt_ops k%:R N) / k%:R = N.
Proof. exact: optimal_hw_speedup. Qed.

End ComposedNTT.

Section AsapMachineAchievability.

Variable R : realType.
Variables (processors bandwidth : nat) (memory_hierarchy : seq nat).

Theorem ntt_asap_machine_optimal_speedup (k : nat) (N : R) :
  0 < k%:R :> R ->
  sw_time (ntt_ops k%:R N) /
    (machine_cycles (ntt_asap_machine processors bandwidth memory_hierarchy k))%:R = N.
Proof.
move=> Hk.
rewrite ntt_asap_machine_attains_span.
exact: optimal_hw_speedup.
Qed.

End AsapMachineAchievability.

(* ================================================================== *)
(** * Concrete 2^16 specializations plus toy N = 2 witness             *)
(* ================================================================== *)

Lemma concrete_span_bound (G : Type) :
  forall C : circuit (2 ^ 16) G, full_dependence C -> (16 <= circ_depth C)%N.
Proof. move=> C; exact: ntt_depth_irreducibility. Qed.

Lemma concrete_butterfly_depth (G : Type) (g0 : G) :
  circ_depth (butterfly_circuit g0 16) = 16.
Proof. exact: butterfly_depth. Qed.

Lemma concrete_butterfly_full_dep (G : Type) (g0 : G) :
  full_dependence (butterfly_circuit g0 16).
Proof. exact: butterfly_full_dep. Qed.

Section ConcreteSpeedup.

Variable R : realType.

Open Scope ring_scope.

Theorem concrete_speedup (span work data P B : R) :
  16%:R <= span ->
  sw_time (ntt_ops 16%:R (2 ^ 16)%:R) /
    hw_time span work data P B <= (2 ^ 16)%:R /\
  sw_time (ntt_ops 16%:R (2 ^ 16)%:R) /
    (2 ^ 16)%:R <= hw_time span work data P B.
Proof. by move=> Hspan; apply: theta_speedup. Qed.

Theorem concrete_achievable :
  sw_time (ntt_ops 16%:R (2 ^ 16)%:R) / 16%:R = (2 ^ 16)%:R :> R.
Proof. by apply: optimal_hw_speedup. Qed.

End ConcreteSpeedup.

Section ConcreteNegacyclicRoot.

Definition z5_ring := 'F_5.
Definition z5_omega : z5_ring := 2%:R.

Lemma z5_modulus_condition :
  (5 %% (2 * 2) = 1)%N.
Proof. by native_compute. Qed.

Lemma z5_omega_unit :
  z5_omega \is a GRing.unit.
Proof. by rewrite unitfE; apply/eqP; native_compute. Qed.

Lemma z5_omega_order :
  z5_omega ^+ 4 = (1 : z5_ring).
Proof. apply/val_inj. by native_compute. Qed.

Lemma z5_omega_half_turn :
  z5_omega ^+ 2 = (-1 : z5_ring).
Proof. apply/val_inj. by native_compute. Qed.

Lemma z5_omega_primitive (m : nat) :
  (0 < m)%N -> (m < 4)%N -> z5_omega ^+ m != (1 : z5_ring).
Proof.
move=> Hm0 Hm4.
case: m Hm0 Hm4 => [|m] //= _ Hm4.
case: m Hm4 => [|m] Hm4.
- by native_compute.
case: m Hm4 => [|m] Hm4.
- by native_compute.
case: m Hm4 => [|m] Hm4.
- by native_compute.
by [].
Qed.

Definition z5_negacyclic_root : negacyclic_root_data :=
  {| ngr_ring := z5_ring;
     ngr_exp := 1;
     ngr_omega := z5_omega;
     ngr_omega_unit := z5_omega_unit;
     ngr_order := z5_omega_order;
     ngr_half_turn := z5_omega_half_turn |}.

Lemma z5_shared_ntt_depth_bound :
  (1 <= circ_depth (ntt_shared_circuit 1))%N.
Proof. exact: negacyclic_shared_ntt_depth_bound z5_negacyclic_root. Qed.

Lemma z5_exact_shared_ntt_depth_bound :
  (1 <= circ_depth (exact_ntt_shared_circuit 1))%N.
Proof. exact: negacyclic_exact_shared_ntt_depth_bound z5_negacyclic_root. Qed.

Lemma z5_origin_annihilates_quotient :
  (@negacyclic_eval_point z5_negacyclic_root
      (negacyclic_origin_index z5_negacyclic_root)) ^+
      ngr_dim z5_negacyclic_root + 1 = 0 :> ngr_ring z5_negacyclic_root.
Proof.
exact: (@negacyclic_origin_point_annihilates_quotient z5_negacyclic_root).
Qed.

End ConcreteNegacyclicRoot.

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
Print Assumptions exact_ntt_shared_circuit_depth_bound.
Print Assumptions exact_negacyclic_operator_depth_bound.
Print Assumptions typed_bootstrapping_global_depth_lower_bound.
Print Assumptions bootstrapping_depth_bound.
Print Assumptions roofline_cross.
Print Assumptions speedup_le_N.
Print Assumptions hw_ge_sw_div_N.
Print Assumptions theta_speedup.
Print Assumptions concrete_span_bound.
Print Assumptions bfly_depth.
Print Assumptions bfly_reach_full.
Print Assumptions butterfly_full_dep.
Print Assumptions butterfly_depth.
Print Assumptions bfly_gate_size.
Print Assumptions butterfly_work.
Print Assumptions ntt_composed_speedup.
Print Assumptions ntt_achievable_speedup.
Print Assumptions ntt_asap_machine_optimal_speedup.
Print Assumptions concrete_butterfly_depth.
Print Assumptions concrete_butterfly_full_dep.
Print Assumptions concrete_speedup.
Print Assumptions concrete_achievable.
Print Assumptions z5_shared_ntt_depth_bound.
Print Assumptions z5_exact_shared_ntt_depth_bound.
Print Assumptions z5_origin_annihilates_quotient.

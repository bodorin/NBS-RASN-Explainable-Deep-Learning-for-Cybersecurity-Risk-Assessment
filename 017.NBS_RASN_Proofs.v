(** * NBS_RASN_Proofs.v

    Machine-checked proof certificates for the three supporting theorems of:

      "Neuro-Bayesian-Symbolic Residual Attention Shallow Network:
       Explainable Deep Learning for Cybersecurity Risk Assessment"
       Revised manuscript 017 — IJCCC final submission - 16 Nov 2026

    Authors of the article:
      Nicolaie Popescu-Bodorin  (Ovidius University, Constanta; Maritime University, Constanta, Spiru Haret University, Bucharest)
      Madeleine Togher           (HCT, Sharjah, UAE)

    Proof assistant: Coq 8.17 / Rocq Prover
    Compile with:   coqc NBS_RASN_Proofs.v

    Theorems certified (Appendix A of manuscript 017):
      Theorem A.1  Axiom-Induced Falsifiability
      Theorem A.2  Complete Transparency (Score Decomposition Uniqueness)
      Theorem A.3  Input-Output Type Safety

    Design note:
      The NBS-RASN is an abstract architecture parameterised by concrete
      neuron identifiers, activation functions, and layer contribution
      values.  Those domain-specific constants are introduced with
      [Parameter] and [Axiom] declarations so the mathematical structure
      of the proofs remains independent of any particular implementation.
      Theorems A.1-A.3 are proved WITHOUT [Admitted]; every leaf is
      either [reflexivity], [discriminate], [lra], or an application of
      a named lemma.
*)

(* ================================================================== *)
(*  Imports                                                            *)
(* ================================================================== *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Decidable.

Open Scope R_scope.
Import ListNotations.

(* ================================================================== *)
(*  Part I.  Abstract architecture types                               *)
(* ================================================================== *)

(** *** 1.1  Layer indices

    The NBS-RASN has exactly 12 layers, labelled L0 through L11.
    LayerIndex is a simple inductive type with decidable equality. *)

Inductive LayerIndex : Type :=
  | L0  | L1  | L2  | L3
  | L4  | L5  | L6  | L7
  | L8  | L9  | L10 | L11.

Lemma LayerIndex_eq_dec :
  forall (a b : LayerIndex), {a = b} + {a <> b}.
Proof. decide equality. Qed.

(** The canonical ordered list of all 12 layer indices. *)
Definition all_layers : list LayerIndex :=
  [L0; L1; L2; L3; L4; L5; L6; L7; L8; L9; L10; L11].

Lemma all_layers_length : length all_layers = 12.
Proof. reflexivity. Qed.

(** *** 1.2  Neuron identifiers *)

Parameter NeuronId : Type.
Parameter NeuronId_eq_dec : forall (n m : NeuronId), {n = m} + {n <> m}.

(** *** 1.3  Activation functions *)

Parameter ActivationFn  : Type.
Parameter default_act   : ActivationFn.   (* used when constructing witnesses *)

(** *** 1.4  Domain types for cybersecurity risk assessment *)

(** Structural project feature vector (CVE / CVSS attributes). *)
Parameter InputFeature : Type.

(** *** 1.5  Network record  G = (V, E, A, F)

    V  =  neurons   : list of neuron identifiers
    E  =  edges     : list of directed connections
    A  =  activation: neuron -> activation function
    F  =  layer_of  : neuron -> layer index            *)

Record Network : Type := mkNetwork {
  neurons    : list NeuronId;
  edges      : list (NeuronId * NeuronId);
  activation : NeuronId -> ActivationFn;
  layer_of   : NeuronId -> LayerIndex
}.

(** Boolean classifiers for the two neuron roles. *)
Parameter is_data_neuron    : NeuronId -> bool.
Parameter is_control_neuron : NeuronId -> bool.

(** Axiom (architecture invariant): the two roles are disjoint. *)
Axiom data_control_disjoint :
  forall n : NeuronId,
    is_data_neuron n = true -> is_control_neuron n = false.

(* ================================================================== *)
(*  Part II.  Boolean formulation of the two structural axioms        *)
(* ================================================================== *)

(** *** 2.1  Gatekeeper Constraint (GK)

    Every edge (u, v) where u is a data neuron and v is a control
    neuron must have layer_of u = L0.

    Equivalently: data→control edges are only permitted from L0. *)

Definition check_gk_edge (net : Network) (e : NeuronId * NeuronId) : bool :=
  let u := fst e in
  let v := snd e in
  if andb (is_data_neuron u) (is_control_neuron v)
  then match LayerIndex_eq_dec (layer_of net u) L0 with
       | left  _ => true
       | right _ => false
       end
  else true.

Definition gk_valid (net : Network) : bool :=
  forallb (check_gk_edge net) (edges net).

(** *** 2.2  Data-Control Separation (DCS)

    No direct edge from a control neuron to a data neuron exists.
    This prevents control flow from contaminating data flow. *)

Definition check_dcs_edge (e : NeuronId * NeuronId) : bool :=
  negb (andb (is_control_neuron (fst e)) (is_data_neuron (snd e))).

Definition dcs_valid (net : Network) : bool :=
  forallb check_dcs_edge (edges net).

(** *** 2.3  Combined structural validity *)

Definition sv_bool (net : Network) : bool :=
  andb (gk_valid net) (dcs_valid net).

(* ================================================================== *)
(*  THEOREM A.1 — Axiom-Induced Falsifiability                        *)
(* ================================================================== *)

(**  Paper statement (Appendix A, Theorem A.1):

       The NBS-RASN model is falsifiable with respect to its structural
       axioms (GK and DCS) in the sense of Popper (1959): for each
       axiom there exists a concrete network configuration that violates
       it, the violation is decidable by finite structural inspection,
       and predictions conditioned on the axioms are therefore
       empirically testable.

     Formal decomposition:
       (a) sv_bool is a computable decision procedure for structural
           validity (Lemma A1_sv_decidable).
       (b) A concrete GK-violating network exists and can be
           verified by computation (Lemma A1_gk_witness_violates).
       (c) A concrete DCS-violating network exists and can be
           verified by computation (Lemma A1_dcs_witness_violates).
       (d) Neither axiom is vacuously true
           (Theorem A1_axiom_induced_falsifiability).
*)

(** (a) Structural validity is a decidable boolean predicate. *)
Lemma A1_sv_decidable :
  forall net : Network,
    {sv_bool net = true} + {sv_bool net = false}.
Proof.
  intro net.
  destruct (sv_bool net); [left | right]; reflexivity.
Qed.

(** (b) Witness for GK violation.

    We introduce two parameter neurons and axiomatise their roles.
    The witness network places n_d in layer L1 (not L0) but includes
    a direct edge n_d -> n_c, violating the gatekeeper constraint. *)

Parameter n_d : NeuronId.      (* a data neuron    *)
Parameter n_c : NeuronId.      (* a control neuron *)
Axiom n_d_is_data    : is_data_neuron    n_d = true.
Axiom n_c_is_control : is_control_neuron n_c = true.

Definition gk_witness : Network := mkNetwork
  [n_d; n_c]
  [(n_d, n_c)]
  (fun _ => default_act)
  (fun n => if NeuronId_eq_dec n n_d then L1 else L0).
  (* n_d is in L1, not L0 — the GK constraint is violated *)

Lemma A1_gk_witness_violates :
  gk_valid gk_witness = false.
Proof.
  unfold gk_valid, gk_witness, edges. simpl.
  rewrite andb_true_r.               (* forallb on a singleton *)
  unfold check_gk_edge. simpl.
  rewrite n_d_is_data, n_c_is_control. simpl.
  destruct (NeuronId_eq_dec n_d n_d) as [_ | Hne].
  - (* layer_of gk_witness n_d  =  L1  (not L0) *)
    destruct (LayerIndex_eq_dec L1 L0) as [Heq | _].
    + discriminate Heq.      (* L1 ≠ L0: contradiction *)
    + reflexivity.           (* right branch of match returns false *)
  - exfalso. apply Hne. reflexivity.
Qed.

(** (c) Witness for DCS violation.

    n_c -> n_d is a direct control-to-data edge, violating DCS. *)

Definition dcs_witness : Network := mkNetwork
  [n_d; n_c]
  [(n_c, n_d)]
  (fun _ => default_act)
  (fun _ => L0).

Lemma A1_dcs_witness_violates :
  dcs_valid dcs_witness = false.
Proof.
  unfold dcs_valid, dcs_witness, edges. simpl.
  rewrite andb_true_r.
  unfold check_dcs_edge. simpl.
  rewrite n_c_is_control, n_d_is_data. simpl.
  reflexivity.
Qed.

(** (d) Theorem A.1: Both axioms are non-vacuous and have
    concrete, decidable falsifiers. *)
Theorem A1_axiom_induced_falsifiability :
  (* Structural validity is decidable ... *)
  (forall net : Network, {sv_bool net = true} + {sv_bool net = false})
  /\
  (* ... and each axiom is violated by a witness network. *)
  (exists net : Network, gk_valid  net = false) /\
  (exists net : Network, dcs_valid net = false).
Proof.
  split.
  - apply A1_sv_decidable.
  - split.
    + exists gk_witness.  apply A1_gk_witness_violates.
    + exists dcs_witness. apply A1_dcs_witness_violates.
Qed.

(* ================================================================== *)
(*  THEOREM A.2 — Complete Transparency (Score Decomposition)         *)
(* ================================================================== *)

(**  Paper statement (Appendix A, Theorem A.2):

       For any input x, the total risk score S(x) equals the sum of
       12 independently computable per-layer contributions
         s_{L0}(x), ..., s_{L11}(x).
       This decomposition is unique: each s_l(x) is determined by l
       and x, and S(x) = s_{L0}(x) + ... + s_{L11}(x).

     Formal decomposition:
       (i)  Existence: total_score = fold_left sum of layer_contribution
            over all_layers (Theorem A2_decomposition_exists).
       (ii) Uniqueness: if two contribution functions produce the same
            individual outputs for all layers and inputs, the sums are
            equal (Theorem A2_decomposition_unique).
       (iii) Cardinality: the decomposition always has exactly 12 terms
            (Lemma A2_decomposition_12_terms).
*)

(** The per-layer contribution: each layer l contributes a real-valued
    score given the input x. *)
Parameter layer_contribution : LayerIndex -> InputFeature -> R.

(** The total risk score is the sum of all 12 layer contributions. *)
Definition total_score (x : InputFeature) : R :=
  fold_left Rplus
    (map (fun l => layer_contribution l x) all_layers)
    0.

(** Convenience: sum of a list of reals. *)
Definition sum_list (rs : list R) : R :=
  fold_left Rplus rs 0.

(** Auxiliary: fold_left Rplus is extensional over the list elements. *)
Lemma fold_Rplus_map_ext :
  forall {A : Type} (f g : A -> R) (l : list A),
    (forall a, In a l -> f a = g a) ->
    fold_left Rplus (map f l) 0 =
    fold_left Rplus (map g l) 0.
Proof.
  intros A f g l Hext.
  f_equal.
  apply map_ext_in.
  exact Hext.
Qed.

(** (i) Existence of the decomposition. *)
Theorem A2_decomposition_exists :
  forall (x : InputFeature),
    total_score x =
    sum_list (map (fun l => layer_contribution l x) all_layers).
Proof.
  intro x. unfold total_score, sum_list. reflexivity.
Qed.

(** (ii) Uniqueness: if two contribution functions agree on every layer
    for every input, their sums agree too. *)
Theorem A2_decomposition_unique :
  forall (f g : LayerIndex -> InputFeature -> R),
    (forall l x, f l x = g l x) ->
    forall x,
      sum_list (map (fun l => f l x) all_layers) =
      sum_list (map (fun l => g l x) all_layers).
Proof.
  intros f g Hfg x.
  unfold sum_list.
  apply fold_Rplus_map_ext.
  intros l _. apply Hfg.
Qed.

(** Corollary: the total score is uniquely determined by
    layer_contribution, all_layers, and the input. *)
Corollary A2_total_score_unique :
  forall (f g : LayerIndex -> InputFeature -> R),
    (forall l x, f l x = g l x) ->
    forall x,
      fold_left Rplus (map (fun l => f l x) all_layers) 0 =
      fold_left Rplus (map (fun l => g l x) all_layers) 0.
Proof.
  intros f g Hfg x.
  exact (A2_decomposition_unique f g Hfg x).
Qed.

(** (iii) The decomposition has exactly 12 terms — one per layer. *)
Lemma A2_decomposition_12_terms :
  forall (x : InputFeature),
    length (map (fun l => layer_contribution l x) all_layers) = 12.
Proof.
  intro x. rewrite map_length. apply all_layers_length.
Qed.

(* ================================================================== *)
(*  THEOREM A.3 — Input-Output Type Safety                            *)
(* ================================================================== *)

(**  Paper statement (Appendix A, Theorem A.3):

       For any well-formed input (structural feature vector satisfying
       the CVSS score constraints), every intermediate layer output
       and the final risk score satisfy the well-typedness predicate
         WellTypedScore s  :=  0 ≤ s ≤ 1.

     Formal decomposition:
       (i)  WellTypedScore is defined as a Prop over R.
       (ii) Each layer transformation preserves WellTypedScore
            (Axiom layer_preserves_wts — the architecture invariant).
       (iii) By induction over any list of layers, the sequential
             forward pass preserves WellTypedScore
             (Lemma A3_process_layers_preserves_wts).
       (iv) Main theorem: forward_pass preserves WellTypedScore
            (Theorem A3_input_output_type_safety).
       (v)  Corollary: intermediate type safety holds for every
            prefix of layers (Corollary A3_prefix_type_safety).
*)

(** Type predicate: a risk score is well-typed iff it is in [0, 1]. *)
Definition WellTypedScore (s : R) : Prop := 0 <= s /\ s <= 1.

(** Each layer is a score transformer: LayerIndex -> R -> R.
    For example, the gatekeeper layer (L0) applies a sigmoid gate. *)
Parameter apply_layer : LayerIndex -> R -> R.

(** Architecture invariant (Axiom): every layer transformation is
    monotone with respect to WellTypedScore.
    Proof obligation discharged by the specific activation functions
    in the NBS-RASN implementation (all outputs clipped or gated to
    [0, 1] by design). *)
Axiom layer_preserves_wts :
  forall (l : LayerIndex) (s : R),
    WellTypedScore s -> WellTypedScore (apply_layer l s).

(** The sequential forward pass: apply layers in order L0 .. L11. *)
Definition forward_pass (s0 : R) : R :=
  fold_left (fun acc l => apply_layer l acc) all_layers s0.

(** *** Key lemma: processing any list of layers preserves
    WellTypedScore.  Proved by list induction; uses only
    layer_preserves_wts and the induction hypothesis. *)
Lemma A3_process_layers_preserves_wts :
  forall (ls : list LayerIndex) (s : R),
    WellTypedScore s ->
    WellTypedScore
      (fold_left (fun acc l => apply_layer l acc) ls s).
Proof.
  induction ls as [| l ls' IH].
  - (* Base case: empty list — no transformation applied. *)
    intros s Hs. simpl. exact Hs.
  - (* Inductive step: apply layer l, then the remaining layers ls'. *)
    intros s Hs. simpl.
    apply IH.
    apply layer_preserves_wts.
    exact Hs.
Qed.

(** *** Theorem A.3: forward_pass preserves WellTypedScore. *)
Theorem A3_input_output_type_safety :
  forall s0 : R,
    WellTypedScore s0 ->
    WellTypedScore (forward_pass s0).
Proof.
  intros s0 Hs0.
  unfold forward_pass.
  apply A3_process_layers_preserves_wts.
  exact Hs0.
Qed.

(** Corollary: if the initial accumulator is 0 (a natural choice
    for a zero-initialised score), the output is well-typed. *)
Corollary A3_zero_initial_well_typed :
  WellTypedScore (forward_pass 0).
Proof.
  apply A3_input_output_type_safety.
  unfold WellTypedScore.
  split; lra.
Qed.

(** Corollary: type safety holds at every intermediate layer.
    After processing any k layers (k ≤ 12), the running score
    is still in [0, 1]. *)
Corollary A3_prefix_type_safety :
  forall (k : nat) (s0 : R),
    WellTypedScore s0 ->
    WellTypedScore
      (fold_left (fun acc l => apply_layer l acc)
                 (firstn k all_layers) s0).
Proof.
  intros k s0 Hs0.
  apply A3_process_layers_preserves_wts.
  exact Hs0.
Qed.

(* ================================================================== *)
(*  Part IV.  Structural invariants about all_layers                  *)
(* ================================================================== *)

(** Every layer index appears exactly once in all_layers.
    This guarantees the score decomposition in Theorem A.2 has
    no duplicated or missing terms. *)

Lemma all_layers_NoDup : NoDup all_layers.
Proof.
  unfold all_layers.
  repeat (apply NoDup_cons;
          [ intro H; simpl in H;
            repeat (destruct H as [H | H];
                    [ discriminate H | ]);
            exact H
          | ]).
  apply NoDup_nil.
Qed.

(** L0 is the first element of all_layers (the gatekeeper layer). *)
Lemma all_layers_head : hd_error all_layers = Some L0.
Proof. reflexivity. Qed.

(** L11 is the last element of all_layers (the output layer). *)
Lemma all_layers_last : last all_layers L0 = L11.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  Summary of certified results                                       *)
(* ================================================================== *)

(**  The certificates above establish the following without [Admitted]:

     [A1_axiom_induced_falsifiability]
       Both the Gatekeeper Constraint and the DCS property are
       computable boolean predicates; each is violated by an
       explicit, concrete witness network.  The axioms are
       therefore falsifiable in Popper's sense (1959).

     [A2_decomposition_exists]  +  [A2_decomposition_unique]
       The total risk score is the fold-left Rplus sum of exactly
       12 per-layer contributions over all_layers (existence),
       and that decomposition is unique given the contribution
       function (uniqueness by functional determinism).

     [A3_input_output_type_safety]
       If the initial score is well-typed (in [0,1]), then after
       processing all 12 layers the output score is well-typed.
       Type safety holds for every layer prefix as well
       (Corollary A3_prefix_type_safety).

     Structural invariants:
       all_layers contains exactly 12 entries (all_layers_length),
       with no duplicates (all_layers_NoDup), starting with the
       gatekeeper layer L0 (all_layers_head) and ending with the
       output layer L11 (all_layers_last).

     Open obligations discharged by axioms (not by proofs here):
       - data_control_disjoint : roles are disjoint by architecture
       - layer_preserves_wts   : each activation clips to [0,1]
       - n_d_is_data, n_c_is_control : witness neuron roles

     These axioms are justified in the manuscript body:
       data_control_disjoint  §3.1 Definition 2 (Gatekeeper Constraint)
       layer_preserves_wts    §4.2 Definition 4 (Deep Learning Characteristics)
       witness axioms         §3.1 Definition 1 (NBS-RASN graph G)
*)

(* ================================================================== *)
(*  End of NBS_RASN_Proofs.v                                           *)
(* ================================================================== *)

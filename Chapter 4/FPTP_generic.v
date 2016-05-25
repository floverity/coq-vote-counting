Require Import Notations.
Require Import Logic.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Wf.
Require Import Wf_nat.
Import ListNotations.

(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Section genericTermination.

(* generic notion of a judgement *)
Variable Judgement : Type.
Variable final: Judgement -> Prop.
Hypothesis final_dec: forall j : Judgement, (final j) + (not (final j)).

(* generic well-founded relation on a type *)
Variable WFO : Type.
Variable wfo: WFO -> WFO -> Prop.
Hypothesis wfo_wf: well_founded wfo.

(* the `measure' function *)
Variable m: { j: Judgement | not (final j) } -> WFO.

(* 'make non-final judgement' - pairs a judgement with evidence that it is non-final *)
Definition mk_nfj: forall j: Judgement, forall e: not (final j), { j : Judgement | not (final j) }.
  intros j e. exists j. assumption.
Defined.

(* generic rule - a relation on two judgements *)
Definition Rule := Judgement -> Judgement -> Prop.

(* property 1: the measure always decreases  *)
Definition dec (Rules : list Rule) : Type :=
  forall r, In r Rules -> 
  forall p c : Judgement, r p c ->
  forall ep : not (final p),
  forall ec : not (final c),
  wfo (m (mk_nfj c ec )) (m (mk_nfj p ep)).

(* property 2: for every non-final judgement, there is a rule which may be applied *)
Definition app (Rules : list Rule) : Type := 
  forall p : Judgement, not (final  p) ->
  existsT r, existsT c, (In r Rules * r p c).

(* the type of proofs *)
Inductive Pf (a : Judgement) (Rules : list Rule) : Judgement -> Type := 
  ax : forall j : Judgement, j = a -> Pf a Rules j
  | mkp: forall c : Judgement, 
  forall r : Rule, In r Rules -> 
  forall b : Judgement, r b c ->
  Pf a Rules b ->
  Pf a Rules c.

(* lemma specifying when and how a proof may be 'extended' *)
Lemma extend: 
  forall Rules : list Rule, 
  dec Rules ->
  app Rules ->
  forall a b : Judgement, 
  forall eb: not (final b),
  Pf a Rules b ->
  existsT c : Judgement, 
    (Pf a Rules c) *
    (forall ec: not (final c), wfo (m (mk_nfj c ec)) (m (mk_nfj b eb))).
Proof.
  intros Rules Hdec Happ a b eb Pab.
  unfold dec in Hdec.
  unfold app in Happ. 
  specialize Happ with b.
  destruct Happ as [r Happ]. assumption.
  destruct Happ as [c [Happ1 Happ2]].
  specialize (Hdec r Happ1 b c Happ2). 
  exists c.
  split.
  apply (mkp a Rules c r Happ1 b Happ2 Pab).
  intro ec.
  specialize (Hdec eb ec).
  assumption.
Defined.

(* auxiliary termination theorem *)
Theorem termination_aux : forall Rules : list Rule, 
  dec Rules ->
  app Rules ->
  forall n: WFO,
  forall a b : Judgement, 
  forall eb:  not (final b),
  m (mk_nfj b eb) = n ->
  Pf a Rules b ->  
  (existsT c : Judgement, final c * Pf a Rules c).
Proof.
  intros Rules Hdec Happ n.
  induction n as [w IH] using (well_founded_induction_type wfo_wf).
  intros a b eb Hmb Hab.
  assert (Hex : existsT c : Judgement, 
    (Pf a Rules c) *
    (forall ec: not (final c), wfo (m (mk_nfj c ec)) (m (mk_nfj b eb)))).
  apply (extend Rules Hdec Happ a b eb Hab).
  destruct Hex as [c [Hex1 Hex2]].
  destruct (final_dec c) as [f | nf].
  (* c is final *)
  exists c. split. assumption. assumption.
  (* c is non-final *)
  specialize (Hex2 nf).
  rewrite <- Hmb in IH. 
  destruct (IH (m (mk_nfj c nf)) Hex2 a c nf) as [j Hj].
  reflexivity.
  assumption.
  exists j.
  assumption.
Defined.  

(* the main theorem *)
Corollary termination:  forall Rules : list Rule, 
  dec Rules ->
  app Rules ->
  forall a : Judgement, 
  (existsT c : Judgement, final c * Pf a Rules c).
Proof. 
  intros Rules Hdec Happ a. 
  destruct (final_dec a) as [f | ea].
  exists a. 
  split.
  assumption.
  apply (ax a).
  reflexivity.    
  apply (termination_aux Rules Hdec Happ (m (mk_nfj a ea)) a a ea).
  reflexivity.
  apply (ax a).
  reflexivity.  
Defined. 

End genericTermination.

Section FPTP. 

Variable cand : Type.
Variable cand_all : list cand.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Hypothesis cand_inh : cand.

(*** specialising the framework ***)

(* intermediate and final states of counting *)
Inductive FPTP_Judgement : Type  :=
  state : (list cand) * (cand -> nat) -> FPTP_Judgement 
 | winner : cand -> FPTP_Judgement.

Definition FPTP_final (a : FPTP_Judgement) : Prop :=
  exists c, a = winner c.

Lemma final_dec: forall j : FPTP_Judgement, (FPTP_final j) + (~ FPTP_final j).
Proof. 
  intro j. destruct j. 
  right.
  unfold FPTP_final.
  unfold not. intro H. 
  destruct H.
  discriminate. 
  left.
  unfold FPTP_final.
  exists c.
  reflexivity.
Defined.

(* well-founded order *)
Definition FPTP_WFO : Type := nat. 
Definition FPTP_wfo: FPTP_WFO -> FPTP_WFO -> Prop := lt.
Lemma  FPTP_wfo_wf: well_founded FPTP_wfo.
Proof. 
  unfold FPTP_wfo.
  apply lt_wf.
Qed.

(* measure function *)
Definition FPTP_m : { j: FPTP_Judgement | not (FPTP_final j) } -> nat.
  intro H. destruct H as [j ej].
  destruct j as [nfj | fj].
  destruct nfj as [u t].
  exact (length u). 
  contradiction ej.  
  unfold FPTP_final. 
  exists fj. 
  reflexivity. 
Defined. 

Definition FPTP_Rule := FPTP_Judgement -> FPTP_Judgement -> Prop.

(* the new tally is the old tally with c's votes incremented by one *)
Definition inc (c:cand) (t: cand -> nat) (nt: cand -> nat) : Prop :=
  (nt c = t c + 1)%nat /\  forall d, d <> c -> nt d = t d.

(* increment tally for cand by one *)
Definition inct (c:cand) (t: cand -> nat) : cand -> nat :=
  fun d => if (cand_eq_dec c d) then (S (t d)) else (t d).

(* Rule 1: if there is an uncounted vote for c, then increment 
 c's tally by one and update the list of uncounted votes*)
Definition count (p: FPTP_Judgement) (c: FPTP_Judgement) : Prop :=
  exists u1 t1 u2 t2, 
  p = state (u1, t1) /\
  (exists l1 c l2, u1 = l1 ++ [c] ++ l2 /\ u2 = l1 ++ l2 /\ inc c t1 t2) /\
  c = state (u2, t2).

(* Rule 2: If all votes have been counted and all cands have 
 fewer votes than c, then c may be declared the winner *)
Definition declare (p: FPTP_Judgement) (c: FPTP_Judgement) : Prop :=
  exists u t d, 
  p = state (u, t) /\
  u = [] /\
  (forall e : cand, t e <= t d) /\
  c = winner d.

(* list of rules for FPTP *)
Definition FPTPR : list FPTP_Rule := [ count; declare ]. 


(*** proving the two properties ***)

(* proof that the FPTP rules satisfy the `decreasing' property *)
Lemma dec_FPTPR : dec FPTP_Judgement FPTP_final FPTP_WFO FPTP_wfo FPTP_m FPTPR. 
Proof. 
  unfold dec. 
  intros r Hin p c Hr ep ec. 
  destruct Hin.
   (* 'count' rule *)
  rewrite <- H in Hr.
  destruct p as [[u1 t1]|]. destruct c as [[u2 t2]|].
    (* nonfinal premise, nonfinal conclusion *)  
    unfold count in Hr.
  unfold FPTP_wfo.
  unfold FPTP_m. simpl.
  destruct Hr as [u [t [nu [nt [Heq1 [Hr Heq2]]]]]].
  inversion Heq1. inversion Heq2.
  destruct Hr as [l1 [c [l2 [Hr1 [Hr2 Hr3]]]]]. 
  subst. 
  rewrite -> (app_length l1 l2).
  rewrite <- (app_ass l1 [c] l2).
  rewrite -> (app_length (l1 ++ [c]) l2). 
  rewrite -> (app_length l1 [c]).
  simpl. omega.
    (* nonfinal premise, final conclusion *)
  unfold count in Hr.
  contradict ec. unfold FPTP_final. exists c. reflexivity. 
    (* final premise *)
  unfold count in Hr. 
  contradict ep. unfold FPTP_final. exists c0. reflexivity. 
  (* 'declare' rule *)
  destruct H. 
  rewrite <- H in Hr.
  destruct p as [[u1 t1]|]. destruct c as [[u2 t2]|].
    (*nonfinal premise, nonfinal conclusion *)
  unfold declare in Hr.
  destruct Hr as [u [t [d [Hr1 [Hr2 [Hr3 Hr4]]]]]].  discriminate.
    (* nonfinal premise, final conclusion *)
  unfold FPTP_final in ec. contradiction ec.
  exists c. reflexivity.
    (* final premise *)
  unfold FPTP_final in ep. contradiction ep.
  exists c0. reflexivity.
  destruct H. 
Defined.

(* proof that the FPTP rules satisfy the `rule applicable' property *)
(* nonempty lists have a minimal element wrt a nat-valued measure *)
Lemma list_max : forall A:Type, forall l: list A, forall f: A -> nat,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->f b <= f m))).
Proof.
  intros A l f.
  induction l as [| l0 ls IHls].
  (* l = [] *)
  left. trivial.
  (* l = l0::ls *)
  right. destruct IHls as [lsemp | lsnemp ].
  (* case ls = [] *)
  exists l0. split. apply (in_eq l0 ls).
  intros b H.
  assert (H0: l0 = b \/ In b ls) by apply (in_inv H).
  destruct H0 as [ eq | ctd].
  replace l0 with b. trivial.
  replace ls with ([]: list A) in ctd. contradict ctd.
  (* case ls <> [] *)
  destruct lsnemp as [maxls Hmax ]. destruct Hmax as [Hmaxin Hmaxgeq].
  assert (H: {f maxls <= (f l0)}  + {(f l0) <= (f maxls)}) by apply (le_ge_dec (f maxls) (f l0)).
  destruct H as [Hl0 | Hmaxls].
  (* l0 is maxium *)
  exists l0. split. apply (in_eq l0 ls). intros b Hin.
  assert (H: l0 = b \/ In b ls) by apply (in_inv Hin).
  destruct H as [Heq | Hls ]. replace l0 with b. trivial.
  transitivity (f maxls). apply (Hmaxgeq b Hls). assumption.
  (* maxls is maximum *)
  exists maxls. split.
  apply (in_cons l0 maxls ls Hmaxin).
  intros b Hin.
  assert (H: l0 = b \/ In b ls) by apply (in_inv Hin). destruct H as [Heq | Htl].
  replace b with l0. assumption. apply (Hmaxgeq b Htl).
Defined.

Lemma list_cand_max: forall f: cand -> nat, existsT m:cand, forall b: cand, f b <= f m.
Proof.
  intros f. specialize (list_max cand cand_all f).
  intro H. destruct H as [Hemp | Hnemp].
  contradict cand_inh. intro c. specialize (cand_finite c).
  replace cand_all with ([]: list cand) in cand_finite. auto.
  destruct Hnemp as [max H]. destruct H as [Hin Hmax].
  exists max. intro b. apply (Hmax b). apply (cand_finite b).
Defined.

Lemma app_FPTPR : app FPTP_Judgement FPTP_final FPTPR.
Proof. 
  unfold app.
  intros p Hnf.
  destruct p as [[u t] | fj].
  destruct u.
  (* case : u = [] *)
  (* 'declare' can be applied *)
  exists declare.
  assert (Hmax : existsT m:cand, forall b: cand, t b <= t m).
  apply list_cand_max.
  destruct Hmax as [m Hmax]. 
  exists (winner m).
  split.
  unfold FPTPR. intuition.
  unfold declare.
  exists []. exists t. exists m.  
  split. trivial. split. trivial. split. assumption. trivial. 
  (* case : there are uncounted votes *)
  (* 'count' can be applied *)
  exists count.
  exists (state (u, inct c t)).
  split.
  unfold FPTPR. intuition.
  unfold count.
  exists (c :: u). exists t. exists u. exists (inct c t). 
  split. reflexivity.
  split. 
  exists []. exists c. exists u.  
  intuition.
  unfold inc. split.  
  unfold inct. 
  destruct cand_eq_dec.
  intuition. intuition. intuition. 
  unfold inct. 
  destruct cand_eq_dec. 
  symmetry in e. 
  contradiction. 
  reflexivity. reflexivity. 
  (* j is final *)
  unfold FPTP_final in Hnf.
  contradiction Hnf.
  exists fj.
  reflexivity.   
Defined. 

End FPTP.

Section candidates.

(* our candidates given as inductive type and list. *)
Inductive cand := Alice | Bob | Claire | Darren.
Definition cand_all := [Alice; Bob; Claire; Darren].

(* everything below here is independent of the definition of cand *)
(* as long as cand is an inductive type with nullary constructors *)
(* only and all_cands mentions all of them.                       *)

Lemma cand_finite: forall c, In c cand_all.
Proof.
  unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
Qed.

Lemma  cand_eq_dec : forall c d : cand, {c = d} + {c <> d}.
Proof.
  intros a b;
  repeat induction a;
    repeat (induction b) || (right; discriminate) ||(left; trivial).
Defined.

Lemma cand_inh : cand.
Proof.
  constructor.
Defined.

End candidates.

Print FPTP_Judgement.

Definition FPTP_termination :=
  termination (FPTP_Judgement cand) (FPTP_final cand) (final_dec cand) 
  FPTP_WFO FPTP_wfo FPTP_wfo_wf (FPTP_m cand) (FPTPR cand) (dec_FPTPR cand) 
  (app_FPTPR cand cand_all cand_finite cand_eq_dec cand_inh).

Extraction Implicit mkp [b].
Extraction Language Haskell.
Extraction "FPTPCode.hs"  FPTP_termination.


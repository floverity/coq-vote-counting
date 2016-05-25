Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.NatInt.NZMul.
Require Import Coq.Structures.OrdersFacts.
Require Import Wf.
Require Import Lexicographic_Product.
Require Import Inverse_Image. 
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
Section STV. 

(* lists with pairwise distinct candidates *)
Inductive PD  {A: Type} : list A -> Prop :=
   PDe :  PD  ( nil)
 | PDc :  forall a:A,forall l: list A, PD l /\ ~(In a l) -> (PD  (cons a l)).

Variable cand: Type.
Variable cand_all: list cand.
Hypothesis cand_pd: PD cand_all.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.

(* a ballot is a list of candidates *)
Definition ballot := list cand.
Check ballot. 

Variable bt : list ballot. 
Variable qu : nat. 
Variable s : nat. 

(* intermediate and final states in vote counting *)
Inductive STV_Judgement :=
   state:                     (** intermediate states **)
       list ballot            (* uncounted votes *)
     * (cand -> list ballot)  (* assignment of counted votes to first pref candidate *)
     * { tally : (cand -> nat) | forall c, tally c <= qu }          (* tally *)
     * (list cand)            (* hopeful cands still in the running *)
     * { elected: list cand | length  elected <= s}           (* elected cands no longer in the running *)
     -> STV_Judgement
  | winners:                  (** final state **)
    list cand -> STV_Judgement.        (* election winners *)

Definition STV_final (a : STV_Judgement) : Prop :=
   exists w, a = winners w. 

Lemma final_dec: forall j : STV_Judgement, (STV_final j) + (not (STV_final j)).
Proof. 
  intro j. destruct j. 
  right.
  unfold STV_final.
  unfold not. intro H. 
  destruct H.
  discriminate. 
  left.
  unfold STV_final.
  exists l.
  reflexivity.
Defined.

(* Rules *)
Definition STV_Rule := STV_Judgement -> STV_Judgement -> Prop.

(* the new tally is the old tally with c's votes incremented by one *)
Definition inc (c:cand) (t: cand -> nat) (nt: cand -> nat) : Prop :=
  (nt c = t c + 1)%nat /\  forall d, d <> c -> nt d = t d.

(* the new assignment is the old assignment with ballot b added for candidate c *)
Definition add (c:cand) (b:ballot) (a: cand -> list ballot) (na: cand -> list ballot) : Prop :=
  na c = b::(a c) /\  forall d, d <> c -> na d = a d.

(* l and nl are equal except that nl additionally contaeqe x *)
Definition eqe {A: Type} (x:A) (l: list A) (nl: list A) : Prop :=
  exists l1 l2: list A, l = l1 ++ l2 /\ nl = l1 ++ [x] ++ l2.

(* l contains x and replacing x with y in l yields nl *)
Definition rep {A:Type} (x y: A) (l nl: list A) :=
  exists l1 l2: list A, l = l1 ++ [x] ++ l2 /\ nl = l1 ++ [y] ++ l2.

(* remove one occurrence of a candidate from a list *)
Fixpoint remc (c: cand) (l: list cand) :=
  match l with 
    nil => nil
  | cons l0 ls => if (cand_eq_dec c l0) then ls else cons l0 (remc c ls)
  end.

Lemma remc_ok : forall c:cand, forall l:list cand, In c l -> eqe c (remc c l) l.
Proof.
  intros c l. induction l as [| l0 ls IHls].
  intro i. contradict i.
  intro i.
  assert (H: {l0=c} + {l0<>c}) by apply (cand_eq_dec l0 c).
  destruct H as [l0eqc | l0neqc ].
  replace (remc c (l0::ls)) with ls.
  unfold eqe. 
  exists ([]: list cand). exists ls. split.
  auto. replace c with l0. auto.
  replace c with l0. unfold remc. destruct (cand_eq_dec l0 l0). trivial.
  contradict n. trivial.
  (* we must have that In c ls *)
  assert (Hin: l0 = c \/ In c ls) by apply (in_inv i).
  destruct Hin as [l0eqc | Hin ]. 
  contradict l0neqc. assumption.
  (* apply IH *)
  assert (eqe c (remc c ls) ls) by apply (IHls Hin).
  unfold eqe in H.
  replace (remc c (l0::ls)) with (l0::(remc c ls)).
  destruct H as [l1 H]. destruct H as [l2 H]. destruct H as [lft rgt].
  unfold eqe.
  exists (l0::l1). exists l2.
  split.
  transitivity (l0::(l1++l2)). congruence. auto.
  transitivity (l0::(l1 ++ [c] ++ l2)). congruence. auto.
  unfold remc.
  destruct (cand_eq_dec c l0). contradict l0neqc. symmetry. assumption. trivial.
Qed.

(* increment tally for cand by one *)
Definition inct (c:cand) (t: cand -> nat) : cand -> nat :=
  fun d => if (cand_eq_dec c d) then (S(t d))%nat else (t d).

Lemma inct_ok: forall c:cand, forall t: cand -> nat, inc c t (inct c t).
Proof.
  intros. unfold inc. split.
  Functional Scheme inct_ind := Induction for inct Sort Prop.
  functional induction  (inct c t c). omega.
  assert False. apply (_x). trivial. elim H.
  intros d ass.
  functional induction (inct c t d).
  assert False. apply ass. trivial. elim H. trivial.
Qed. 

(* add ballot to vote assignment  for cand *)
Definition adda (c:cand) (b:ballot) (a: cand -> list ballot) : cand -> list ballot :=
  fun d => if (cand_eq_dec c d) then (b::(a d)) else (a d).

Lemma adda_ok : forall c: cand, forall b: ballot, forall a: cand -> list ballot, add c b a (adda c b a).
Proof.
  intros. unfold adda. unfold add. destruct (cand_eq_dec c c). split. trivial.
  intros d ass. destruct (cand_eq_dec c d).  contradict ass. auto. trivial.
  split. contradict n. trivial. contradict n. trivial.
Qed.

(* prefixing is one way of conjoining *)
Lemma ins_hd {A: Type}: forall c: A, forall l: list A, eqe c l (c::l).
  Proof.
  intros c l.
  unfold eqe.
  exists ([]: list A). exists l. split.
  auto. auto.
Qed.
Notation " x 'With' p " := (exist _ x p) (at level 20). 

Lemma tly_qu : forall t :{ tally : (cand -> nat) | forall c, tally c <= qu }, 
   forall c, (proj1_sig t) c < qu -> 
  (forall d, inct c (proj1_sig t) d <= qu).
Proof.
  intros t c H1 d.
  assert (inc c (proj1_sig t) (inct c (proj1_sig t))).
  apply inct_ok.
  unfold inc in H.
  destruct H as [H2 H3].
  destruct (cand_eq_dec c d).
  subst. rewrite -> H2. intuition.
  specialize (H3 d).
  assert (d<>c). apply not_eq_sym. assumption.
  specialize (H3 H).
  rewrite -> H3.
  destruct t. simpl.
  simpl in H1, H2, H3. 
  specialize (l d).
  assumption. 
Qed. 

Lemma eq_tly: forall c, forall t: cand-> nat, (forall d : cand, t d <= qu) -> qu <= t c -> t c = qu.
Proof. 
  intros c t H1 H2.
  specialize H1 with c. intuition.
Qed.

Definition c1 (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists u nu a na t nt h e f fs,          (** count one vote **)
    let 'tl With tp := t in
    let 'ntl With ntp := nt in
  p = state (u, a, t, h, e ) /\          (* if we are counting votes *)
  eqe (f::fs) nu u /\                           (* and del'ing a vote with 1st pref f yields new list of uncounteds *)
  In f h /\                                     (* and f is a hopeful *)
  tl f < qu /\                                    (* and this isn't surplus *)
  add f (f::fs) a na /\                         (* and the new assignment records the vote for f *)
  inc f tl ntl /\                                 (* and the new tally increments the votes for f by one *)
  c = state (nu, na, nt, h, e).        (* we continue with updated tally and assignment *)
 
Lemma el_length_cons : forall l: list cand, forall d: cand, length l < s ->  length (d::l) <= s.
Proof. 
  intros l d H. simpl. auto.
Qed.    

Definition el (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists u a t h nh ne d e,                (** elect a candidate **)
    let 'els With elp := e in                (*  e and ne are sigma-types: {l : list cand | length l <= s } *)
    let 'nels With nelp := ne in
  p = state (u, a, t, h, e) /\           (* if we have an uncounted vote with 1st preference f *)
  In d h /\                                     (* and d is a hopeful *)
  (proj1_sig t) (d) = qu /\                                 (* and d has enough votes *)
  length els < s /\                              (* and there are still unfilled seats *)
  eqe d nh h /\                                 (* and f has been removed from the new list of hopefuls *)
  eqe d els nels /\                     (* and del'ing d from the new elected cands gives old elected *)
  c = state (u, a, t, nh, ne).            (* then proceed with updated  hopefuls and elected cands *)
  
Definition tv (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists u nu a t h e f fs,                (** transfer vote **)
  p = state (u, a, t, h, e) /\           (* if we are counting votes *)
  ~(In f h) /\                                  (* and f no longer in the running *)
  rep (f::fs) fs u nu /\                        (* and the uncounted votes are updated by deleting first pref f from a vote *)
 c = state (nu, a, t, h, e).            (* we continue with updated set of uncounted votes *)

Definition ey (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists u nu  a t h e,                    (** empty vote **)
  p = state (u, a, t, h, e) /\           (* if we are counting votes *)
  eqe [] nu u /\                                (* and an empty vote is removed from uncounted votes *)
  c = state (nu, a, t, h, e).             (* continue with updated set of uncounted votes *)

Definition tl (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists u a t h nh e d,                           (** transfer least **)
  p = state ([], a, t, h, e) /\                      (* if we have no uncounted votes *)
  length (proj1_sig e) + length h > s /\   (* and there are still too many candidates *)
  In d h  /\                                              (* and candidate d is still hopeful *)
  (forall e, In e h-> (proj1_sig t) d <= (proj1_sig t) e) /\   (* but all others have more votes *)
  eqe d nh h /\                                       (* and d has been removed from the new list of hopefuls *)
  u = a(d) /\                                            (* we transfer d's votes by marking them as uncounted *)
  c = state (u, a, t,nh, e).                       (* and continue in this new state *)

Definition hw (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists w u a t h e,                      (** hopefuls win **)
  p = state (u, a, t, h, e) /\           (* if at any time *)
  length (proj1_sig e) + length h <= s /\                   (* we have more hopefuls and electeds  than seats *)
  w = (proj1_sig e) ++ h /\                                 (* and the winning candidates are their union *)
  c = winners (w).                      (* the elected cands and the remaining hopefuls are declared winners *)

Definition ew (p: STV_Judgement) (c: STV_Judgement) : Prop :=
  exists w u a t h e,                      (** elected win **)
  p = state (u, a, t, h, e) /\           (* if at any time *)
  length (proj1_sig e) = s /\          (* we have as many elected candidates as setas *) 
  w = (proj1_sig e) /\                    (* and the winners are precisely the electeds *)
  c = winners w.                         (* they are declared the winners *)

(* list of rules for STV *)
Definition STV : list STV_Rule := [ c1; el; tv; ey; tl; hw; ew ].

(* lexicographic order is well-founded *)
(* from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/2554 *)
Definition STV_WFO := nat * (nat * nat). 

Definition dep2 := sigT (A:= nat) (fun a => nat).
Definition dep3 := sigT (A:= nat) (fun a => dep2).

Definition mk2  : nat * nat -> dep2.
 intros (p,q).
 exists p.
 exact q.
 Defined.

Definition mk3 : nat * (nat * nat) -> dep3.
 intros (n, p_q).
 exists n.
 exact (mk2 p_q).
Defined. 

Definition lt_pq :dep2->dep2->Prop :=
     (lexprod nat (fun a => nat) Peano.lt (fun a:nat =>Peano.lt)).
Definition lt_npq : dep3 -> dep3 -> Prop :=
     (lexprod nat (fun a => dep2) Peano.lt (fun a:nat =>lt_pq)).

Lemma wf_lexprod : well_founded lt_npq.
 unfold lt_npq;apply wf_lexprod.
 apply lt_wf.
 intro n.
 unfold lt_pq;apply wf_lexprod.
 apply lt_wf.
 intro m; apply lt_wf.
Qed.

Definition STV_wfo : STV_WFO -> STV_WFO -> Prop := (fun x y : nat * (nat * nat) => 
 lt_npq (mk3 x) (mk3 y)).

Lemma STV_wfo_wf : well_founded STV_wfo.
  unfold STV_wfo. 
 apply wf_inverse_image.
 apply wf_lexprod.
Qed.


(* defining the measure *)

(* sum of lengths *)
Fixpoint sum_len {A: Type} (l: list (list A)) : nat := match l with
| [] => 0
| x::xs => (length x + sum_len xs)%nat
end.

(* sum of lengths is a homomorphism *)
Lemma sum_len_hom {A: Type} (l1 l2: list (list A)) : sum_len (l1 ++ l2) = (sum_len l1 + sum_len l2)%nat.
Proof.
  induction l1 as [|x xs IHxs].
  simpl. reflexivity.
  simpl. rewrite -> IHxs. rewrite -> Plus.plus_assoc. reflexivity.
Qed.

Lemma sum_len_dec {A: Type} (l1 l2: list (list A)) (x: A) (xs : list A) :
  sum_len (l1 ++ [xs] ++ l2) < sum_len (l1 ++ [x::xs] ++ l2).
Proof.
  rewrite -> ?sum_len_hom.  simpl. 
   omega.
Qed.

(* measure *)
Definition STV_m: { j: STV_Judgement | not (STV_final j) } -> STV_WFO.
  intro H. 
  destruct H as [j ej]. 
  destruct j. 
  destruct p as [[[[u a] t] h] e].
  split. 
  exact (length h). 
  split.
  exact (length u).
  exact (sum_len u).
  contradiction ej.
  unfold STV_final. 
  exists l. 
  reflexivity.
Defined.

(* the lexicographic order is defined as intended *)
Lemma wfo_aux:  forall a b c a' b' c' : nat,
  (lt_npq (mk3 (a, (b, c))) (mk3 (a', (b', c'))) <->
    (a < a' \/
    (a = a' /\ b < b' \/
    (a = a' /\ b = b' /\ c < c')))).
Proof.
  intros. split. unfold lt_npq. unfold mk3. simpl. intro H. inversion H. subst.
  (* case 1st component are below one another *)
  auto.
  (* case 1st components are equal *)
  unfold lt_pq in H1. inversion H1. subst. auto.
  (* case 1st and 2nd components are equal and 3rd are below one another *)
  subst. auto.
  (* right-to-left direction *)
  intro H. destruct H.
  (* case 1st components are below one another *)
  unfold lt_npq. apply left_lex. assumption.
  destruct H.
  (* case 1st components are equal and 2nd components are below one another *)
  destruct H as [H1 H2]. subst. apply right_lex. apply left_lex. assumption.
  (* case 1st and 2nd components are identical, and 3rd components are below one another *)
  destruct H as [H1 H2]. subst. apply right_lex.  destruct H2 as [H1 H2]. subst. apply right_lex. assumption.
Qed.


(* we can find a candidate with least no of first prefs *)
Lemma list_min : forall A:Type, forall l: list A, forall f: A -> nat,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->f m <= f b))).
Proof.
  intros.
  induction l as [ | l ls ].
  left. trivial.
  destruct IHls.
  right.
  exists l. split.
  apply (in_eq l ls). intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass). destruct H. replace l with b. apply (le_n (f b)). replace ls with ([] : list A) in H.
  contradict H.
  right. destruct s0. destruct a.
  assert ( {f x <= (f l)}  + {(f l) <= (f x)}).
  apply (le_ge_dec (f x) (f l)). destruct H1.
  (* x is the minimum *)
  exists x. split.
  apply (in_cons l x ls). assumption. intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass).
  destruct H1. replace b with l. assumption.
  apply (H0  b H1).
  (* l is the minimum *)
  exists l. split.
  apply (in_eq l ls).
  intros b ass.
  assert (l = b \/ In b ls). apply (in_inv ass). destruct H1. 
  replace l with b. apply (le_n (f b)).
  transitivity (f x). assumption. apply (H0 b). assumption.
Defined.

(* proof of app property: a rule can always be applied to a non-final judgement *)
Lemma app_STV : app STV_Judgement STV_final STV.
Proof. 
  unfold app.
  intros p Hnf.  
  destruct p. 
  destruct p as [[[[u a] t] h] e].
  destruct u.
  (* case u = [] *)
  destruct (le_lt_dec (length (proj1_sig e) + length h) s).
    (* case length e + length h <= s *)
  exists hw.
  exists (winners ((proj1_sig e) ++ h)).
  split. unfold STV.
  simpl. intuition.
  unfold hw.
  exists ((proj1_sig e) ++ h); exists []; exists a; exists t; exists h; exists e.
  split. reflexivity.
  split. assumption.
  split. reflexivity. 
  reflexivity.      
    (* case length e + length h > s *)
  destruct h. 
      (* case h = [] *) 
  contradict l. destruct e. intro H. simpl in H. intuition.
      (* case h = (c :: h) *)
  exists tl.
  assert (min: ((c::h)= []) + (existsT d, (In d (c :: h) /\ (forall e, In e (c :: h) -> (proj1_sig t) d <= (proj1_sig t) e)))).
  apply list_min .
  destruct min as [emp | non_emp].
  symmetry in emp.
  assert ([] <> (c :: h)).   
  apply nil_cons.
  contradiction.
  destruct non_emp as [d [Hin Hmin]].
  exists (state (a d, a, t, remc d (c :: h), e)).
  split. unfold STV.
  intuition.
  unfold tl.
  exists (a d); exists a; exists t; exists (c :: h); exists (remc d (c :: h)); exists e; exists d.
  split. reflexivity.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply (remc_ok d (c :: h) Hin).
  split. reflexivity.
  reflexivity.          
  (* case u <> [] *) 
  destruct b. 
    (* case b = [] *)
  exists ey. 
  exists (state (u, a, t, h, e)).
  split. 
  unfold STV. intuition.
  unfold ey.
  exists ([] :: u); exists u; exists a; exists t; exists h; exists e.
  split. reflexivity.
  split. apply (ins_hd [] u).
  reflexivity.
  (* case b <> [] *)
  destruct (in_dec cand_eq_dec c h).
    (* case In c h *)
  destruct (le_lt_dec qu ((proj1_sig t) c)). 
      (* case t c >= qu *)
  destruct (le_lt_dec s (length (proj1_sig e))).
        (* case.length e >= s *)
  exists ew.
  exists (winners (proj1_sig e)).
  split. unfold STV.
  simpl. intuition.
  unfold ew.
  exists (proj1_sig e); exists ((c :: b) :: u); exists a; exists t; exists h; exists e. 
  split. reflexivity.
  split. destruct e. simpl in l0. simpl. intuition. 
  split. reflexivity. 
  reflexivity. 
        (* case.length e < s *)
  exists el.
  exists (state (((c :: b) :: u), a, t, (remc c h), (@exist (list cand) (fun l => length l <= s) (c :: (proj1_sig e)) (el_length_cons (proj1_sig e) c l0)))).
  split. unfold STV. 
  simpl. intuition.
  unfold el.
  exists ((c :: b) :: u). exists a; exists t. exists h; 
  exists (remc c h).
  pose (nel := c::(proj1_sig e)).
  pose (nep := el_length_cons (proj1_sig e) c l0).
  pose (ne := @exist (list cand) (fun l => length l <= s) nel nep).
  exists ne. exists c. exists e.
  remember e as e0. destruct e0.
  simpl.
  split. reflexivity.
  split. assumption.
  split. destruct t. simpl. simpl in l.
  apply (eq_tly c x0 l2). assumption.
  split. simpl in l0. assumption. 
  split. apply (remc_ok c h i).
  split. unfold nel. unfold eqe. exists []. exists x. simpl. split. reflexivity. reflexivity.
  unfold ne. unfold nel. simpl.
  reflexivity.
      (* case t c < qu *)
  exists c1.
  exists (state (u, (adda c (c :: b) a), (@exist (cand -> nat) (fun tl => (forall c0, tl c0 <= qu)) (inct c (proj1_sig t)) (tly_qu t c l)), h, e)).
  split. unfold STV. 
  simpl. intuition.
  unfold c1.
  exists ((c :: b) :: u); exists u; exists a; exists (adda c (c :: b) a).
  exists t.
  exists (@exist (cand -> nat) (fun tl => (forall c, tl c <= qu)) (inct c (proj1_sig t)) (tly_qu t c l)).
   exists h; exists e; exists c; exists b.
  destruct t. 
  split. reflexivity.
  split. apply (ins_hd (c :: b) u).
  split. assumption.
  split. assumption.
  split. apply (adda_ok c (c :: b) a).
  split. apply (inct_ok c x).
  reflexivity.         
    (* case ~ In c h *)
  exists tv. 
  exists (state ((b :: u), a, t, h, e)).
  split. unfold STV.
  simpl. intuition.
  unfold tv.
  exists ((c :: b) :: u); exists (b :: u); exists a; exists t; exists h; exists e; exists c; exists b.
  split. reflexivity. 
  split. assumption. 
  split. unfold rep.  
  exists []; exists u.
  split. simpl. reflexivity.
  simpl. reflexivity.
  reflexivity.    
  (* final judgement *)
  contradiction Hnf.
  unfold STV_final.
  exists l.
  reflexivity.
Qed.

(* proof of dec property : when a rule is applied, the measure decreases *)
(* proof is done rule by rule *)
Lemma dec_STV_c1 : forall p c : STV_Judgement,
c1 p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  (* non final judgements *)
  unfold STV_m.
  simpl.
  unfold STV_wfo.
  rewrite -> wfo_aux.
  right. left.
  unfold c1 in Hr. 
  destruct Hr as [u [nu [a [na [t [nt [h [e [f [fs H]]]]]]]]]]. 
  destruct t. destruct nt.  
  destruct H as [Heq1 [Heqe [Hin [Ht [Hadd [Hinc Heq2]]]]]].
  inversion Heq1. 
  inversion Heq2.
  split. reflexivity. 
  unfold eqe in Heqe.
  destruct Heqe as [l1 [l2 [Heqe1 Heqe2]]].
  rewrite -> Heqe1, Heqe2. 
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.   
  (* final jugements *)
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed. 


Lemma dec_STV_tv : forall p c : STV_Judgement,
tv p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  (* non final judgements *)
  unfold STV_m. simpl.
  unfold STV_wfo. 
  rewrite -> wfo_aux.
  right. right. 
  unfold tv in Hr.
  destruct Hr as [u [nu [a [t [h [e [f [fs H]]]]]]]].
  destruct H as [Heq1 [Hin [Hrep Heq2]]].
  inversion Heq1. inversion Heq2. subst.
  split. 
  reflexivity. 
  split.  
  unfold rep in Hrep.
  destruct Hrep as [l1 [l2 [Hrep1 Hrep2]]].
  rewrite -> Hrep1, Hrep2. 
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition. 
  unfold rep in Hrep.
  destruct Hrep as [l1 [l2 [Hrep1 Hrep2]]].
  rewrite -> Hrep1, Hrep2.
  apply sum_len_dec. 
  unfold STV_final in ec. contradict ec.
  exists l. reflexivity.
  unfold STV_final in ep. contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_STV_el : forall p c : STV_Judgement,
el p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  (* non final judgements *)
  unfold STV_m. simpl. 
  unfold STV_wfo. 
  rewrite -> wfo_aux.
  left.   
  unfold el in Hr. 
  destruct Hr as [u [a [t [h [nh [e [ne [d H]]]]]]]].
  destruct d. 
  destruct e.
  destruct H as [Heq1 [Hin [Hq [Hl [Hh [He Heq2]]]]]].
  inversion Heq1. 
  inversion Heq2. 
  unfold eqe in Hh.
  destruct Hh as [l1 [l2 [Hh1 Hh2]]].
  rewrite -> Hh1, Hh2.
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.   
  (* final jugements *)
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_STV_ey : forall p c : STV_Judgement,
ey p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  (* non final judgements *)
  unfold STV_m. simpl. 
  unfold STV_wfo. 
  rewrite -> wfo_aux.
  right. left.  
  unfold ey in Hr. 
  destruct Hr as [u [nu [a [t [h [e H]]]]]].
  destruct H as [Heq1 [Heqe Heq2]].
  inversion Heq1. 
  inversion Heq2.
  split. reflexivity. 
  unfold eqe in Heqe.
  destruct Heqe as [l1 [l2 [Heqe1 Heqe2]]].
  rewrite -> Heqe1, Heqe2.
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.   
  (* final jugements *)
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_STV_tl : forall p c : STV_Judgement,
tl p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  (* non final judgements *)
  unfold STV_m. simpl. 
  unfold STV_wfo. 
  rewrite -> wfo_aux.
  left.   
  unfold tl in Hr. 
  destruct Hr as [u [a [t [h [nh [e [d H]]]]]]].
  destruct H as [Heq1 [Hl [Hin [Ht [Heqe [Ha Heq2]]]]]].
  inversion Heq1. 
  inversion Heq2.
  unfold eqe in Heqe.
  destruct Heqe as [l1 [l2 [Heqe1 Heqe2]]].
  rewrite -> Heqe1, Heqe2.
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.   
  (* final jugements *)
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_STV_hw : forall p c : STV_Judgement,
hw p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  unfold hw in Hr. 
  destruct Hr as [w [u [a [t [h [e H]]]]]].
  destruct H as [Heq1 [Hl [Hw Heq2]]].
  inversion Heq2.
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.   
  (* final jugements *)
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_STV_ew : forall p c : STV_Judgement,
ew p c -> forall (ep : ~ STV_final p) (ec : ~ STV_final c),
STV_wfo (STV_m (mk_nfj STV_Judgement STV_final c ec))
  (STV_m (mk_nfj STV_Judgement STV_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[u1 a1] t1] h1] e1].
  destruct c. destruct p as  [[[[u2 a2] t2] h2] e2].
  unfold ew in Hr. 
  destruct Hr as [w [u [a [t [h [e H]]]]]].
  destruct H as [Heq1 [Hl [Hw Heq2]]].
  inversion Heq2.
  unfold STV_final in ec.
  contradict ec.
  exists l. reflexivity.   
  (* final jugements *)
  unfold STV_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

(* proof of dec property *)
Lemma dec_STV : dec STV_Judgement STV_final STV_WFO STV_wfo STV_m STV. 
Proof. 
  unfold dec.
  intros r Hin p c Hr ep ec.
  destruct Hin.
  rewrite <- H in Hr.
  apply (dec_STV_c1). 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_el. 
  assumption.     
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_tv. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_ey. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_tl. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_hw. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_STV_ew. 
  assumption.
  destruct H.
Qed.                  

End STV.

Section candidates.
(* our candidates *)
Inductive cand := Alice | Bob | Charlie | Deliah.
Definition cand_all := [Alice; Bob; Charlie; Deliah].

(* everything below here is independent of the definition of cand *)
(* as long as cand is an inductive type with nullary constructors *)
(* only and all_cands mentions all of them *)

Lemma cand_pd: PD cand_all.
Proof.
  repeat apply PDc
    || split
    || (repeat apply PDe
        || unfold In
        || tauto
        || (intro H; discriminate H; clear H)
        || (intro H; elim H; clear H)).
Qed.

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

End candidates.

Definition STV_termination :=
  termination (STV_Judgement cand qu s) (STV_final cand qu s) (final_dec cand qu s) STV_WFO 
  STV_wfo STV_wfo_wf (STV_m cand qu s) (STV cand qu s) (dec_STV cand qu s) 
  (app_STV cand cand_eq_dec qu s).

Extraction Language Haskell.
Extraction "/tmp/STV_generic.hs" STV_termination.         




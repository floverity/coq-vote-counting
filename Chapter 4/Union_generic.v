Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.NatInt.NZMul.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.ZArith.Znat. 
Require Import Coq.QArith.QArith_base.
Require Import  Coq.QArith.QOrderedType.
Require Import QArith_base Equalities Orders OrdersTac.
Require Import Coq.Sorting.Permutation.
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
Close Scope Q_scope. 

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

Section unionCount.
Close Scope Q_scope. 

(* lists with pairwise distinct candidates *)
Inductive PD  {A: Type} : list A -> Prop :=
   PDe :  PD  ( nil)
 | PDc :  forall a:A,forall l: list A, PD l /\ ~(In a l) -> (PD  (cons a l)).

Variable cand: Type.
Variable cand_all: list cand.
Hypothesis cand_pd: PD cand_all.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.
Hypothesis cand_in_dec: forall c : cand, forall l : list cand, {In c l} + {~In c l}.

(* a ballot is a permutation of the list of candidates and a transfer balue *)
Definition ballot :=  ({v : list cand | Permutation cand_all v} * Q).

Variable bs : list ballot.
Variable st : nat. 
Definition qu : Q := ((inject_Z (Z.of_nat (length bs))) / (1 + inject_Z (Z.of_nat st)) + 1)%Q. 

(* intermediate and final states in vote counting *)
Inductive FT_Judgement :=
   state:                                   (** intermediate states **)
       list ballot                          (* uncounted votes *)
     * (cand -> Q)                   (* tally *)
     * (cand -> list ballot)          (* pile of ballots for each candidate*)
     * list cand                          (* backlog of candidates requiring transfer *)
     * {elected: list cand | length  elected <= st}   (* elected candidates no longer in the running *)
     * list cand                          (* hopeful candidates still in the running *)
     -> FT_Judgement
  | winners:                  (** final state **)
    list cand -> FT_Judgement.        (* election winners *)

Definition FT_final (a : FT_Judgement) : Prop :=
   exists w, a = winners w.

Lemma final_dec: forall j : FT_Judgement, (FT_final j) + (not (FT_final j)).
Proof. 
  intro j. destruct j. 
  right.
  unfold FT_final.
  unfold not. intro H. 
  destruct H.
  discriminate. 
  left.
  unfold FT_final.
  exists l.
  reflexivity.
Defined.


(* Rules *)
Definition FT_Rule := FT_Judgement -> FT_Judgement -> Prop.

(* relation for `first continuing candidate' on a ballot in the list of ballots requiring attention *)
Definition fcc (ba : list ballot) (h : list cand) (c : cand) (b : ballot): Prop := 
  In b ba /\
  In c h /\
  (exists l1 l2 : list cand, 
      proj1_sig (fst b) = l1 ++ [c] ++ l2 /\ 
      forall d, (In d l1 -> ~(In d h))).

(* l and nl are equal except that nl additionally contains x *)
Definition eqe {A: Type} (x:A) (l: list A) (nl: list A) : Prop :=
  exists l1 l2: list A, l = l1 ++ l2 /\ nl = l1 ++ [x] ++ l2.

(* l and nl are equal except that nl additionally contains all the elements of a list k *)
Definition leqe {A: Type} (k: list A) (l: list A) (nl: list A) : Prop :=
  forall x, In x k -> eqe x l nl. 

(* summation of weights in a list of ballots *)
Fixpoint sum (l : list ballot) : Q :=
 match l with 
   | [] => 0%Q 
   | l :: ls => (snd l + sum ls)%Q
 end. 

Definition count (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists ba t nt p np bl h e,                (** count the ballots requiring attention **)
  prem = state (ba, t, p, bl, e, h) /\     (* if we are in an intermediate state of the count *) 
  [] <> ba /\                                        (* and there are ballots requiring attention *)
  (forall c, exists l,                              (* and for each candidate c there is a list of ballots *)
     np(c) = p(c) ++ l /\                       (* such that the pile for c is updated by adding these ballots to the top *)
     (forall b, In b l <-> fcc ba h c b) /\ (* and a ballot is added to c's pile iff c is the first continuing candidate on the ballot *)
     nt(c) = sum (np(c))) /\                  (* and the new tally for c is the sum of the weights of the ballots in c's pile *)
  conc = state ([], nt, np, bl, e, h).     (* then we proceed with no ballots requiring attention and updated piles and tallies *) 

Definition transfer (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists nba t p np bl nbl h e,         (** transfer votes **) 
  prem = state ([], t, p, bl, e, h) /\   (* if we are in an intermediate state of the count*)
  (forall c, In c h -> (t(c) < qu)%Q) /\        (* and we can't elect any candidate *)
  exists l c,                                     (* and there exists a list l and a candidate c *)
     (bl = c :: l /\                               (* such that c is the head of the backlog *)
     nbl = l /\                                    (* and the backlog is updated by removing the head c *)
     nba = p(c) /\                             (* and the pile of ballots for c is the new list of ballots requiring attention *)
     np(c) = [] /\                                (* and the new pile for c is empty *)
     (forall d, d <> c -> np(d) = p(d))) /\ (* and the piles for every other candidate remain the same *)
  conc = state (nba, t, np, nbl, e, h).  (* then continue with the new pile of ballots requiring attention and updated piles and backlog *)

Definition cut_list {A : Type} (l : list A) (n : nat) : list A :=
  if (le_lt_dec (length l) n) then  l else l.

Inductive ordered {A : Type} (f : A -> Q) : list A -> Prop := 
  ord_emp : ordered f []  
 | ord_sing : forall x : A, ordered f [x]
 | ord_cons : forall l x y, ordered f (y :: l) -> (f(x) >= f(y))%Q -> ordered f (x :: y :: l).

Definition elect (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists (ba: list ballot) (t: cand -> Q) (p np: cand -> list ballot) (bl nbl h nh: list cand) (e ne: {l : list cand | length l <= st }),
    let (els, elp) := e in                (*  e and ne are sigma-types: {l : list cand | length l <= s } *)
    let (nels, nelp) := ne in
  prem = state ([], t, p, bl, e, h) /\ (* if there are no ballots requiring attentions *)
  exists l,                                      (* and there is a list l *)
    (l <> [] /\                                   (* that is non empty *)
     length l <= st - length (proj1_sig e) /\   (* and is no greater than the number of available seats *) 
     (forall c, In c l -> In c h /\ (t(c) >= qu)%Q) /\       (* and contains the candidates who have reached the quota*)
     ordered t l /\ (* and l is ordered by tally, with the greatest at the head of the list *)
     leqe l nh h /\           (* and all of the candidates over quota have been removed from the hopefuls *)
     leqe l els nels /\      (* and added to the list of elected candidates *)
     (forall c, In c l -> (np c = map (fun (b : ballot) => 
        (fst b, (snd b * ((t(c)-qu)/t(c)))%Q)) (p c))) /\   (* and the piles for the candidates over quota are updated by transfer balue *)
     (forall c, ~ In c l -> np (c) = p (c)) /\  (* and the piles for all other candidates remain the same *)
     nbl = bl ++ l) /\                                  (* and the backlog is updated by adding l to the end *)
  conc = state ([], t, np, nbl, ne, nh).      (* then continue counting with updated piles, backlog, electeds and hopefuls *)

Definition elim (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists nba t p np e h nh,                    (** eliminate a hopeful **)
  prem = state ([], t, p, [], e, h) /\          (* if there are no ballots requiring attention and no backlog*)
  length (proj1_sig e) + length h > st /\ (* and the sum of the elected candidates and hopfuls is greater than the number of seats *)
  (forall c, In c h -> (t(c) < qu)%Q) /\    (* and all of the hopefuls are under the quota *)
  exists c,                                             (* and there is a candidate c *)
     ((forall d, In d h -> (t(c) <= t(d)))%Q /\            (* with minimum tally *)
     eqe c nh h /\                                   (* and the hopefuls are updated by removing c *)
     nba = p(c) /\                                    (* and the new list of ballots to requiring attention is c's pile *)
     np(c)=[] /\                                        (* and the new pile for c is empty *)
     (forall d, d <> c -> np (d) = p (d))) /\  (* and every other pile remains the same *)                                         
   conc = state (nba, t, np, [], e, nh).  (* then continute counting with updated ballots requiring attentions, piles and hopefuls *)

Definition hwin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                            (** hopefuls win **)
  prem = state (ba, t, p, bl, e, h) /\           (* if at any time *)
  length (proj1_sig e) + length h <= st /\ (* we have fewer hopefuls and electeds  than seats *)
  w = (proj1_sig e) ++ h /\                        (* and the winning candidates are their union *)
  conc = winners (w).                              (* the elected cands and the remaining hopefuls are declared winners *)

Definition ewin (prem: FT_Judgement) (conc: FT_Judgement) : Prop :=
  exists w ba t p bl e h,                    (** elected win **)
  prem = state (ba, t, p, bl, e, h) /\   (* if at any time *)
  length (proj1_sig e) = st /\             (* we have as many elected candidates as setas *) 
  w = (proj1_sig e) /\                        (* and the winners are precisely the electeds *)
  conc = winners (w).                      (* they are declared the winners *)

Definition FTR : list FT_Rule := [count; transfer; elect; elim; hwin; ewin].

(* well founded order *)

Definition FT_WFO := nat * (nat * nat). 

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

Definition FT_wfo : FT_WFO -> FT_WFO -> Prop := (fun x y : nat * (nat * nat) => 
 lt_npq (mk3 x) (mk3 y)).

Lemma FT_wfo_wf : well_founded FT_wfo.
  unfold FT_wfo. 
 apply wf_inverse_image.
 apply wf_lexprod.
Qed.

(* measure function maps to (length h, length bl, length ba) *)
Definition FT_m: { j: FT_Judgement | not (FT_final j) } -> FT_WFO.
  intro H. 
  destruct H as [j ej]. 
  destruct j. 
  destruct p as [[[[[ba t] p] bl] e] h].
  split. 
  exact (length h). 
  split.
  exact (length bl).
  exact (length ba).
  contradiction ej.
  unfold FT_final. 
  exists l. 
  reflexivity.
Defined.

(* lexicographic order behaves as expected *)
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
Lemma list_min : forall A:Type, forall l: list A, forall f: A -> Q,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->(f m <= f b)%Q))).
Proof.
  intros.
  induction l as [ | l ls ].
  left. trivial.
  destruct IHls.
  right.
  exists l. split.
  apply (in_eq l ls). intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass). destruct H. replace l with b. intuition. replace ls with ([] : list A) in H.
  contradict H.
  right. destruct s. destruct a.
  assert ( {(f x < (f l))%Q}  + {((f l) <= (f x))%Q}).
  apply (Qlt_le_dec (f x) (f l))%Q.
  assert ( {(f x <= (f l))%Q}  + {((f l) <= (f x))%Q}).
  intuition.
  destruct H2.
  (* x is the minimum *)
  exists x. split.
  apply (in_cons l x ls). assumption. intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass).
  destruct H2. replace b with l. assumption.
  apply (H0 b H2).
  (* l is the minimum *)
  exists l. split.
  apply (in_eq l ls).
  intros b ass.
  assert (l = b \/ In b ls). apply (in_inv ass). destruct H2. 
  replace l with b. intuition.
  specialize (H0 b H2).
  apply (Qle_trans (f l) (f x) (f b)). assumption. assumption.
Defined. 

(* remove one occurrence of a candidate from a list *)
Fixpoint remc (c: cand) (l: list cand) :=
  match l with 
    nil => nil
  | cons l0 ls => if (cand_eq_dec c l0) then ls else cons l0 (remc c ls)
  end.

(* remove a list of candidates from another list *) 
Fixpoint reml (l : list cand) ( r : list cand) : list cand :=
  match r with 
  [] => l
  | r0 :: rs => reml (remove cand_eq_dec r0 l) rs
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

(* update piles of candidates in a list *)
Fixpoint upiles (p: cand -> list ballot) (t: cand -> Q) (m : list cand) : cand -> list ballot :=
  match m with 
  [] => p 
 | m0 :: ms => upiles (fun (c : cand) => 
        (if cand_eq_dec c m0 then (map (fun (b : ballot) => 
        (fst b, (snd b * ((t(m0)-qu)/t(m0)))%Q)) (p m0)) else p c)) t ms
  end.

(* empty the pile for one candidate and leave the rest unchanged *)
Definition emp (c: cand) (p: cand -> list ballot) : cand -> list ballot :=
  fun d => if (cand_eq_dec c d) then [] else p d.

(* proof of dec property *)
(* proof done rule by rule *)
Lemma dec_FT_count : forall p c : FT_Judgement,
count p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
  intros p c Hr ep ec.
  destruct p.
  destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c.
  destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
   (* non final judgements *)
  unfold FT_m.
  simpl.
  unfold FT_wfo.
  rewrite -> wfo_aux.
  right. right.
  unfold count in Hr.
  destruct Hr as [ba [t [nt [p [np [bl [h [e H]]]]]]]].
  destruct H as [Heq1 [Hba [Hc Heq2]]].
  inversion Heq1.  
  inversion Heq2. subst.
  split. reflexivity. 
  split. reflexivity.
  simpl.
  destruct ba. 
  contradict Hba. reflexivity. 
  simpl. intuition.
  (* final jugements *)
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed. 

Lemma dec_FT_transfer : forall p c : FT_Judgement,
transfer p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
  intros p c Hr ep ec.
  destruct p.
  destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c.
  destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
   (* non final judgements *)
  unfold FT_m.
  simpl.
  unfold FT_wfo.
  rewrite -> wfo_aux.
  right. left. 
  unfold transfer in Hr.
  destruct Hr as [nba [t [p [np [bl [nbl [h [e H]]]]]]]].
  destruct H as [Heq1 [ Hinh [l [c [Hex Heq2]]]]].
  inversion Heq1.  
  inversion Heq2. subst.
  split. reflexivity.
  destruct Hex as [Hex1 [Hex2 Hex]].
  rewrite -> Hex1, Hex2.
  intuition.   
  (* final jugements *)
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed. 

Lemma dec_FT_elect : forall p c : FT_Judgement,
elect p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
  intros p c Hr ep ec.
  destruct p.
  destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c.
  destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
   (* non final judgements *)
  unfold FT_m.
  simpl.
  unfold FT_wfo.
  rewrite -> wfo_aux.
  left. 
  unfold elect in Hr.
  destruct Hr as [ba [t [p [np [bl [nbl [h [nh [e [ne H]]]]]]]]]].
  destruct e.
  destruct ne.
  destruct H as [Heq1 [k [Hc Heq2]]].
  inversion Heq1.  
  inversion Heq2. subst.
  destruct Hc as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  unfold leqe in H5.
  unfold eqe in H5.
  destruct k.
  contradict H1. reflexivity.
  specialize (H5 c).
  assert (In c (c :: k)).
  intuition.
  specialize (H5 H).
  destruct H5 as [l1 [l2 [h1 h2]]].
  subst.
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.
  (* final jugements *)
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed. 

Lemma dec_FT_elim : forall p c : FT_Judgement,
elim p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof. 
  intros p c Hr ep ec.
  destruct p.
  destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c.
  destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
   (* non final judgements *)
  unfold FT_m.
  simpl.
  unfold FT_wfo.
  rewrite -> wfo_aux.
  left. 
  unfold elim in Hr.
  destruct Hr as [nba [t [p [np [e [h [nh H]]]]]]].
  destruct H as [Heq1 [Hl [Hc [c [Ht Heq2]]]]].
  inversion Heq1. 
  inversion Heq2. 
  subst.
  destruct Ht as [H1 [H2 H3]].
  unfold eqe in H2.
  destruct H2 as [l1 [l2 [h1 h2]]].
  subst.
  rewrite -> app_length. rewrite -> app_length. rewrite -> app_length.
  intuition.
  (* final jugements *)
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_FT_hwin : forall p c : FT_Judgement,
hwin p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c. destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
  unfold hwin in Hr. 
  destruct Hr as [w [ba [t [p [bl [e [h H]]]]]]].
  destruct H as [Heq1 [Hl [Hw Heq2]]].
  inversion Heq2.
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.   
  (* final jugements *)
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_FT_ewin : forall p c : FT_Judgement,
ewin p c -> forall (ep : ~ FT_final p) (ec : ~ FT_final c),
FT_wfo (FT_m (mk_nfj FT_Judgement FT_final c ec))
  (FT_m (mk_nfj FT_Judgement FT_final p ep)).
Proof.
  intros p c Hr ep ec.
  destruct p. destruct p as [[[[[ba1 t1] p1] bl1] e1] h1].  
  destruct c. destruct p as [[[[[ba2 t2] p2] bl2] e2] h2].
  unfold hwin in Hr. 
  destruct Hr as [w [ba [t [p [bl [e [h H]]]]]]].
  destruct H as [Heq1 [Hl [Hw Heq2]]].
  inversion Heq2.
  unfold FT_final in ec.
  contradict ec.
  exists l. reflexivity.   
  (* final jugements *)
  unfold FT_final in ep.
  contradict ep.
  exists l. reflexivity.
Qed.

Lemma dec_FT : dec FT_Judgement FT_final FT_WFO FT_wfo FT_m FTR. 
Proof. 
  unfold dec.
  intros r Hin p c Hr ep ec.
  destruct Hin.
  rewrite <- H in Hr.
  apply dec_FT_count. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_FT_transfer. 
  assumption.     
  destruct H.
  rewrite <- H in Hr.
  apply dec_FT_elect. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_FT_elim. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_FT_hwin. 
  assumption.
  destruct H.
  rewrite <- H in Hr.
  apply dec_FT_ewin. 
  assumption.
  destruct H.
Qed.                      

Fixpoint insert_sorted (A : Type) (a : A) (f : A -> Q) (l : list A) : list A :=
 match l with
   | [] => [a]
   | b :: ls =>
      match (Qcompare (f a) (f b)) with
      | Eq => a::l
      | Lt => a::l
      | Gt => b::(insert_sorted A a f ls)
      end
 end.

(* proof of app property --- still under construction ---
Lemma app_FT : app FT_Judgement FT_final FTR.
Proof. 
  unfold app.
  intros p Hnf.
  destruct p. 
  destruct p as [[[[[ba t] p] bl] e] h].  
  destruct ba.
  (* case ba = [] *)
  destruct (le_lt_dec (length (proj1_sig e) + length h) st) as [ les1 | les2 ].
       (* case length (proj1_sig e) + length h <= st *)
  exists hwin. 
  exists (winners ((proj1_sig e) ++ h)).
  split. 
  unfold FTR. intuition. 
  unfold hwin. 
  exists (proj1_sig e ++ h); exists []; exists t; exists p; exists bl; exists e; exists h.
  split. reflexivity.
  split. assumption.
  split. reflexivity.
  reflexivity.
       (* case length (proj1_sig e) + length h > st *)
   assert (existsT m : list cand, 
    (forall d : cand, In d m <-> In d h /\ (t(d) >= qu)%Q)
    /\ (ordered t m)).
  apply (over_quota cand h t qu cand_eq_dec).
  destruct X as [l [Hl1 Hl2]].
  destruct l.
               (* case l = [] (-> forall In c h, t(c) < qu) *)
  assert (forall d, In d h -> (t(d)<qu)%Q).
  intros d H.
  specialize (Hl1 d).
  destruct Hl1 as [Hla Hlb].
  assert (~ (In d h /\ (qu <= t d)%Q)).
  contradict Hlb.
  intuition.
  intuition. 
  destruct bl. 
                  (* case bl = [] *)
  exists elim.
  assert (min:  (h = []) + (existsT d, (In d h /\ (forall e, In e h -> (t d <= t e)%Q)))).
  apply list_min .
  destruct min as [emp | non_emp].
  destruct h. 
          (* case h = [] *)
  contradict les2. destruct e. simpl. intuition.
          (* case h = c :: h *)
  symmetry in emp. 
  assert ([] <> c :: h). 
  apply nil_cons.
  contradiction.
  destruct non_emp as [d [Hin Hmin]].
  exists (state ((p d), t, (emp d p), [], e, (remc d h))).
  split.
  unfold FTR.
  intuition.
  unfold elim.
  exists (p d); exists t; exists p; exists (emp d p); exists e; exists h; exists (remc d h).
  split. reflexivity.
  split. assumption.
  split. assumption.
  exists d.
  split. split. assumption.
  split. apply (remc_ok d h Hin).
  split. reflexivity.
  split. unfold emp. destruct (cand_eq_dec d d). reflexivity. contradict n. reflexivity.
  intros d0 Hneq.
  unfold emp. destruct (cand_eq_dec d d0). subst. contradict Hneq. reflexivity. reflexivity.
  reflexivity. 
                  (* case bl = c :: bl *)
  exists transfer.
  exists (state ((p c), t, (emp c p), bl, e, h)).
  split. unfold FTR. intuition.
  unfold transfer.
  exists (p c). exists t. exists p. exists (emp c p). exists (c :: bl). exists bl. exists h. exists e.
  split. reflexivity.
  split. assumption.
  exists bl. exists c.
  split. split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. unfold emp. destruct (cand_eq_dec c c). reflexivity. contradict n. reflexivity.
  intros d Hneq.
  unfold emp. destruct (cand_eq_dec c d). subst. contradict Hneq. reflexivity. reflexivity.
  reflexivity.
               (* case l = c :: k  (-> ~(forall In c h, t(c) < qu)) *)     
  exists elect. (* construct new pile *)
      (* l *)
  destruct (le_lt_dec (length (c::l) + (length (proj1_sig e))) (st)).
  rewrite <- app_length in l0. 
  exists (state ([], t, (upiles p t (c :: l)), (bl ++ (c :: l)), 
  (@exist (list cand) (fun l => length l <= st) ((c :: l) ++ (proj1_sig e)) (l0)),
  (reml (c :: l) h))).
  split. 
  unfold FTR. intuition.
  unfold elect.
  exists []. exists t. exists p. exists (upiles p t (c :: l)). exists bl.  
  exists ( bl ++ c :: l). exists h. exists (reml h (c :: l)). exists e.  exists (@exist (list cand) (fun l => length l <= st) ((c :: l) ++ (proj1_sig e)) (l0)).
  destruct e. split.
  reflexivity.
  exists (c :: l).
  split.
  split. intuition. symmetry in H.  contradict H. apply nil_cons.
  split. simpl. simpl in l0. 
  rewrite -> app_length in l0. intuition.  
  split. intro c0. specialize (Hl1 c0). destruct Hl1.  assumption.
  split. assumption.  
  split. admit.
  split. admit.
  split. intros c0 H. unfold upiles. destruct (cand_eq_dec c0 c). subst. *)


End unionCount. 
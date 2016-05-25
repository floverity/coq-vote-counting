module FPTPCode where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r x h y =
  eq_rect x h y

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons y l' -> S (length l')}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

le_lt_dec :: Nat -> Nat -> Sumbool
le_lt_dec n m =
  nat_rec (\m0 -> Left) (\n0 iHn m0 ->
    case m0 of {
     O -> Right;
     S m1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m1)}) n m

le_ge_dec :: Nat -> Nat -> Sumbool
le_ge_dec n m =
  sumbool_rec (\_ -> Left) (\_ -> Right) (le_lt_dec n m)

type Rule judgement = ()

mk_nfj :: a1 -> a1
mk_nfj j =
  j

type App judgement =
  judgement -> () -> SigT (Rule judgement) (SigT judgement ())

data Pf judgement =
   Ax judgement
 | Mkp judgement (Pf judgement)

extend :: (a1 -> a2) -> (List (Rule a1)) -> (App a1) -> a1 -> a1 -> (Pf
          a1) -> SigT a1 (Prod (Pf a1) ())
extend m rules happ a b pab =
  let {happ0 = happ b} in
  case happ0 __ of {
   ExistT _ happ1 ->
    case happ1 of {
     ExistT c _ -> ExistT c (Pair (Mkp c pab) __)}}

termination_aux :: (a1 -> Sum () ()) -> (a1 -> a2) -> (List (Rule a1)) ->
                   (App a1) -> a2 -> a1 -> a1 -> (Pf a1) -> SigT a1
                   (Prod () (Pf a1))
termination_aux final_dec0 m rules happ n a b x =
  well_founded_induction_type (\w iH a0 b0 _ _ hab ->
    let {hex = extend m rules happ a0 b0 hab} in
    case hex of {
     ExistT c p ->
      case p of {
       Pair hex1 _ ->
        let {s = final_dec0 c} in
        case s of {
         Inl _ -> ExistT c (Pair __ hex1);
         Inr _ ->
          eq_rect_r w iH (m (mk_nfj b0)) (m (mk_nfj c)) __ a0 c __ __ hex1}}})
    n a b __ __ x

termination :: (a1 -> Sum () ()) -> (a1 -> a2) -> (List (Rule a1)) -> (App
               a1) -> a1 -> SigT a1 (Prod () (Pf a1))
termination final_dec0 m rules happ a =
  let {s = final_dec0 a} in
  case s of {
   Inl _ -> ExistT a (Pair __ (Ax a));
   Inr _ ->
    termination_aux final_dec0 m rules happ (m (mk_nfj a)) a a (Ax a)}

data FPTP_Judgement cand =
   State (Prod (List cand) (cand -> Nat))
 | Winner cand

final_dec :: (FPTP_Judgement a1) -> Sum () ()
final_dec j =
  case j of {
   State p -> Inr __;
   Winner c -> Inl __}

fPTP_m :: (FPTP_Judgement a1) -> Nat
fPTP_m h =
  case h of {
   State nfj ->
    case nfj of {
     Pair u t -> length u};
   Winner fj -> false_rec}

type FPTP_Rule cand = ()

inct :: (a1 -> a1 -> Sumbool) -> a1 -> (a1 -> Nat) -> a1 -> Nat
inct cand_eq_dec0 c t d =
  case cand_eq_dec0 c d of {
   Left -> S (t d);
   Right -> t d}

fPTPR :: List (FPTP_Rule a1)
fPTPR =
  Cons __ (Cons __ Nil)

list_max :: (List a1) -> (a1 -> Nat) -> Sum () (SigT a1 ())
list_max l f =
  list_rect (Inl __) (\l0 ls iHls -> Inr
    (case iHls of {
      Inl _ -> ExistT l0 __;
      Inr lsnemp ->
       case lsnemp of {
        ExistT maxls _ ->
         let {h = le_ge_dec (f maxls) (f l0)} in
         case h of {
          Left -> ExistT l0 __;
          Right -> ExistT maxls __}}})) l

list_cand_max :: (List a1) -> a1 -> (a1 -> Nat) -> SigT a1 ()
list_cand_max cand_all0 cand_inh0 f =
  let {h = list_max cand_all0 f} in
  case h of {
   Inl _ -> false_rect;
   Inr hnemp ->
    case hnemp of {
     ExistT max _ -> ExistT max __}}

app_FPTPR :: (List a1) -> (a1 -> a1 -> Sumbool) -> a1 -> (FPTP_Judgement
             a1) -> SigT (Rule (FPTP_Judgement a1))
             (SigT (FPTP_Judgement a1) ())
app_FPTPR cand_all0 cand_eq_dec0 cand_inh0 p =
  case p of {
   State p0 ->
    case p0 of {
     Pair u t ->
      case u of {
       Nil -> ExistT __
        (let {hmax = list_cand_max cand_all0 cand_inh0 t} in
         case hmax of {
          ExistT m _ -> ExistT (Winner m) __});
       Cons c u0 -> ExistT __ (ExistT (State (Pair u0
        (inct cand_eq_dec0 c t))) __)}};
   Winner fj -> false_rect}

data Cand =
   Alice
 | Bob
 | Claire
 | Darren

cand_rect :: a1 -> a1 -> a1 -> a1 -> Cand -> a1
cand_rect f f0 f1 f2 c =
  case c of {
   Alice -> f;
   Bob -> f0;
   Claire -> f1;
   Darren -> f2}

cand_rec :: a1 -> a1 -> a1 -> a1 -> Cand -> a1
cand_rec =
  cand_rect

cand_all :: List Cand
cand_all =
  Cons Alice (Cons Bob (Cons Claire (Cons Darren Nil)))

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec a b =
  cand_rec (cand_rec Left Right Right Right b)
    (cand_rec Right Left Right Right b)
    (cand_rec Right Right Left Right b)
    (cand_rec Right Right Right Left b) a

cand_inh :: Cand
cand_inh =
  Alice

fPTP_termination :: (FPTP_Judgement Cand) -> SigT (FPTP_Judgement Cand)
                    (Prod () (Pf (FPTP_Judgement Cand)))
fPTP_termination =
  termination final_dec fPTP_m fPTPR (\x _ ->
    app_FPTPR cand_all cand_eq_dec cand_inh x)


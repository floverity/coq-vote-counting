{-# LANGUAGE StandaloneDeriving, FlexibleInstances, OverlappingInstances #-}

import Data.List
import FPTPCode

{- conversion between coq and haskell data structures -}
{- haskell lists to coq lists -}
h2cl [] = Nil
h2cl (a:as) = Cons a (h2cl as)

{- coq lists to haskell lists -}
c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x:(c2hl xs)

{- coq naturals to haskell Ints -}
c2hn :: Nat -> Int
c2hn O = 0
c2hn (S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))



{- equality for coq data structures -}
deriving instance Eq Cand
deriving instance Eq Nat
deriving instance (Eq a) => Eq (List a)

{- visualisation of data structures -}
instance Show  (Prod () (Pf (FPTP_Judgement Cand))) where
  show (Pair _ p)  = show p
instance (Show a, Show b) => Show (Prod a b) where
  show (Pair x y) = "(" ++ (show x) ++ ", " ++ (show y) ++ ")"
deriving instance Show Cand
-- deriving instance Show Nat
instance Show Nat where
  show n = show (c2hn n)
deriving instance Show (FPTP_Judgement Cand)

line :: String
line = ('-'):line

overline :: String -> String
overline s = (take (Data.List.length s) line) ++ "\n" ++ s

{- data type definition:

data Pf judgement =
   Ax judgement
 | Mkp judgement (Pf judgement)

-}

instance Show (Pf (FPTP_Judgement Cand)) where
  show (Ax j) = overline (show j)
  show (Mkp j  p) = (show p) ++ "\n" ++ (overline (show j)) 

instance (Show a, Show b) => Show (SigT a b) where
 show (ExistT x p) = (show x) ++ "\n" ++ (show p)



instance Show (Cand -> Nat) where
  show f = show_l (c2hl cand_all) where
    show_l [] = ""
    show_l [c] = (show c) ++ "[" ++ (show (f c)) ++ "]"
    show_l (c:cs) = (show c) ++ "[" ++ (show (f c)) ++ "] " ++ (show_l cs)

instance (Show a) => Show (List a) where
  show l = show (c2hl l)

-- test data
j1 :: FPTP_Judgement Cand
j1 = State (Pair (h2cl [Alice, Alice, Bob, Claire]) (\x -> O))

fptp_count :: [Cand] -> SigT (FPTP_Judgement Cand) (Prod () (Pf (FPTP_Judgement Cand)))
fptp_count l = fPTP_termination (State (Pair (h2cl l) (\x -> O)))

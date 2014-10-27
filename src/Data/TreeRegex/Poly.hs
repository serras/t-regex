{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
module Data.TreeRegex.Poly where

import Data.GenericK

import Unsafe.Coerce -- :(

-- As defined in page 58 of "Tree Automata Techniques and Applications"
-- * f -> set of constructors
-- * s -> set of iteration and concatenation positions
-- * ix -> index over the data types
data TreeRegex'' s (ix :: k) (f :: k -> (k -> *) -> *)
  = Empty'
  | Any'
  | In' (f ix (TreeRegex' s f))
  | Square' s
  | Choice' (TreeRegex' s f ix) (TreeRegex' s f ix)
  | Concat' (s -> TreeRegex' s f ix) (TreeRegex' s f ix)
  | Iter' (s -> TreeRegex' s f ix)
data TreeRegex' s f ix = TR { unTreeRegex' :: TreeRegex'' s ix f }
newtype TreeRegex f ix = TreeRegex { unTreeRegex :: forall s. TreeRegex' s f ix }

pattern Empty = TR Empty'
pattern Any = TR Any'
pattern In x = TR (In' x)
pattern Square s = TR (Square' s)
pattern Choice x y = TR (Choice' x y)
pattern Concat x y = TR (Concat' x y)
pattern Iter x = TR (Iter' x)

newtype Fix' (ix :: k) (f :: k -> (k -> *) -> *) = Fix' { unFix' :: f ix (Fix f) }
newtype Fix  (f :: k -> (k -> *) -> *) (ix :: k) = Fix  { unFix  :: Fix' ix f }

pattern F x = Fix (Fix' x)


match :: (Generic1k f, MatchG' (Rep1k f))
      => TreeRegex f ix -> Fix f ix -> Bool
match r t = match' (unTreeRegex r) t 0 []

match' :: (Generic1k f, MatchG' (Rep1k f))
       => TreeRegex' Integer f ix
       -> Fix f ix
       -> Integer  -- Fresh variable generator
       -> [(Integer, forall h ix. TreeRegex' Integer h ix)]  -- Ongoing substitution
       -> Bool
match' Empty          _ _ _ = False
match' Any            _ _ _ = True
match' (In r)     (F t) i s = matchG' (from1k r) (from1k t) i s
match' (Square n)     t i s = let Just r = unsafeCoerce (lookup n s) in match' r t i s
match' (Choice r1 r2) t i s = match' r1 t i s || match' r2 t i s
match' (Concat r1 r2) t i s = match' (r1 i) t (i+1) ((i, unsafeCoerce r2):s)
match' (Iter r)       t i s = match' (Concat r (Iter r)) t i s

class MatchG' (f :: k -> (k -> *) -> *) where
  matchG' :: (Generic1k g, MatchG' (Rep1k g))
          => f ix (TreeRegex' Integer g) -> f ix (Fix g)
          -> Integer -> [(Integer, forall h xi. TreeRegex' Integer h xi)] -> Bool


instance MatchG' U1k where
  matchG' _ _ _ _ = True

instance MatchG' (Par1k xi) where
  matchG' (Par1k r) (Par1k t) = match' r t

instance MatchG' f => MatchG' (Rec1k f xi) where
  matchG' (Rec1k r) (Rec1k t) = matchG' r t

instance Eq c => MatchG' (K1k i c) where
  matchG' (K1k r) (K1k t) _ _ = r == t

instance (MatchG' a, MatchG' b) => MatchG' (a :++: b) where
  matchG' (L1k r) (L1k t) i s = matchG' r t i s
  matchG' (R1k r) (R1k t) i s = matchG' r t i s
  matchG' _       _       _ _ = False

instance (MatchG' a, MatchG' b) => MatchG' (a :**: b) where
  matchG' (r1 :**: r2) (t1 :**: t2) i s = matchG' r1 t1 i s && matchG' r2 t2 i s

instance MatchG' f => MatchG' (Tag1k f xi) where
  matchG' (Tag1k r) (Tag1k t) = matchG' r t

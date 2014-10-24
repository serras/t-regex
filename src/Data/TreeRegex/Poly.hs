{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.TreeRegex.Poly where

import GHC.Generics
import Data.GenericK

-- As defined in page 58 of "Tree Automata Techniques and Applications"
-- * f -> set of constructors
-- * s -> set of iteration and concatenation positions
-- * ix -> index over the data types
data TreeRegex' s (f :: (k -> *) -> (k -> *)) (ix :: k)
  = Empty
  | Any
  | In (f (TreeRegex' s f) ix)
  | Square s
  | Choice (TreeRegex' s f ix) (TreeRegex' s f ix)
  | Concat (s -> TreeRegex' s f ix) (TreeRegex' s f ix)
  | Iter (s -> TreeRegex' s f ix)
newtype TreeRegex f ix = TreeRegex { unTreeRegex :: forall s. TreeRegex' s f ix }

newtype Fix (f :: (k -> *) -> (k -> *)) (ix :: k) = Fix { unFix :: f (Fix f) ix }


match :: (Generic1k f, MatchG' (Rep1k f ix))
      => TreeRegex f ix -> Fix f ix -> Bool
match r t = match' (unTreeRegex r) t 0  -- []

match' :: (Generic1k f, MatchG' (Rep1k f ix))
       => TreeRegex' Integer f ix
       -> Fix f ix
       -> Integer  -- Fresh variable generator
       -- -> [(Integer, TreeRegex' Integer f)]  -- Ongoing substitution
       -> Bool
match' Empty          _ _ = False
match' Any            _ _ = True
match' (In r)   (Fix t) i = matchG' (from1k r) (from1k t) i
-- match' (Square n)     t i = let Just r = lookup n s in match' r t i s
match' (Choice r1 r2) t i = match' r1 t i || match' r2 t i
-- match' (Concat r1 r2) t i = match' (r1 i) t (i+1) ((i,r2):s)
match' (Iter r)       t i = match' (Concat r (Iter r)) t i -- s

class MatchG' (f :: * -> *) where
  matchG' :: (Generic1k g, MatchG' (Rep1k g xi))
          => f (TreeRegex' Integer g xi) -> f (Fix g xi)
          -> Integer {- -> [(Integer, TreeRegex' Integer g)] -} -> Bool

instance MatchG' U1 where
  matchG' _ _ _ = True

instance MatchG' Par1 where
  matchG' (Par1 r) (Par1 t) = match' r t

instance Eq c => MatchG' (K1 i c) where
  matchG' (K1 r) (K1 t) _ = r == t

instance MatchG' f => MatchG' (Rec1 f) where
  matchG' (Rec1 r) (Rec1 t) = matchG' r t

instance MatchG' a => MatchG' (M1 i c a) where
  matchG' (M1 r) (M1 t) = matchG' r t

instance (MatchG' a, MatchG' b) => MatchG' (a :+: b) where
  matchG' (L1 r) (L1 t) i = matchG' r t i
  matchG' (R1 r) (R1 t) i = matchG' r t i
  matchG' _      _      _ = False

instance (MatchG' a, MatchG' b) => MatchG' (a :*: b) where
  matchG' (r1 :*: r2) (t1 :*: t2) i = matchG' r1 t1 i && matchG' r2 t2 i

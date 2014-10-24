{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
module Data.TreeRegex.Mono where

import GHC.Generics

-- As defined in page 58 of "Tree Automata Techniques and Applications"
-- * f -> set of constructors
-- * k -> set of iteration and concatenation positions
data TreeRegex' k f
  = Empty
  | Any
  | In (f (TreeRegex' k f))
  | Square k
  | Choice (TreeRegex' k f) (TreeRegex' k f)
  | Concat (k -> TreeRegex' k f) (TreeRegex' k f)
  | Iter (k -> TreeRegex' k f)
  deriving Generic

newtype Fix f = Fix { unFix :: f (Fix f) } deriving Generic
newtype TreeRegex f = TreeRegex { unTreeRegex :: forall k. TreeRegex' k f }

match :: (Generic1 f, MatchG' (Rep1 f))
      => TreeRegex f -> Fix f -> Bool
match r t = match' (unTreeRegex r) t 0 []

match' :: (Generic1 f, MatchG' (Rep1 f))
       => TreeRegex' Integer f
       -> Fix f
       -> Integer  -- Fresh variable generator
       -> [(Integer, TreeRegex' Integer f)]  -- Ongoing substitution
       -> Bool
match' Empty          _ _ _ = False
match' Any            _ _ _ = True
match' (In r)   (Fix t) i s = matchG' (from1 r) (from1 t) i s
match' (Square n)     t i s = let Just r = lookup n s in match' r t i s
match' (Choice r1 r2) t i s = match' r1 t i s || match' r2 t i s
match' (Concat r1 r2) t i s = match' (r1 i) t (i+1) ((i,r2):s)
match' (Iter r)       t i s = match' (Concat r (Iter r)) t i s

class MatchG' f where
  matchG' :: (Generic1 g, MatchG' (Rep1 g))
          => f (TreeRegex' Integer g) -> f (Fix g)
          -> Integer -> [(Integer, TreeRegex' Integer g)] -> Bool

instance MatchG' U1 where
  matchG' _ _ _ _ = True

instance MatchG' Par1 where
  matchG' (Par1 r) (Par1 t) = match' r t

instance Eq c => MatchG' (K1 i c) where
  matchG' (K1 r) (K1 t) _ _ = r == t

instance MatchG' f => MatchG' (Rec1 f) where
  matchG' (Rec1 r) (Rec1 t) = matchG' r t

instance MatchG' a => MatchG' (M1 i c a) where
  matchG' (M1 r) (M1 t) = matchG' r t

instance (MatchG' a, MatchG' b) => MatchG' (a :+: b) where
  matchG' (L1 r) (L1 t) i s = matchG' r t i s
  matchG' (R1 r) (R1 t) i s = matchG' r t i s
  matchG' _      _      _ _ = False

instance (MatchG' a, MatchG' b) => MatchG' (a :*: b) where
  matchG' (r1 :*: r2) (t1 :*: t2) i s = matchG' r1 t1 i s && matchG' r2 t2 i s


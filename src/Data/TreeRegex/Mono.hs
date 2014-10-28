{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Data.TreeRegex.Mono where

import Control.Applicative
import GHC.Generics

newtype Fix f = Fix { unFix :: f (Fix f) } deriving Generic

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


data Void

data TreeRegexCapture' k f r where
  EmptyC  :: TreeRegexCapture' k f Void
  AnyC    :: TreeRegexCapture' k f (Fix f)
  InC     :: (f (TreeRegexCapture' k f r)) -> TreeRegexCapture' k f (f r)
  SquareC :: k -> TreeRegexCapture' k f (Fix f)
  ChoiceC :: TreeRegexCapture' k f a -> TreeRegexCapture' k f a -> TreeRegexCapture' k f a
  ConcatC :: (k -> TreeRegexCapture' k f (a -> b)) -> TreeRegexCapture' k f a -> TreeRegexCapture' k f b
  IterC   :: (k -> TreeRegexCapture' k f a) -> TreeRegexCapture' k f [a]
  MapC    :: (a -> b) -> TreeRegexCapture' k f a -> TreeRegexCapture' k f b
  PureC   :: r -> TreeRegexCapture' k f r

newtype TreeRegexCapture f r = TreeRegexCapture { unTreeRegexCapture :: forall k. TreeRegexCapture' k f r }

capture :: (Generic1 f, CaptureG' (Rep1 f))
        => TreeRegexCapture f r -> Fix f -> Maybe r
capture r t = capture' (unTreeRegexCapture r) t 0 []

capture' :: (Generic1 f, CaptureG' (Rep1 f))
         => TreeRegexCapture' Integer f r
         -> Fix f
         -> Integer  -- Fresh variable generator
         -> [(Integer, forall s. TreeRegexCapture' Integer f s)]  -- Ongoing substitution
         -> Maybe r
capture' EmptyC          _ _ _ = Nothing
capture' AnyC            f _ _ = Just f
capture' (InC r)   (Fix t) i s = to1 <$> captureG' (from1 r) (from1 t) i s
capture' (SquareC n)     t i s = let Just r = lookup n s in capture' r t i s
capture' (ChoiceC r1 r2) t i s = capture' r1 t i s <|> capture' r2 t i s
-- capture' (ConcatC r1 r2) t i s = capture' (r1 i) t (i+1) ((i,r2):s)
capture' (IterC r)       t i s = capture' (ConcatC (\k -> MapC (:) (r k)) (IterC r)) t i s
capture' (MapC f r)      t i s = f <$> capture' r t i s
capture' (PureC r)       t i s = Just r

class CaptureG' f where
  captureG' :: (Generic1 g, CaptureG' (Rep1 g))
            => f (TreeRegexCapture' Integer g r) -> f (Fix g)
            -> Integer -> [(Integer, forall r. TreeRegexCapture' Integer g r)]
            -> Maybe (f r)

instance CaptureG' U1 where
  captureG' _ _ _ _ = Just U1

instance CaptureG' Par1 where
  captureG' (Par1 r) (Par1 t) i s = Par1 <$> capture' r t i s

instance Eq c => CaptureG' (K1 i c) where
  captureG' (K1 r) (K1 t) _ _ | r == t    = K1 <$> Just t
                              | otherwise = Nothing

instance CaptureG' f => CaptureG' (Rec1 f) where
  captureG' (Rec1 r) (Rec1 t) i s = Rec1 <$> captureG' r t i s

instance CaptureG' a => CaptureG' (M1 i c a) where
  captureG' (M1 r) (M1 t) i s = M1 <$> captureG' r t i s

instance (CaptureG' a, CaptureG' b) => CaptureG' (a :+: b) where
  captureG' (L1 r) (L1 t) i s = L1 <$> captureG' r t i s
  captureG' (R1 r) (R1 t) i s = R1 <$> captureG' r t i s
  captureG' _      _      _ _ = Nothing

instance (CaptureG' a, CaptureG' b) => CaptureG' (a :*: b) where
  captureG' (r1 :*: r2) (t1 :*: t2) i s = (:*:) <$> captureG' r1 t1 i s <*> captureG' r2 t2 i s

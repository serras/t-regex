{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PolyKinds #-}
module Data.TreeRegex.Mono where

import Control.Applicative
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as M
import GHC.Generics
import Unsafe.Coerce -- :(

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


-- PARSER COMBINATORS STYLE
-- ========================

data Void

data TreeRegexCapture' (k :: * -> *) f r where
  EmptyC    :: TreeRegexCapture' k f Void
  AnyC      :: TreeRegexCapture' k f (Fix f)
  InC       :: f (TreeRegexCapture' k f r) -> TreeRegexCapture' k f (f r)
  SquareC   :: k r -> TreeRegexCapture' k f r
  -- Almost an Alternative: we have fmap, pure, <|> and sort of <*>
  ChoiceC   :: TreeRegexCapture' k f a -> TreeRegexCapture' k f a -> TreeRegexCapture' k f a
  ConcatC   :: (k a -> TreeRegexCapture' k f ([a] -> b)) -> TreeRegexCapture' k f a -> TreeRegexCapture' k f b
  -- DeepIterC :: (k a -> TreeRegexCapture' k f ([a] -> a)) -> TreeRegexCapture' k f [a]
  PureC     :: r -> TreeRegexCapture' k f r
  MapC      :: (a -> b) -> TreeRegexCapture' k f a -> TreeRegexCapture' k f b

newtype TreeRegexCapture f r = TreeRegexCapture { unTreeRegexCapture :: forall k. TreeRegexCapture' k f r }

tupleC :: (k a -> TreeRegexCapture' k f b) -> TreeRegexCapture' k f a -> TreeRegexCapture' k f (b,[a])
tupleC r s = ConcatC (\k -> MapC (\x xs -> (x,xs)) (r k)) s

-- Good for matching, but not for capturing!
shallowIterC :: (b -> [a] -> a) -> (k a -> TreeRegexCapture' k f b) -> TreeRegexCapture' k f a
shallowIterC f r = ConcatC (\k -> MapC f (r k)) (shallowIterC f r)

shallowFixC :: (k a -> TreeRegexCapture' k f ([a] -> a)) -> TreeRegexCapture' k f a
shallowFixC = shallowIterC id  -- Or simply: iterC r = Concat r (fixC r)

traverseC :: (b -> a) -> (k a -> TreeRegexCapture' k f b) -> TreeRegexCapture' k f [a]
traverseC f r = MapC snd $ traverseC' f r
  where traverseC' :: (b -> a) -> (k a -> TreeRegexCapture' k f b) -> TreeRegexCapture' k f (a,[a])
        traverseC' g rx = ConcatC (\k -> MapC (\x xs -> (g x, g x:xs)) (rx k)) (MapC fst $ traverseC' g rx)

listC :: (k a -> TreeRegexCapture' k f a) -> TreeRegexCapture' k f [a]
listC = traverseC id

fixListC :: (k (Fix f) -> TreeRegexCapture' k f (f (Fix f))) -> TreeRegexCapture' k f [Fix f]
fixListC = traverseC Fix

capture :: (Generic1 f, CaptureG' (Rep1 f))
        => TreeRegexCapture f r -> Fix f -> Maybe r
capture r t = fst <$> capture' (unTreeRegexCapture r) t 0 []

data WrappedInt a = W {unW :: Integer}
                  deriving (Eq, Show)

capture' :: (Generic1 f, CaptureG' (Rep1 f))
         => TreeRegexCapture' WrappedInt f r
         -> Fix f
         -> Integer  -- Fresh variable generator
         -> [(Integer, forall s. TreeRegexCapture' WrappedInt f s)]  -- Ongoing substitution
         -> Maybe (r, [(Integer, [forall s. s])])
capture' EmptyC          _ _ _ = Nothing
capture' AnyC            f _ _ = Just (f, [])
capture' (InC r)   (Fix t) i s = applyFst to1 <$> captureG' (from1 r) (from1 t) i s
capture' (SquareC (W n)) t i s = let Just r = lookup n s in case capture' r t i s of
                                   Nothing -> Nothing
                                   Just (e, inner) -> Just (e, mix [(n, [unsafeCoerce e])] inner)
capture' (ChoiceC r1 r2) t i s = case (capture' r1 t i s, capture' r2 t i s) of
                                   (Just e1, _)  -> Just e1
                                   (Nothing, e2) -> e2
capture' (ConcatC r1 r2) t i s = case capture' (r1 (W i)) t (i+1) ((i,unsafeCoerce r2):s) of
                                   Nothing -> Nothing
                                   Just (f, inner) -> case lookup i inner of
                                     Nothing -> Just (f [], remove i inner)
                                     Just ls -> Just (f (reverse (unsafeCoerce ls)), remove i inner)
capture' (MapC f r)      t i s = applyFst f <$> capture' r t i s
capture' (PureC r)       _ _ _ = Just (r, [])

mix :: (Eq a, Show a) => [(a,[b])] -> [(a,[b])] -> [(a,[b])]
mix lst1 lst2 = foldr mixElem lst1 lst2
  where mixElem (n,p) [] = [(n,p)]
        mixElem (n,p) ((m,q):rest) | n == m    = (n, p ++ q) : rest
                                   | otherwise = (m,p) : mixElem (n,p) rest

remove :: Eq a => a -> [(a,b)] -> [(a,b)]
remove _ [] = []
remove e ((x,y):xs) | e == x    = xs
                    | otherwise = (x,y):remove e xs

applyFst :: (a -> b) -> (a, c) -> (b, c)
applyFst f (x, y) = (f x, y)

class CaptureG' f where
  captureG' :: (Generic1 g, CaptureG' (Rep1 g))
            => f (TreeRegexCapture' WrappedInt g r) -> f (Fix g)
            -> Integer -> [(Integer, forall s. TreeRegexCapture' WrappedInt g s)]
            -> Maybe (f r, [(Integer, [forall s. s])])

instance CaptureG' U1 where
  captureG' _ _ _ _ = Just (U1, [])

instance CaptureG' Par1 where
  captureG' (Par1 r) (Par1 t) i s = applyFst Par1 <$> capture' r t i s

instance Eq c => CaptureG' (K1 i c) where
  captureG' (K1 r) (K1 t) _ _ | r == t    = Just (K1 t, [])
                              | otherwise = Nothing

instance CaptureG' f => CaptureG' (Rec1 f) where
  captureG' (Rec1 r) (Rec1 t) i s = applyFst Rec1 <$> captureG' r t i s

instance CaptureG' a => CaptureG' (M1 i c a) where
  captureG' (M1 r) (M1 t) i s = applyFst M1 <$> captureG' r t i s

instance (CaptureG' a, CaptureG' b) => CaptureG' (a :+: b) where
  captureG' (L1 r) (L1 t) i s = applyFst L1 <$> captureG' r t i s
  captureG' (R1 r) (R1 t) i s = applyFst R1 <$> captureG' r t i s
  captureG' _      _      _ _ = Nothing

instance (CaptureG' a, CaptureG' b) => CaptureG' (a :*: b) where
  captureG' (r1 :*: r2) (t1 :*: t2) i s = case (captureG' r1 t1 i s, captureG' r2 t2 i s) of
                                            (Just (e1,c1), Just (e2,c2)) -> Just (e1 :*: e2, mix c1 c2)
                                            _                            -> Nothing


-- REGEX CAPTURE STYLE
-- ===================

data TreeRegexNew' k c f where
  EmptyN   :: TreeRegexNew' k c f
  AnyN     :: TreeRegexNew' k c f
  InN      :: f (TreeRegexNew' k c f) -> TreeRegexNew' k c f
  SquareN  :: k -> TreeRegexNew' k c f
  ChoiceN  :: TreeRegexNew' k c f -> TreeRegexNew' k c f -> TreeRegexNew' k c f
  ConcatN  :: (k -> TreeRegexNew' k c f) -> TreeRegexNew' k c f -> TreeRegexNew' k c f
  CaptureN :: c -> TreeRegexNew' k c f -> TreeRegexNew' k c f

newtype TreeRegexNew c f = TreeRegexNew { unTreeRegexNew :: forall k. TreeRegexNew' k c f }

matchN :: (Ord c, Generic1 f, MatchNG' (Rep1 f), Alternative m)
      => TreeRegexNew c f -> Fix f -> Maybe (Map c (m (Fix f)))
matchN r t = matchN' (unTreeRegexNew r) t 0 []

matchN' :: (Ord c, Generic1 f, MatchNG' (Rep1 f), Alternative m)
        => TreeRegexNew' Integer c f
        -> Fix f
        -> Integer  -- Fresh variable generator
        -> [(Integer, TreeRegexNew' Integer c f)]  -- Ongoing substitution
        -> Maybe (Map c (m (Fix f)))
matchN' EmptyN          _ _ _ = Nothing
matchN' AnyN            _ _ _ = Just M.empty
matchN' (InN r)   (Fix t) i s = matchNG' (from1 r) (from1 t) i s
matchN' (SquareN n)     t i s = let Just r = lookup n s in matchN' r t i s
matchN' (ChoiceN r1 r2) t i s = matchN' r1 t i s <|> matchN' r2 t i s
matchN' (ConcatN r1 r2) t i s = matchN' (r1 i) t (i+1) ((i,r2):s)
matchN' (CaptureN c r)  t i s = M.insertWith (<|>) c (pure t) <$> matchN' r t i s

iterN :: (k -> TreeRegexNew' k c f) -> TreeRegexNew' k c f
iterN r = (ConcatN r (iterN r))

class MatchNG' f where
  matchNG' :: (Ord c, Generic1 g, MatchNG' (Rep1 g), Alternative m)
           => f (TreeRegexNew' Integer c g) -> f (Fix g)
           -> Integer -> [(Integer, TreeRegexNew' Integer c g)]
           -> Maybe (Map c (m (Fix g)))

instance MatchNG' U1 where
  matchNG' _ _ _ _ = Just M.empty

instance MatchNG' Par1 where
  matchNG' (Par1 r) (Par1 t) = matchN' r t

instance Eq c => MatchNG' (K1 i c) where
  matchNG' (K1 r) (K1 t) _ _ = do guard (r == t)
                                  return M.empty

instance MatchNG' f => MatchNG' (Rec1 f) where
  matchNG' (Rec1 r) (Rec1 t) = matchNG' r t

instance MatchNG' a => MatchNG' (M1 i c a) where
  matchNG' (M1 r) (M1 t) = matchNG' r t

instance (MatchNG' a, MatchNG' b) => MatchNG' (a :+: b) where
  matchNG' (L1 r) (L1 t) i s = matchNG' r t i s
  matchNG' (R1 r) (R1 t) i s = matchNG' r t i s
  matchNG' _      _      _ _ = Nothing

instance (MatchNG' a, MatchNG' b) => MatchNG' (a :*: b) where
  matchNG' (r1 :*: r2) (t1 :*: t2) i s = M.unionWith (<|>) <$> matchNG' r1 t1 i s <*> matchNG' r2 t2 i s

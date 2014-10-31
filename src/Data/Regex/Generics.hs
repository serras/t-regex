{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Regex.Generics (
  Regex(Regex),
  Regex'(Inject),
  empty_, none,
  any_,
  inj,
  square, var, (!),
  choice, (<||>),
  concat_, (<.>),
  iter, (^*),
  capture, (<<-),
  matches, match,
  Fix(..),
  with
) where

import Control.Applicative
import Control.Monad (guard)
import Data.Functor.Foldable
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isJust)
import GHC.Generics

data Regex' k c f
  = Empty
  | Any
  | Inject (f (Regex' k c f))
  | Square k
  | Choice (Regex' k c f) (Regex' k c f)
  | Concat (k -> Regex' k c f) (Regex' k c f)
  | Capture c (Regex' k c f)
newtype Regex c f = Regex { unRegex :: forall k. Regex' k c f }

empty_ :: Regex' k c f
empty_ = Empty

none :: Regex' k c f
none = empty_

any_ :: Regex' k c f
any_ = Any

inj :: f (Regex' k c f) -> Regex' k c f
inj = Inject

square :: k -> Regex' k c f
square = Square

var :: k -> Regex' k c f
var = square

(!) :: k -> Regex' k c f
(!) = square

choice :: Regex' k c f -> Regex' k c f -> Regex' k c f
choice = Choice

infixl 3 <||>
(<||>) :: Regex' k c f -> Regex' k c f -> Regex' k c f
(<||>) = choice

concat_ :: (k -> Regex' k c f) -> Regex' k c f -> Regex' k c f
concat_ = Concat

(<.>) :: (k -> Regex' k c f) -> Regex' k c f -> Regex' k c f
(<.>) = concat_

iter :: (k -> Regex' k c f) -> Regex' k c f
iter r = Concat r (iter r)

(^*) :: (k -> Regex' k c f) -> Regex' k c f
(^*) = iter

capture :: c -> Regex' k c f -> Regex' k c f
capture = Capture

infixl 4 <<-
(<<-) :: c -> Regex' k c f -> Regex' k c f
(<<-) = capture

matches :: forall c f. (Ord c, Generic1 f, MatchG (Rep1 f))
        => Regex c f -> Fix f -> Bool
r `matches` t = isJust $ (match r t :: Maybe (Map c [Fix f]))

match :: (Ord c, Generic1 f, MatchG (Rep1 f), Alternative m)
      => Regex c f -> Fix f -> Maybe (Map c (m (Fix f)))
match r t = match' (unRegex r) t 0 []

match' :: (Ord c, Generic1 f, MatchG (Rep1 f), Alternative m)
       => Regex' Integer c f
       -> Fix f
       -> Integer  -- Fresh variable generator
       -> [(Integer, Regex' Integer c f)]  -- Ongoing substitution
       -> Maybe (Map c (m (Fix f)))
match' Empty            _ _ _ = Nothing
match' Any              _ _ _ = Just M.empty
match' (Inject r) (Fix t) i s = matchG (from1 r) (from1 t) i s
match' (Square n)       t i s = let Just r = lookup n s in match' r t i s
match' (Choice r1 r2)   t i s = match' r1 t i s <|> match' r2 t i s
match' (Concat r1 r2)   t i s = match' (r1 i) t (i+1) ((i,r2):s)
match' (Capture c r)    t i s = M.insertWith (<|>) c (pure t) <$> match' r t i s

class MatchG f where
  matchG :: (Ord c, Generic1 g, MatchG (Rep1 g), Alternative m)
         => f (Regex' Integer c g) -> f (Fix g)
         -> Integer -> [(Integer, Regex' Integer c g)]
         -> Maybe (Map c (m (Fix g)))

instance MatchG U1 where
  matchG _ _ _ _ = Just M.empty

instance MatchG Par1 where
  matchG (Par1 r) (Par1 t) = match' r t

instance Eq c => MatchG (K1 i c) where
  matchG (K1 r) (K1 t) _ _ = do guard (r == t)
                                return M.empty

instance MatchG f => MatchG (Rec1 f) where
  matchG (Rec1 r) (Rec1 t) = matchG r t

instance MatchG a => MatchG (M1 i c a) where
  matchG (M1 r) (M1 t) = matchG r t

instance (MatchG a, MatchG b) => MatchG (a :+: b) where
  matchG (L1 r) (L1 t) i s = matchG r t i s
  matchG (R1 r) (R1 t) i s = matchG r t i s
  matchG _      _      _ _ = Nothing

instance (MatchG a, MatchG b) => MatchG (a :*: b) where
  matchG (r1 :*: r2) (t1 :*: t2) i s = M.unionWith (<|>) <$> matchG r1 t1 i s <*> matchG r2 t2 i s


class With f fn r | fn -> r where
  with :: fn -> Fix f -> Maybe r

instance (Generic1 f, MatchG (Rep1 f), Ord c)
         => With f (Regex c f) () where
  with r t = (const ()) <$> (match r t :: Maybe (Map c [Fix f]))
  
instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Regex Integer f) [Fix f] where
  with r t = M.findWithDefault [] 1 <$> match (r 1) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Regex Integer f)
                   ([Fix f], [Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m))
             <$> match (r 1 2) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m, M.findWithDefault [] 3 m))
             <$> match (r 1 2 3) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m,
                     M.findWithDefault [] 3 m, M.findWithDefault [] 4 m))
             <$> match (r 1 2 3 4) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m, M.findWithDefault [] 3 m,
                     M.findWithDefault [] 4 m, M.findWithDefault [] 5 m))
             <$> match (r 1 2 3 4 5) t

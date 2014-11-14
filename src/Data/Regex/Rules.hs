{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module Data.Regex.Rules (
  Action, Rule, Grammar,
  eval,
  (->>>), (->>),
  this, at,
  inh, syn,
  rule, check
) where

import Control.Applicative
import Control.Monad.State
import Data.Foldable (foldMap)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.Generics

type Action  c (f :: * -> *) inh syn = Fix f -> inh -> Map c syn -> (Bool, Map c inh, syn)
type Rule    c (f :: * -> *) inh syn = (Regex c f, Action c f inh syn)
type Grammar c (f :: * -> *) inh syn = [Rule c f inh syn]

eval :: (Ord c, Matchable f, Monoid syn)
     => Grammar c f inh syn -> inh -> Fix f -> syn
eval grammar down term = fromJust $ foldr (<|>) empty $ map evalRule grammar
  where evalRule (regex, action) = do  -- Maybe monad
          (captures :: Map c [Fix f]) <- match regex term
          let (ok, children, up) = action term down $ M.mapWithKey evalList captures
              evalList k = foldMap $ eval grammar (children M.! k)
          guard ok
          return up

data ActionState c inh syn = ActionState { _apply :: Bool, _this :: (inh, syn), _rest :: Map c (inh, syn) }

this :: Functor f => ((inh,syn) -> f (inh,syn))
                  -> ActionState c inh syn -> f (ActionState c inh syn)
this go (ActionState ok th rs) = (\x -> ActionState ok x rs) <$> go th
{-# INLINE this #-}

at :: (Ord c, Functor f) => c -> ((inh,syn) -> f (inh,syn))
                         -> ActionState c inh syn -> f (ActionState c inh syn)
at k go (ActionState ok th rs) = (\x -> ActionState ok th (M.insert k x rs)) <$> go (rs M.! k)
{-# INLINE at #-}

inh :: Functor f => (inh -> f inh) -> (inh, syn) -> f (inh, syn)
inh go (i,s) = (\x -> (x,s)) <$> go i
{-# INLINE inh #-}

syn :: Functor f => (syn -> f syn) -> (inh, syn) -> f (inh, syn)
syn go (i,s) = (\x -> (i,x)) <$> go s
{-# INLINE syn #-}


stateToAction :: (Ord c, Monoid syn)
              => [c] -> (Fix f -> State (ActionState c inh syn) ())
              -> Action c f inh syn
stateToAction nodes st term down up =
  let initialRest = M.fromList $ map (\c -> (c, (down, up M.! c))) nodes  -- down copy rule
      initial = ActionState True (down, mempty) initialRest  -- start with empty
      ActionState ok th rs = execState (st term) initial
   in (ok, M.map fst rs, snd th)

(->>>) :: Monoid syn
       => (forall k. Regex' k Integer f) -> (Fix f -> State (ActionState Integer inh syn) ())
       -> [Integer] -> Rule Integer f inh syn
(rx ->>> st) nodes = (Regex rx, stateToAction nodes st)

(->>) :: Monoid syn
      => (forall k. Regex' k Integer f) -> State (ActionState Integer inh syn) ()
      -> [Integer] -> Rule Integer f inh syn
rx ->> st = rx ->>> const st

check :: Bool -> State (ActionState Integer inh syn) ()
check ok = modify (\(ActionState _ th rs) -> ActionState ok th rs)


class RuleBuilder (f :: * -> *) inh syn fn r | fn -> r, r -> f inh syn where
  rule :: fn -> r

instance Monoid syn =>
  RuleBuilder f inh syn
              ([Integer] -> Rule Integer f inh syn)
              (Rule Integer f inh syn) where
  rule r = r []

instance Monoid syn =>
  RuleBuilder f inh syn
              (Integer -> [Integer] -> Rule Integer f inh syn)
              (Rule Integer f inh syn) where
  rule r = r 1 [1]

instance Monoid syn =>
  RuleBuilder f inh syn
              (Integer -> Integer -> [Integer] -> Rule Integer f inh syn)
              (Rule Integer f inh syn) where
  rule r = r 1 2 [1,2]

instance Monoid syn =>
  RuleBuilder f inh syn
              (Integer -> Integer -> Integer -> [Integer] -> Rule Integer f inh syn) 
              (Rule Integer f inh syn) where
  rule r = r 1 2 3 [1,2,3]

instance Monoid syn =>
  RuleBuilder f inh syn
              (Integer -> Integer -> Integer -> Integer -> [Integer] -> Rule Integer f inh syn) 
              (Rule Integer f inh syn) where
  rule r = r 1 2 3 4 [1,2,3,4]

instance Monoid syn =>
  RuleBuilder f inh syn
              (Integer -> Integer -> Integer -> Integer -> Integer -> [Integer] -> Rule Integer f inh syn) 
              (Rule Integer f inh syn) where
  rule r = r 1 2 3 4 5 [1,2,3,4,5]

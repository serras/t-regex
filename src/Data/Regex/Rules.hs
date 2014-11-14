{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
-- | Attribute grammars with regular expression matching.
module Data.Regex.Rules (
  -- * Basic blocks
  Action, Rule, Grammar,
  eval,
  -- * Nice syntax for defining rules
  rule,
  -- ** Combinators
  check,
  (->>>), (->>),
  -- ** Special lenses
  this, at,
  inh, syn
) where

import Control.Applicative
import Control.Monad.State
import Data.Foldable (foldMap)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.Generics

-- | Actions create new inherited attributes for their children,
--   and synthesized attribute for its own node, from the synthesized
--   attributes of children and the inheritance from its parent.
--   Additionally, actions may include an explicit backtrack.
type Action  c (f :: * -> *) inh syn = Fix f -> inh -> Map c syn -> (Bool, Map c inh, syn)
-- | A rule comprises the regular expression to match
--   and the action to execute if successful.
type Rule    c (f :: * -> *) inh syn = (Regex c f, Action c f inh syn)
-- | A grammar is simply a list of rules.
type Grammar c (f :: * -> *) inh syn = [Rule c f inh syn]

-- | Evaluate an attribute grammar over a certain term.
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

-- | Lens for the attributes of the current node. To be used in composition with 'inh' or 'syn'.
this :: Functor f => ((inh,syn) -> f (inh,syn))
                  -> ActionState c inh syn -> f (ActionState c inh syn)
this go (ActionState ok th rs) = (\x -> ActionState ok x rs) <$> go th
{-# INLINE this #-}

-- | Lens the attributes of a child node. To be used in composition with 'inh' or 'syn'.
at :: (Ord c, Functor f) => c -> ((inh,syn) -> f (inh,syn))
                         -> ActionState c inh syn -> f (ActionState c inh syn)
at k go (ActionState ok th rs) = (\x -> ActionState ok th (M.insert k x rs)) <$> go (rs M.! k)
{-# INLINE at #-}

-- | Lens for the inherited attributes of a node.
--   Use only as getter with 'this' and as setter with 'at'.
inh :: Functor f => (inh -> f inh) -> (inh, syn) -> f (inh, syn)
inh go (i,s) = (\x -> (x,s)) <$> go i
{-# INLINE inh #-}

-- | Lens the inherited synthesized attributes of a node.
--   Use only as setter with 'this' and as getter with 'at'.
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

-- | Separates matching and attribute calculation on a rule.
--   The action should take as extra parameter the node which was matched.
(->>>) :: Monoid syn
       => (forall k. Regex' k Integer f) -> (Fix f -> State (ActionState Integer inh syn) ())
       -> [Integer] -> Rule Integer f inh syn
(rx ->>> st) nodes = (Regex rx, stateToAction nodes st)

-- | Separates matching and attribute calculation on a rule.
(->>) :: Monoid syn
      => (forall k. Regex' k Integer f) -> State (ActionState Integer inh syn) ()
      -> [Integer] -> Rule Integer f inh syn
rx ->> st = rx ->>> const st

-- | Makes the attribute calculation fail if the condition is false.
--   This function can be used to add extra conditions over whether
--   a certain rule should be applied (a bit like guards).
check :: Bool -> State (ActionState Integer inh syn) ()
check ok = modify (\(ActionState _ th rs) -> ActionState ok th rs)


class RuleBuilder (f :: * -> *) inh syn fn r | fn -> r, r -> f inh syn where
  -- | Converts a rule description into an actual 'Rule'.
  --   Its use must follow this pattern:
  --
  --     * A block of lambda-bound variables will introduce the capture names,
  --     * A tree regular expression to match should capture using the previous names,
  --     * After '->>>' or '->>', the state calculation should proceed.
  --
  --   > rule $ \c1 c2 ->
  --   >   regex ... c1 <<- ... c2 <<- ... ->> do
  --   >     at c2 . inh .= ...          -- Set inherited for children
  --   >     c1Syn <- use (at c1 . syn)  -- Get synthesized from children
  --   >     this . syn  .= ...          -- Set upwards synthesized attributes
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

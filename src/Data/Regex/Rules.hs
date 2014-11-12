{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Regex.Rules (
  Action, Rule, Grammar,
  eval,
  (!!)
) where

import Control.Applicative
import Data.Foldable (foldMap)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.Generics

type Action  c (f :: * -> *) inh syn = Fix f -> inh -> Map c syn -> (Map c inh, syn)
type Rule    c (f :: * -> *) inh syn = (Regex c f, Action c f inh syn)
type Grammar c (f :: * -> *) inh syn = [Rule c f inh syn]

eval :: (Ord c, Matchable f, Monoid syn)
     => Grammar c f inh syn -> inh -> Fix f -> syn
eval grammar inh term = fromJust $ foldr (<|>) empty $ map evalRule grammar
  where evalRule (regex, action) = do  -- Maybe monad
          (captures :: Map c [Fix f]) <- match regex term
          let (children, syn) = action term inh $ M.mapWithKey evalList captures
              evalList k = foldMap $ eval grammar (children M.! k)
          return syn

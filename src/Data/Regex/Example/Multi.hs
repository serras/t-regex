{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Example of tree regular expressions over
--   a family of regular data types.
--   Click on @Source@ to view the code.
module Data.Regex.Example.Multi (
  -- * Data type definition
  Ty(..), Bis(..), FixOne, FixTwo,
  -- ** Useful pattern synonyms
  pattern NilOne, pattern ConsOne,
  pattern NilTwo, pattern ConsTwo,
  -- ** Some 'Bis' values
  aBis1, aBis2,
  -- * Tree regular expressions
  -- ** Some stand-alone expressions
  rBis1, rBis2, rBis3, rBis4,
  -- ** Using 'with' views
  cBis1, eBis1,
  -- ** Using the 'mrx' quasi-quoter
  eBis2,
  -- * Grammars
  grammar1
) where

import Control.Lens hiding (at, (#), children)
import Data.MultiGenerics
import Data.Regex.MultiGenerics
import Data.Regex.MultiRules
import Data.Regex.TH

data Ty = One | Two

data Bis f ix where
  NilOne'  :: Bis f One
  ConsOne' :: Int  -> f Two -> Bis f One
  NilTwo'  :: Bis f Two
  ConsTwo' :: Char -> f One -> Bis f Two

type FixOne = Fix Bis One
type FixTwo = Fix Bis Two

instance ShowM (Fix Bis) where
  showM (Fix NilOne')        = "NilOne"
  showM (Fix (ConsOne' n r)) = "(ConsOne " ++ show n ++ " " ++ showM r ++ ")"
  showM (Fix NilTwo')        = "NilTwo"
  showM (Fix (ConsTwo' c r)) = "(ConsTwo " ++ show c ++ " " ++ showM r ++ ")"
instance Show (Fix Bis One) where
  show = showM
instance Show (Fix Bis Two) where
  show = showM

pattern NilOne       = Fix NilOne'
pattern ConsOne x xs = Fix (ConsOne' x xs)
pattern NilTwo       = Fix NilTwo'
pattern ConsTwo x xs = Fix (ConsTwo' x xs)

-- | Implementation of 'Generic1m' for 'Bis'.
--   This is required to use tree regular expressions.
instance Generic1m Bis where
  type Rep1m Bis =    Tag1m U1m One
                 :++: Tag1m (K1m () Int  :**: Par1m Two) One
                 :++: Tag1m U1m Two
                 :++: Tag1m (K1m () Char :**: Par1m One) Two

  from1k NilOne' = L1m $ Tag1m U1m
  from1k (ConsOne' x xs) = R1m $ L1m $ Tag1m (K1m x :**: Par1m xs)
  from1k NilTwo' = R1m $ R1m $ L1m $ Tag1m U1m
  from1k (ConsTwo' x xs) = R1m $ R1m $ R1m $ Tag1m (K1m x :**: Par1m xs)

  to1k (L1m (Tag1m U1m)) = NilOne'
  to1k (R1m (L1m (Tag1m (K1m x :**: Par1m xs)))) = ConsOne' x xs
  to1k (R1m (R1m (L1m (Tag1m U1m)))) = NilTwo'
  to1k (R1m (R1m (R1m (Tag1m (K1m x :**: Par1m xs))))) = ConsTwo' x xs

aBis1 :: FixOne
aBis1 = NilOne

aBis2 :: FixOne
aBis2 = ConsOne 1 (ConsTwo 'a' NilOne)

rBis1 :: Regex (Wrap Char) Bis One
rBis1 = Regex $ capture ('a'?) $ inj NilOne'

rBis2 :: Regex c Bis One
rBis2 = Regex $ inj (ConsOne' 2 (inj NilTwo'))

rBis3 :: Regex c Bis One
rBis3 = Regex $ inj (ConsOne' 2 (inj (ConsTwo' 'a' (inj NilOne'))))

rBis4 :: Regex c Bis One
rBis4 = Regex $ inj NilOne' <||> inj NilOne'

cBis1 :: Wrap Integer One -> Regex (Wrap Integer) Bis One
cBis1 x = Regex $ x <<- inj NilOne'


eBis1 :: FixOne -> [FixOne]
eBis1 (with cBis1 -> Just x) = x
eBis1 _                      = error "What?"

eBis2 :: FixOne -> [FixOne]
eBis2 [mrx| (x :: One) <<- inj NilOne' |] = x

grammar1 :: IndexIndependentGrammar (Wrap Integer) Bis () String
grammar1 = [
    rule0 $ 
      inj NilOne' ->> do
        this.syn_ .= "NilOne"
  , rule $ \x ->
      inj (ConsOne' 1 (x <<- any_)) ->> do
        s <- use (at x . syn_)
        this.syn_ .= "Special - " ++ s
  , rule $ \x ->
      inj (ConsOne' __ (x <<- any_)) ->>> \(ConsOne n _) -> do
        s <- use (at x . syn_)
        this.syn_ .= show n ++ " - " ++ s
  , rule0 $ 
      inj NilTwo' ->> do
        this.syn_ .= "NilTwo"
  , rule $ \x ->
      inj (ConsTwo' __ (x <<- any_)) ->>> \(ConsTwo n _) -> do
        s <- use (at x . syn_)
        this.syn_ .= show n ++ " - " ++ s
  ]

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.TreeRegex.Example where

import qualified Data.TreeRegex.Mono as M
import qualified Data.TreeRegex.Poly as P
import GHC.Generics

data Tree' f = Leaf' | Branch' Int f f
  deriving Generic1
type Tree = M.Fix Tree'

-- Pattern synonyms for constructors
pattern Leaf = M.Fix Leaf'
pattern Branch n l r = M.Fix (Branch' n l r)

aTree1 :: Tree
aTree1 = Branch 2 (Branch 3 Leaf Leaf) Leaf

aTree2 :: Tree
aTree2 = Branch 2 (Branch 2 Leaf Leaf) Leaf

-- Pattern synonyms for regexes
pattern LeafR = M.In Leaf'
pattern BranchR n l r = M.In (Branch' n l r)

rTree1 :: M.TreeRegex Tree'
rTree1 = M.TreeRegex $ BranchR 2 M.Any LeafR

rTree2 :: M.TreeRegex Tree'
rTree2 = M.TreeRegex $ BranchR 4 M.Any M.Any

rTree3 :: M.TreeRegex Tree'
rTree3 = M.TreeRegex $ M.Iter (\k -> BranchR 2 (M.Square k) (M.Square k) `M.Choice` LeafR)

data Ty = One | Two

data Bis f ix where
  NilOne'  :: Bis f One
  ConsOne' :: Int -> f Two -> Bis f One
  NilTwo'  :: Bis f Two
  ConsTwo' :: Char -> f One -> Bis f Two

type FixOne = P.Fix Bis One
type FixTwo = P.Fix Bis Two

pattern NilOne       = P.Fix NilOne'
pattern ConsOne x xs = P.Fix (ConsOne' x xs)
pattern NilTwo       = P.Fix NilTwo'
pattern ConsTwo x xs = P.Fix (ConsTwo' x xs)

aBis1 :: FixOne
aBis1 = NilOne

aBis2 :: FixOne
aBis2 = ConsOne 1 (ConsTwo 'a' NilOne)

{-
rBis1 :: P.TreeRegex Bis One
rBis1 = P.TreeRegex $ P.In NilOne'

rBis2 :: P.TreeRegex Bis One
rBis2 = P.TreeRegex $ P.In (ConsOne' 2 (P.In NilTwo'))

rBis3 :: P.TreeRegex Bis One
rBis3 = P.TreeRegex $ P.In (ConsOne' 2 (P.In (ConsTwo' 'a' (P.In NilOne'))))
-}

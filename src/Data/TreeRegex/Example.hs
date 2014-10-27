{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.TreeRegex.Example where

import qualified Data.TreeRegex.Mono as M
import qualified Data.TreeRegex.Poly as P
import GHC.Generics
import Data.GenericK

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

data Bis ix f where
  NilOne'  :: Bis One f
  ConsOne' :: Int -> f Two -> Bis One f
  NilTwo'  :: Bis Two f
  ConsTwo' :: Char -> f One -> Bis Two f

type FixOne = P.Fix Bis One
type FixTwo = P.Fix Bis Two

pattern NilOne       = P.F NilOne'
pattern ConsOne x xs = P.F (ConsOne' x xs)
pattern NilTwo       = P.F NilTwo'
pattern ConsTwo x xs = P.F (ConsTwo' x xs)

aBis1 :: FixOne
aBis1 = NilOne

aBis2 :: FixOne
aBis2 = ConsOne 1 (ConsTwo 'a' NilOne)

rBis1 :: P.TreeRegex Bis One
rBis1 = P.TreeRegex $ P.In NilOne'

rBis2 :: P.TreeRegex Bis One
rBis2 = P.TreeRegex $ P.In (ConsOne' 2 (P.In NilTwo'))

rBis3 :: P.TreeRegex Bis One
rBis3 = P.TreeRegex $ P.In (ConsOne' 2 (P.In (ConsTwo' 'a' (P.In NilOne'))))

rBis4 :: P.TreeRegex Bis One
rBis4 = P.TreeRegex $ P.In NilOne' `P.Choice` P.In NilOne'


instance Generic1k Bis where
  type Rep1k Bis =    Tag1k U1k One
                 :++: Tag1k (K1k () Int  :**: Par1k Two) One
                 :++: Tag1k U1k Two
                 :++: Tag1k (K1k () Char :**: Par1k One) Two

  from1k NilOne' = L1k $ Tag1k U1k
  from1k (ConsOne' x xs) = R1k $ L1k $ Tag1k (K1k x :**: Par1k xs)
  from1k NilTwo' = R1k $ R1k $ L1k $ Tag1k U1k
  from1k (ConsTwo' x xs) = R1k $ R1k $ R1k $ Tag1k (K1k x :**: Par1k xs)

  to1k (L1k (Tag1k U1k)) = NilOne'
  to1k (R1k (L1k (Tag1k (K1k x :**: Par1k xs)))) = ConsOne' x xs
  to1k (R1k (R1k (L1k (Tag1k U1k)))) = NilTwo'
  to1k (R1k (R1k (R1k (Tag1k (K1k x :**: Par1k xs))))) = ConsTwo' x xs

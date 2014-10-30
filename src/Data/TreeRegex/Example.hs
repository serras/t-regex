{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.TreeRegex.Example where

import qualified Data.TreeRegex.Mono  as M
import qualified Data.TreeRegex.Multi as P
import Data.Typeable
import GHC.Generics
import Data.MultiGenerics

data Tree' f = Leaf' | Branch' Int f f
  deriving (Generic1, Show, Typeable)
type Tree = M.Fix Tree'

instance Show Tree where
  show (M.Fix Leaf') = "Leaf"
  show (M.Fix (Branch' n t1 t2)) = "(Branch " ++ show n ++ " " ++ show t1 ++ " " ++ show t2 ++ ")"

-- Pattern synonyms for constructors
pattern Leaf = M.Fix Leaf'
pattern Branch n l r = M.Fix (Branch' n l r)

aTree1 :: Tree
aTree1 = Branch 2 (Branch 3 Leaf Leaf) Leaf

aTree2 :: Tree
aTree2 = Branch 2 (Branch 2 Leaf Leaf) Leaf

aTree3 :: Tree
aTree3 = Branch 2 Leaf Leaf

-- Pattern synonyms for regexes
pattern LeafR = M.In Leaf'
pattern BranchR n l r = M.In (Branch' n l r)

rTree1 :: M.TreeRegex Tree'
rTree1 = M.TreeRegex $ BranchR 2 M.Any LeafR

rTree2 :: M.TreeRegex Tree'
rTree2 = M.TreeRegex $ BranchR 4 M.Any M.Any

rTree3 :: M.TreeRegex Tree'
rTree3 = M.TreeRegex $ M.Iter (\k -> BranchR 2 (M.Square k) (M.Square k) `M.Choice` LeafR)

-- Pattern synonyms for capturing regexes
-- They do not work :(
-- pattern LeafC = M.InC Leaf'
-- pattern BranchC n l r = M.InC (Branch' n l r)

rTreeC1 :: M.TreeRegexCapture Tree' [Tree]
rTreeC1 = M.TreeRegexCapture $ M.fixListC (\k -> M.InC (Branch' 2 (M.SquareC k) (M.SquareC k)) `M.ChoiceC` (M.InC Leaf'))

rTreeN1 :: M.TreeRegexNew String Tree'
rTreeN1 = M.TreeRegexNew $
            M.iterN $ \k ->
              M.CaptureN "x" $
                M.InN (Branch' 2 (M.SquareN k) (M.SquareN k))
                `M.ChoiceN` (M.InN Leaf')

data Ty = One | Two

data Bis f ix where
  NilOne'  :: Bis f One
  ConsOne' :: Int  -> f Two -> Bis f One
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

rBis1 :: P.TreeRegex Bis One
rBis1 = P.TreeRegex $ P.In NilOne'

rBis2 :: P.TreeRegex Bis One
rBis2 = P.TreeRegex $ P.In (ConsOne' 2 (P.In NilTwo'))

rBis3 :: P.TreeRegex Bis One
rBis3 = P.TreeRegex $ P.In (ConsOne' 2 (P.In (ConsTwo' 'a' (P.In NilOne'))))

rBis4 :: P.TreeRegex Bis One
rBis4 = P.TreeRegex $ P.In NilOne' `P.Choice` P.In NilOne'

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

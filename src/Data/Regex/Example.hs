{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
module Data.Regex.Example where

import Data.Regex.Generics
import GHC.Generics

data Tree' f = Leaf' | Branch' Int f f
  deriving (Generic1, Show)
type Tree = Fix Tree'

-- Pattern synonyms for constructors
pattern Leaf = Fix Leaf'
pattern Branch n l r = Fix (Branch' n l r)

instance Show Tree where
  show (Fix Leaf') = "Leaf"
  show (Fix (Branch' n t1 t2)) = "(Branch " ++ show n ++ " " ++ show t1 ++ " " ++ show t2 ++ ")"

aTree1 :: Tree
aTree1 = Branch 2 (Branch 3 Leaf Leaf) Leaf

aTree2 :: Tree
aTree2 = Branch 2 (Branch 2 Leaf Leaf) Leaf

aTree3 :: Tree
aTree3 = Branch 2 Leaf Leaf

rTree1 :: Regex String Tree'
rTree1 = Regex $
           iter $ \k ->
             capture "x" $
                    inj (Branch' 2 (square k) (square k))
               <||> inj Leaf'

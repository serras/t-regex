{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
module Data.TreeRegex.Example where

import Data.TreeRegex.Mono
import GHC.Generics

data Tree f = Leaf | Branch Int f f
  deriving Generic1

leaf :: Fix Tree
leaf = Fix Leaf

branch :: Int -> Fix Tree -> Fix Tree -> Fix Tree
branch n l r = Fix (Branch n l r)

aTree1 :: Fix Tree
aTree1 = branch 2 (branch 3 leaf leaf) leaf

aTree2 :: Fix Tree
aTree2 = branch 2 (branch 2 leaf leaf) leaf

rTree1 :: MonoRegex Tree
rTree1 = MonoRegex $ In (Branch 2 Any (In Leaf))

rTree2 :: MonoRegex Tree
rTree2 = MonoRegex $ In (Branch 4 Any Any)

rTree3 :: MonoRegex Tree
rTree3 = MonoRegex $ Iter (\k -> (In (Branch 2 (Square k) (Square k)) :|: (In Leaf)))


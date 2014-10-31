{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Regex.Example where

import Data.Regex.Generics
import Data.Regex.TH
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

rTree2 :: Integer -> Regex Integer Tree'
rTree2 c = Regex $
             iter $ \k ->
               capture c $
                      inj (Branch' 2 (square k) (square k))
                 <||> inj Leaf'

pattern Branch_ n l r = Inject (Branch' n l r)
pattern Leaf_         = Inject Leaf'

rTree3 :: Integer -> Integer -> Regex Integer Tree'
rTree3 c1 c2 = Regex ( (\k -> c1 <<- Branch_ 2 (k!) (k!) <||> c2 <<- Leaf_)^* )

eWith1 :: Tree -> [Tree]
eWith1 (with rTree2 -> Just e) = e
eWith1 _                       = error "What?"

eWith2 :: Tree -> [Tree]
eWith2 (with rTree3 -> Just (_,e)) = e
eWith2 _                           = error "What?"

eWith2Bis :: Tree -> [Tree]
eWith2Bis $(r [|\x e -> iter $ \k -> x <<- inj (Branch' 2 (k!) (k!)) <||> e <<- (inj Leaf') |]) = e
eWith2Bis _  = error "What?"

eWith3 :: Tree -> [Tree]
eWith3 $(r [| \x y -> x <<- inj Leaf' |]) = _
eWith3 _                                  = error "What?"

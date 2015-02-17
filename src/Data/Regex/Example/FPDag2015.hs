{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Regex.Example.FPDag2015 where

import Control.Applicative
import Data.Regex.Generics
import Data.Regex.TH
import GHC.Generics
import Test.QuickCheck

data List_ a l = Cons_ a l | Nil_ deriving (Show, Generic1)
type List a    = Fix (List_ a)

pattern Cons x xs = Fix (Cons_ x xs)
pattern Nil       = Fix Nil_

instance Arbitrary a => Arbitrary (List a) where
  arbitrary = frequency [ (1, return Nil)
                        , (3, Cons <$> arbitrary <*> arbitrary) ]

oneTwoOrOneThree :: Regex c (List_ Int)
oneTwoOrOneThree = Regex $
  inj $ Cons_ 1 (inj (Cons_ 2 $ inj Nil_) <||> inj (Cons_ 3 $ inj Nil_))

oneTwoThree :: List Char -> Bool
oneTwoThree [rx| iter (\k -> inj (Cons_ 'a' (inj $ Cons_ 'b' (inj $ Cons_ 'c' (k#)))) <||> _last <<- inj Nil_) |] = True
oneTwoThree _ = False

data Tree_ t = Node_ Int t t | Leaf_ Int deriving (Show, Generic1)
type Tree    = Fix Tree_

pattern Node x l r = Fix (Node_ x l r)
pattern Leaf x     = Fix (Leaf_ x)

matchAny :: Regex c Tree_
matchAny = Regex $ any_

topTwo :: Regex c Tree_
topTwo = Regex $ inj (Node_ 2 any_ any_)

shape1 :: Regex c Tree_
shape1 = Regex $
  inj $ Node_ 2 (inj $ Node_ 3 any_ any_)
                (inj $ Node_ 4 any_ any_)

shape2 :: Regex c Tree_
shape2 = Regex $
  inj $ Node_ __ (inj $ Node_ 3 any_ any_)
                 (inj $ Node_ 4 any_ any_)

allTwos :: Regex c Tree_
allTwos = Regex $ iter (\k -> inj (Node_ 2 (var k) (var k)) <||> inj (Leaf_ 2))

allTwosPostfix :: Regex c Tree_
allTwosPostfix = Regex ((\k -> inj (Node_ 2 (k#) (k#)) <||> inj (Leaf_ 2))^*)

allLeaves :: Tree -> [Int]
allLeaves [rx| iter (\k -> inj (Node_ __ (k#) (k#)) <||> leaves <<- inj (Leaf_ __)) |] =
  map (\(Leaf i) -> i) leaves   -- Note this is a Fix-ed element

data Expr_ e = Plus_ e e | Times_ e e | Var_ Int deriving (Show, Generic1)
type Expr    = Fix Expr_

iPlus  a b = inj (Plus_  a b)
iTimes a b = inj (Times_ a b)
iVar   v   = inj (Var_ v)

simplify :: Expr -> Expr
simplify [rx| iPlus  (iVar 0) (x <<- any_) <||> iPlus  (x <<- any_) (iVar 0)
         <||> iTimes (iVar 1) (x <<- any_) <||> iTimes (x <<- any_) (iVar 1) |] = simplify (head x)
simplify x = x
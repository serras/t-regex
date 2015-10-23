{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Example of tree regular expressions over a regular data type.
--   Click on @Source@ to view the code.
module Data.Regex.Example.Mono (
  -- * Data type definitions
  Tree'(..), Tree,
  Rose'(..), Rose,
  -- ** Useful pattern synonyms
  pattern Leaf, pattern Branch,
  pattern Rose,
  -- ** Some 'Tree' values
  aTree1, aTree2, aTree3,
  -- ** Some 'Rose' values
  aRose1, aRose2,
  -- * Tree regular expressions
  -- ** Useful pattern synonyms
  pattern Leaf_, pattern Branch_,
  -- ** Some stand-alone expressions
  rTree1, rTree2, rTree3, rRose1,
  -- ** Using 'with' views
  eWith1, eWith2,
  -- ** Using the 'rx' quasi-quoter
  eWith2Bis, eWith3, eWith4,
  -- * Grammar and rules
  grammar1, grammar2, grammar3
) where

import Control.Applicative ((<$>), (<*>))
import Control.Lens hiding (at, (#), children)
import Data.Map ((!))
import qualified Data.Map as M
import Data.Monoid (Sum(..))
import Data.Regex.Generics
import Data.Regex.Rules
import Data.Regex.TH
import GHC.Generics
import Test.QuickCheck

-- | The pattern functor, which should be kept open.
--   Recursion is done by using the argument.
data Tree' f = Leaf' | Branch' { elt :: Int, left :: f, right :: f }
  deriving (Generic1, Show)
-- | Closes the data type by creating its fix-point.
type Tree = Fix Tree'

instance Arbitrary Tree where
  arbitrary = frequency
    [ (1, return Leaf)
    , (5, Branch <$> arbitrary <*> arbitrary <*> arbitrary) ]

-- | The pattern functor for rose trees.
data Rose' f = Rose' { value :: Int, child :: [f] }
  deriving (Generic1, Show)
-- | Closes the data type by creating its fix-point.
type Rose = Fix Rose'

-- | Pattern synonym for the 'Leaf' constructor inside 'Fix'.
pattern Leaf = Fix Leaf'
-- | Pattern synonym for the 'Branch' constructor inside 'Fix'.
pattern Branch n l r = Fix (Branch' n l r)
-- | Pattern synonym for the 'Rose' constructor inside 'Fix'.
pattern Rose v c = Fix (Rose' v c)

instance Show Tree where
  show (Fix Leaf') = "Leaf"
  show (Fix (Branch' n t1 t2)) = "(Branch " ++ show n ++ " " ++ show t1 ++ " " ++ show t2 ++ ")"

instance Show Rose where
  show (Fix (Rose' n c)) = show n ++ show c

aTree1 :: Tree
aTree1 = Branch 2 (Branch 3 (Branch 2 (Branch 4 Leaf Leaf) Leaf) Leaf) Leaf

aTree2 :: Tree
aTree2 = Branch 2 (Branch 2 Leaf Leaf) Leaf

aTree3 :: Tree
aTree3 = Branch 2 Leaf Leaf

aRose1 :: Rose
aRose1 = Rose 2 [Rose 2 [], Rose 2 []]

aRose2 :: Rose
aRose2 = Rose 2 [Rose 2 [], Rose 2 [Rose 3 []]]

rTree1 :: Regex String Tree'
rTree1 = iter $ \k ->
           capture "x" $
                  inj (Branch' 2 k k)
             <||> inj Leaf'

rTree2 :: Integer -> Regex Integer Tree'
rTree2 c = iter $ \k ->
             capture c $
                    inj (Branch' 2 k k)
               <||> inj Leaf'

pattern Branch_ n l r = Inject (Branch' n l r)
pattern Leaf_         = Inject Leaf'

rTree3 :: Integer -> Integer -> Regex Integer Tree'
rTree3 c1 c2 = ( (\k -> c1 <<- Branch_ 2 k k <||> c2 <<- Leaf_)^* )

rRose1 :: Regex String Rose'
rRose1 = iter $ \k -> capture "x" $ inj (Rose' 2 [k])

eWith1 :: Tree -> [Tree]
eWith1 (with rTree2 -> Just e) = e
eWith1 _                       = error "What?"

eWith2 :: Tree -> [Tree]
eWith2 (with rTree3 -> Just (_,e)) = e
eWith2 _                           = error "What?"

eWith2Bis :: Tree -> [Tree]
eWith2Bis [rx| (\k -> branches <<- Branch_ 2 k k <||> leaves <<- Leaf_)^* |] = leaves
eWith2Bis _  = []

eWith3 :: Tree -> [Tree]
eWith3 [rx| x <<- Leaf_ |] = x
eWith3 _                   = error "What?"

eWith4 :: Tree -> [Int]
eWith4 [rx| (\k -> x <<- inj (Branch' __ k k) <||> e <<- Leaf_)^* |] = map (elt . unFix) x
eWith4 _  = error "What?"

unFix :: Fix f -> f (Fix f)
unFix (Fix x) = x

grammar1 :: Grammar String Tree' () String
grammar1 = [ ( inj (Branch' 2 ("l" <<- any_) ("r" <<- any_))
             , \_ _ children ->
                  ( True
                  , M.fromList [("l",()),("r",())]
                  , "(" ++ children ! "l"
                    ++ ")-SPECIAL-("
                    ++ children ! "r" ++ ")" ) )
           , ( inj (Branch' __ ("l" <<- any_) ("r" <<- any_))
             , \(Branch e _ _) _ children ->
                  ( True
                  , M.fromList [("l",()),("r",())]
                  , "(" ++ children ! "l"
                    ++ ")-" ++ show e  ++ "-("
                    ++ children ! "r" ++ ")" ) )
           , ( Leaf_, \_ _ _ -> (True, M.empty, "leaf") )
           ]

grammar2 :: Grammar Integer Tree' () (String, Sum Integer)
grammar2 = [
    rule $ \l r ->
     inj (Branch' 2 (l <<- any_) (r <<- any_)) ->> do
       -- check False
       (lText,lN) <- use (at l . syn)
       (rText,rN) <- use (at r . syn)
       this.syn._1 .= "(" ++ lText ++ ")-SPECIAL-(" ++ rText ++ ")"
       this.syn._2 .= lN + rN
  , rule $ \l r ->
     inj (Branch' __ (l <<- any_) (r <<- any_)) ->>> \(Branch e _ _) -> do
       (lText,lN) <- use (at l . syn)
       (rText,rN) <- use (at r . syn)
       this.syn._1 .= "(" ++ lText ++ ")-" ++ show e ++ "-(" ++ rText ++ ")"
       this.syn._2 .= lN + rN
  , rule $ Leaf_ ->> do
       this.syn._1 .= "leaf"
       this.syn._2 .= Sum 1
  ]

grammar3 :: Grammar Integer Tree' Char (String, Sum Integer)
grammar3 = [
    rule $ \l r ->
     inj (Branch' 2 (l <<- any_) (r <<- any_)) ->> do
       special <- use (this.inh)
       at l . inh .= succ special
       at r . inh .= succ special
       -- check False
       (lText,lN) <- use (at l . syn)
       (rText,rN) <- use (at r . syn)
       if lText == "leaf" && rText == "leaf"
          then this.syn._1 .= "leaves"
          else this.syn._1 .= "(" ++ lText ++ ")-" ++ [special] ++ "-(" ++ rText ++ ")"
       this.syn._2 .= lN + rN
  , rule $ \l r ->
     inj (Branch' __ (l <<- any_) (r <<- any_)) ->>> \(Branch e _ _) -> do
       (lText,lN) <- use (at l . syn)
       (rText,rN) <- use (at r . syn)
       this.syn._1 .= "(" ++ lText ++ ")-" ++ show e ++ "-(" ++ rText ++ ")"
       this.syn._2 .= lN + rN
  , rule $ Leaf_ ->> do
       this.syn._1 .= "leaf"
       this.syn._2 .= Sum 1
  ]

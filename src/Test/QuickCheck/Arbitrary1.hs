module Test.QuickCheck.Arbitrary1 (
  Arbitrary1(..)
) where

import Control.Applicative
import Test.QuickCheck

-- | Version of 'Arbitrary' for functors.
class Arbitrary1 f where
  arbitrary1 :: Gen a -> Gen (f a)

-- From QuickCheck source
instance Arbitrary1 [] where
  arbitrary1 g = sized $ \n ->
    do k <- choose (0,n)
       sequence [ g | _ <- [1..k] ]

instance Arbitrary1 Maybe where
  arbitrary1 g = frequency [(1, return Nothing), (3, Just <$> g)]

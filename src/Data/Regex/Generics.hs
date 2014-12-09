{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- | Tree regular expressions over regular data types.
module Data.Regex.Generics (
  -- * Base types
  Regex(Regex),
  Regex'(Inject),
  Fix(..),
  
  -- * Constructors
  -- | For a description and study of tree regular expressions, you are invited to read
  --   Chapter 2 of <http://tata.gforge.inria.fr/ Tree Automata Techniques and Applications>.
  
  -- ** Emptiness
  empty_, none,
  -- ** Whole language
  any_,
  -- ** Injection
  inj, __,
  -- ** Holes/squares
  square, var, (#),
  -- ** Alternation
  choice, (<||>),
  -- ** Concatenation
  concat_, (<.>),
  -- ** Iteration
  iter, (^*),
  -- ** Capture
  capture, (<<-),
  
  -- * Matching
  Matchable,
  matches, match,
  
  -- * Views
  with,

  -- * Random generation
  Arbitrary1(..),
  arbitraryFromRegex
) where

import Control.Applicative
import Control.Exception
import Control.Monad (guard)
import Data.Foldable as F
import Data.Functor.Foldable (Fix(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isJust)
import Data.Typeable
import GHC.Generics
import System.IO.Unsafe (unsafePerformIO)
import Test.QuickCheck

-- | The basic data type for tree regular expressions.
--
--   * 'k' is used as phantom type to point to concatenation and iteration positions.
--   * 'c' is the type of capture identifiers.
--   * 'f' is the pattern functor over which regular expressions match.
--     In tree regular expression jargon, expresses the set of constructors for nodes.
data Regex' k c (f :: * -> *)
  = Empty
  | Any
  | Inject  (f (Regex' k c f))  -- ^ Useful for defining pattern synonyms for injected constructors.
  | Square k
  | Choice (Regex' k c f) (Regex' k c f)
  | Concat (k -> Regex' k c f) (Regex' k c f)
  | Capture c (Regex' k c f)
-- | Tree regular expressions over pattern functor 'f' with capture identifiers of type 'c'.
newtype Regex c (f :: * -> *) = Regex { unRegex :: forall k. Regex' k c f }

-- | Matches no value.
empty_, none :: Regex' k c f
empty_ = Empty
none = empty_

-- | Matches any value of the data type.
any_ :: Regex' k c f
any_ = Any

-- | Injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are checked for equality,
-- except when using '__' as the value.
inj :: f (Regex' k c f) -> Regex' k c f
inj = Inject

-- | Serves as a placeholder for any value in a non-'f'-typed position.
__ :: a
__ = throw DoNotCheckThisException

data DoNotCheckThisException = DoNotCheckThisException deriving (Show, Typeable)
instance Exception DoNotCheckThisException

-- | Indicates the position of a hole in a regular expression.
square, var :: k -> Regex' k c f
square = Square
var = square

-- | Indicates the position of a hole in a regular expression.
--   This function is meant to be used with the @PostfixOperators@ pragma.
(#) :: k -> Regex' k c f
(#) = square

-- | Expresses alternation between two tree regular expressions:
--   Data types may match one or the other.
--   When capturing, the first one is given priority.
infixl 3 <||>
choice, (<||>) :: Regex' k c f -> Regex' k c f -> Regex' k c f
choice = Choice
(<||>) = choice

-- | Concatenation: a whole in the first tree regular expression
--   is replaced by the second one.
concat_, (<.>) :: (k -> Regex' k c f) -> Regex' k c f -> Regex' k c f
concat_ = Concat
(<.>) = concat_

-- | Repeated replacement of a hole in a tree regular expression.
--   Iteration fulfills the law: @iter r = r \<.\> iter r@.
iter :: (k -> Regex' k c f) -> Regex' k c f
iter r = Concat r (iter r)

-- | Repeated replacement of a hole in a tree regular expression.
--   This function is meant to be used with the @PostfixOperators@ pragma.
(^*) :: (k -> Regex' k c f) -> Regex' k c f
(^*) = iter

-- | Indicates a part of a value that, when matched, should be
--   given a name of type 'c' and saved for querying.
infixl 4 <<-
capture, (<<-) :: c -> Regex' k c f -> Regex' k c f
capture = Capture
(<<-) = capture


-- | Types which can be matched.
type Matchable f = (Generic1 f, MatchG (Rep1 f))

-- | Checks whether a term 't' matches the tree regular expression 'r'.
matches :: forall c f. (Ord c, Matchable f)
        => Regex c f -> Fix f -> Bool
r `matches` t = isJust $ (match r t :: Maybe (Map c [Fix f]))

-- | Checks whether a term 't' matches the tree regular expression 'r'.
--   When successful, it returns in addition a map of captured subterms.
--
--   The behaviour of several matches over the same capture identifier
--   is governed by the 'Alternative' functor 'm'. For example, if
--   @m = []@, all matches are returned in prefix-order. If @m = Maybe@,
--   only the first result is returned.
match :: (Ord c, Matchable f, Alternative m)
      => Regex c f -> Fix f -> Maybe (Map c (m (Fix f)))
match r t = match' (unRegex r) t 0 []

match' :: (Ord c, Matchable f, Alternative m)
       => Regex' Integer c f
       -> Fix f
       -> Integer  -- Fresh variable generator
       -> [(Integer, Regex' Integer c f)]  -- Ongoing substitution
       -> Maybe (Map c (m (Fix f)))
match' Empty             _ _ _ = Nothing
match' Any               _ _ _ = Just M.empty
match' (Inject r)  (Fix t) i s = injG (from1 r) (from1 t) i s
match' (Square n)        t i s = let Just r = lookup n s in match' r t i s
match' (Choice r1 r2)    t i s = match' r1 t i s <|> match' r2 t i s
match' (Concat r1 r2)    t i s = match' (r1 i) t (i+1) ((i,r2):s)
match' (Capture c r)     t i s = M.insertWith (<|>) c (pure t) <$> match' r t i s

class MatchG f where
  injG :: (Ord c, Matchable g, Alternative m)
       => f (Regex' Integer c g) -> f (Fix g)
       -> Integer -> [(Integer, Regex' Integer c g)]
       -> Maybe (Map c (m (Fix g)))

instance MatchG U1 where
  injG _ _ _ _ = Just M.empty

instance MatchG Par1 where
  injG (Par1 r) (Par1 t) = match' r t

instance Eq c => MatchG (K1 i c) where
  injG (K1 r) (K1 t) _ _ = unsafePerformIO $
                             catch (evaluate $ do guard (r == t) -- Maybe monad
                                                  return M.empty)
                                   (\(_ :: DoNotCheckThisException) -> return $ Just M.empty)

instance (Functor f, Foldable f) => MatchG (Rec1 f) where
  injG (Rec1 rs) (Rec1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> match' r t i s) ts) rs

instance MatchG a => MatchG (M1 i c a) where
  injG (M1 r) (M1 t) = injG r t

instance (MatchG a, MatchG b) => MatchG (a :+: b) where
  injG (L1 r) (L1 t) i s = injG r t i s
  injG (R1 r) (R1 t) i s = injG r t i s
  injG _      _      _ _ = Nothing

instance (MatchG a, MatchG b) => MatchG (a :*: b) where
  injG (r1 :*: r2) (t1 :*: t2) i s = M.unionWith (<|>) <$> injG r1 t1 i s <*> injG r2 t2 i s

instance (Functor f, Foldable f, MatchG g) => MatchG (f :.: g) where
  injG (Comp1 rs) (Comp1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> injG r t i s) ts) rs


class With f fn r | fn -> r where
  -- | Useful function to be used as view pattern.
  --   The first argument should be a function, which indicates those places where captured are found
  --   Those captured are automatically put in a tuple, giving a simpler and type-safer
  --   access to captured subterms that looking inside a map.
  --
  --   As an example, here is how one would use it for capturing two subterms:
  --
  --   > f (with (\x y -> iter $ \k -> x <<- inj One <||> y <<- inj (Two (var k))) -> Just (x, y)) = ... x and y available here ...
  --
  --   For more concise syntax which uses quasi-quotation, check "Data.Regex.TH".
  with :: fn -> Fix f -> Maybe r

instance (Generic1 f, MatchG (Rep1 f), Ord c)
         => With f (Regex c f) () where
  with r t = (const ()) <$> (match r t :: Maybe (Map c [Fix f]))
  
instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Regex Integer f) [Fix f] where
  with r t = M.findWithDefault [] 1 <$> match (r 1) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Regex Integer f)
                   ([Fix f], [Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m))
             <$> match (r 1 2) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m, M.findWithDefault [] 3 m))
             <$> match (r 1 2 3) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m,
                     M.findWithDefault [] 3 m, M.findWithDefault [] 4 m))
             <$> match (r 1 2 3 4) t

instance (Generic1 f, MatchG (Rep1 f))
         => With f (Integer -> Integer -> Integer -> Integer -> Integer -> Regex Integer f)
                   ([Fix f],[Fix f],[Fix f],[Fix f],[Fix f]) where
  with r t = (\m -> (M.findWithDefault [] 1 m, M.findWithDefault [] 2 m, M.findWithDefault [] 3 m,
                     M.findWithDefault [] 4 m, M.findWithDefault [] 5 m))
             <$> match (r 1 2 3 4 5) t


-- Generation of arbitrary elements following a pattern

-- | Version of 'Arbitrary' for functors.
class Arbitrary1 f where
  arbitrary1 :: Arbitrary a => Gen a -> Gen (f a)

-- From QuickCheck source
instance Arbitrary1 [] where
  arbitrary1 g = sized $ \n ->
    do k <- choose (0,n)
       sequence [ g | _ <- [1..k] ]

-- | Return a random value which matches the given regular expression.
arbitraryFromRegex :: (Generic1 f, ArbitraryRegexG (Rep1 f), Arbitrary (Fix f))
                   => Regex c f -> Gen (Fix f)
arbitraryFromRegex r = arbitraryFromRegex_ (unRegex r) 0 []

arbitraryFromRegex_ :: (Generic1 f, ArbitraryRegexG (Rep1 f), Arbitrary (Fix f))
                    => Regex' Integer c f
                    -> Integer -> [(Integer, Regex' Integer c f)]
                    -> Gen (Fix f)
arbitraryFromRegex_ Empty          _ _ = error "Cannot generate empty tree"
arbitraryFromRegex_ Any            _ _ = arbitrary
arbitraryFromRegex_ (Capture _ r)  i s = arbitraryFromRegex_ r i s
arbitraryFromRegex_ (Inject r)     i s = Fix . to1 <$> arbG (from1 r) i s
arbitraryFromRegex_ (Square n)     i s = let Just r = lookup n s in arbitraryFromRegex_ r i s
arbitraryFromRegex_ (Concat r1 r2) i s = arbitraryFromRegex_ (r1 i) (i+1) ((i,r2):s)
arbitraryFromRegex_ r@(Choice _ _) i s = oneof $ [arbitraryFromRegex_ rx i s | rx <- toListOfChoices r]

toListOfChoices :: Regex' Integer c f -> [Regex' Integer c f]
toListOfChoices Empty          = []
toListOfChoices Any            = [Any]
toListOfChoices (Capture _ r)  = toListOfChoices r
toListOfChoices (Choice r1 r2) = toListOfChoices r1 ++ toListOfChoices r2
toListOfChoices r              = [r]

class ArbitraryRegexG f where
  arbG :: (Generic1 g, ArbitraryRegexG (Rep1 g), Arbitrary (Fix g))
       => f (Regex' Integer c g)
       -> Integer -> [(Integer, Regex' Integer c g)]
       -> Gen (f (Fix g))

instance ArbitraryRegexG U1 where
  arbG U1 _ _ = return U1

instance ArbitraryRegexG Par1 where
  arbG (Par1 r) i s = Par1 <$> arbitraryFromRegex_ r i s

instance Arbitrary c => ArbitraryRegexG (K1 i c) where
  arbG (K1 r) _ _ = unsafePerformIO $
                      catch (r `seq` return (return (K1 r)))  -- try to return a constant value
                            (\(_ :: DoNotCheckThisException) -> return (K1 <$> arbitrary))

instance (Foldable f, Arbitrary1 f) => ArbitraryRegexG (Rec1 f) where
  arbG (Rec1 rs) i s = let r:_ = toList rs in Rec1 <$> arbitrary1 (arbitraryFromRegex_ r i s)

instance ArbitraryRegexG a => ArbitraryRegexG (M1 i c a) where
  arbG (M1 r) i s = M1 <$> arbG r i s

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :+: b) where
  arbG (L1 r) i s = L1 <$> arbG r i s
  arbG (R1 r) i s = R1 <$> arbG r i s

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :*: b) where
  arbG (r1 :*: r2) i s = (:*:) <$> arbG r1 i s <*> arbG r2 i s

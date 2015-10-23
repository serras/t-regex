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
  -- Regex(Regex),
  Regex(Inject),
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
  -- Holes/squares
  -- square, var, (#),
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
  matches, match, matchList,

  -- * Views
  with,

  -- * Random generation
  arbitraryFromRegex,
  arbitraryFromRegexAndGen
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
import Test.QuickCheck.Arbitrary1

-- | The basic data type for tree regular expressions.
--
--   * 'c' is the type of capture identifiers.
--   * 'f' is the pattern functor over which regular expressions match.
--     In tree regular expression jargon, expresses the set of constructors for nodes.
data Regex c (f :: * -> *)
  = Empty
  | Any
  | Inject  (f (Regex c f))  -- ^ Useful for defining pattern synonyms for injected constructors.
  -- | Square k
  | Choice (Regex c f) (Regex c f)
  -- | Concat (k -> Regex' k c f) (Regex' k c f)
  | Capture c (Regex c f)

{-
-- Tree regular expressions over pattern functor 'f' with capture identifiers of type 'c'.
newtype Regex c (f :: * -> *) = Regex { unRegex :: forall k. Regex' k c f }
-}

-- | Matches no value.
empty_, none :: Regex c f
empty_ = Empty
none = empty_

-- | Matches any value of the data type.
any_ :: Regex c f
any_ = Any

-- | Injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are checked for equality,
-- except when using '__' as the value.
inj :: f (Regex c f) -> Regex c f
inj = Inject

-- | Serves as a placeholder for any value in a non-'f'-typed position.
__ :: a
__ = throw DoNotCheckThisException

data DoNotCheckThisException = DoNotCheckThisException deriving (Show, Typeable)
instance Exception DoNotCheckThisException

{-
-- Indicates the position of a hole in a regular expression.
square, var :: k -> Regex' k c f
square = Square
var = square

-- Indicates the position of a hole in a regular expression.
-- This function is meant to be used with the @PostfixOperators@ pragma.
(#) :: k -> Regex' k c f
(#) = square
-}

-- | Expresses alternation between two tree regular expressions:
--   Data types may match one or the other.
--   When capturing, the first one is given priority.
infixl 3 <||>
choice, (<||>) :: Regex c f -> Regex c f -> Regex c f
choice = Choice
(<||>) = choice

-- | Concatenation: a whole in the first tree regular expression
--   is replaced by the second one.
concat_, (<.>) :: (Regex c f -> Regex c f) -> Regex c f -> Regex c f
concat_ = ($)
(<.>) = concat_

-- | Repeated replacement of a hole in a tree regular expression.
--   Iteration fulfills the law: @iter r = r \<.\> iter r@.
iter :: (Regex c f -> Regex c f) -> Regex c f
iter r = concat_ r (iter r)

-- | Repeated replacement of a hole in a tree regular expression.
--   This function is meant to be used with the @PostfixOperators@ pragma.
(^*) :: (Regex c f -> Regex c f) -> Regex c f
(^*) = iter

-- | Indicates a part of a value that, when matched, should be
--   given a name of type 'c' and saved for querying.
infixl 4 <<-
capture, (<<-) :: c -> Regex c f -> Regex c f
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
{-
match :: (Ord c, Matchable f, Alternative m)
      => Regex c f -> Fix f -> Maybe (Map c (m (Fix f)))
match r t = match' (unRegex r) t 0 []
-}

match :: (Ord c, Matchable f, Alternative m)
      => Regex c f
      -> Fix f
      -- -> Integer  -- Fresh variable generator
      -- -> [(Integer, Regex' Integer c f)]  -- Ongoing substitution
      -> Maybe (Map c (m (Fix f)))
match Empty             _ = Nothing
match Any               _ = Just M.empty
match (Inject r)  (Fix t) = injG (from1 r) (from1 t)
-- match (Square n)        t = let Just r = lookup n s in match r t
match (Choice r1 r2)    t = match r1 t <|> match r2 t
-- match' (Concat r1 r2)    t i s = match' (r1 i) t (i+1) ((i,r2):s)
match (Capture c r)     t = M.insertWith (<|>) c (pure t) <$> match r t

-- | Specialized version of `match` which returns all captures.
matchList :: (Ord c, Matchable f)
          => Regex c f -> Fix f -> Maybe (Map c [Fix f])
matchList = match

class MatchG f where
  injG :: (Ord c, Matchable g, Alternative m)
       => f (Regex c g) -> f (Fix g)
       -- -> Integer -> [(Integer, Regex' Integer c g)]
       -> Maybe (Map c (m (Fix g)))

instance MatchG U1 where
  injG _ _ = Just M.empty

instance MatchG Par1 where
  injG (Par1 r) (Par1 t) = match r t

instance Eq c => MatchG (K1 i c) where
  injG (K1 r) (K1 t) = unsafePerformIO $
                         catch (evaluate $ do guard (r == t) -- Maybe monad
                                              return M.empty)
                               (\(_ :: DoNotCheckThisException) -> return $ Just M.empty)

instance (Functor f, Foldable f) => MatchG (Rec1 f) where
  injG (Rec1 rs) (Rec1 ts) =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> match r t) ts) rs

instance MatchG a => MatchG (M1 i c a) where
  injG (M1 r) (M1 t) = injG r t

instance (MatchG a, MatchG b) => MatchG (a :+: b) where
  injG (L1 r) (L1 t) = injG r t
  injG (R1 r) (R1 t) = injG r t
  injG _      _      = Nothing

instance (MatchG a, MatchG b) => MatchG (a :*: b) where
  injG (r1 :*: r2) (t1 :*: t2) = M.unionWith (<|>) <$> injG r1 t1 <*> injG r2 t2

instance (Functor f, Foldable f, MatchG g) => MatchG (f :.: g) where
  injG (Comp1 rs) (Comp1 ts) =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> injG r t) ts) rs


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

-- | Return a random value which matches the given regular expression.
arbitraryFromRegex :: (Generic1 f, ArbitraryRegexG (Rep1 f), Arbitrary (Fix f))
                   => Regex c f -> Gen (Fix f)
arbitraryFromRegex = arbitraryFromRegexAndGen arbitrary

-- | Return a random value which matches the given regular expression,
--   and which uses a supplied generator for 'any_'.
{-
arbitraryFromRegexAndGen :: (Generic1 f, ArbitraryRegexG (Rep1 f))
                         => Gen (Fix f) -> Regex c f -> Gen (Fix f)
arbitraryFromRegexAndGen g r = arbitraryFromRegex_ g (unRegex r) 0 []
-}

arbitraryFromRegexAndGen :: (Generic1 f, ArbitraryRegexG (Rep1 f))
                         => Gen (Fix f)
                         -> Regex c f
                         --- > Integer -> [(Integer, Regex' Integer c f)]
                         -> Gen (Fix f)
arbitraryFromRegexAndGen _ Empty          = error "Cannot generate empty tree"
arbitraryFromRegexAndGen g Any            = g
arbitraryFromRegexAndGen g (Capture _ r)  = arbitraryFromRegexAndGen g r
arbitraryFromRegexAndGen g (Inject r)     = Fix . to1 <$> arbG g (from1 r)
-- arbitraryFromRegexAndGen g (Square n)     i s = let Just r = lookup n s in arbitraryFromRegex_ g r i s
-- arbitraryFromRegexAndGen g (Concat r1 r2) i s = arbitraryFromRegex_ g (r1 i) (i+1) ((i,r2):s)
arbitraryFromRegexAndGen g r@(Choice _ _) = oneof [arbitraryFromRegexAndGen g rx | rx <- toListOfChoices r]

toListOfChoices :: Regex c f -> [Regex c f]
toListOfChoices Empty          = []
toListOfChoices Any            = [Any]
toListOfChoices (Capture _ r)  = toListOfChoices r
toListOfChoices (Choice r1 r2) = toListOfChoices r1 ++ toListOfChoices r2
toListOfChoices r              = [r]

class ArbitraryRegexG f where
  arbG :: (Generic1 g, ArbitraryRegexG (Rep1 g))
       => Gen (Fix g)
       -> f (Regex c g)
       -- -> Integer -> [(Integer, Regex' Integer c g)]
       -> Gen (f (Fix g))

instance ArbitraryRegexG U1 where
  arbG _ U1 = return U1

instance ArbitraryRegexG Par1 where
  arbG g (Par1 r) = Par1 <$> arbitraryFromRegexAndGen g r

instance Arbitrary c => ArbitraryRegexG (K1 i c) where
  arbG _ (K1 r) = unsafePerformIO $
                    catch (r `seq` return (return (K1 r)))  -- try to return a constant value
                          (\(_ :: DoNotCheckThisException) -> return (K1 <$> arbitrary))

instance (Foldable f, Arbitrary1 f) => ArbitraryRegexG (Rec1 f) where
  arbG g (Rec1 rs) = let r:_ = toList rs in Rec1 <$> arbitrary1 (arbitraryFromRegexAndGen g r)

instance ArbitraryRegexG a => ArbitraryRegexG (M1 i c a) where
  arbG g (M1 r) = M1 <$> arbG g r

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :+: b) where
  arbG g (L1 r) = L1 <$> arbG g r
  arbG g (R1 r) = R1 <$> arbG g r

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :*: b) where
  arbG g (r1 :*: r2) = (:*:) <$> arbG g r1 <*> arbG g r2

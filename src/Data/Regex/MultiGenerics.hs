{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Tree regular expressions over mutually recursive regular data types.
module Data.Regex.MultiGenerics (
  -- * Base types
  Regex(Regex),
  Regex',
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
  square, var, (!),
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
  matches,
  Capturable,
  match,
  -- ** Querying capture groups
  CaptureGroup(..),
  lookupGroup,

  -- * Views
  with,
  Wrap(..),
  (?),

  -- * Random generation
  arbitraryFromRegex,
  arbitraryFromRegexAndGen
) where

import Control.Applicative
import Control.Exception
import Control.Monad (guard)
import qualified Data.Foldable as F
import Data.Foldable (Foldable, toList)
import Data.List (intercalate)
import Data.MultiGenerics
import Data.Typeable
import System.IO.Unsafe (unsafePerformIO)
import Test.QuickCheck
import Test.QuickCheck.Arbitrary1

import Unsafe.Coerce -- :(

-- | The basic data type for tree regular expressions.
--
--   * 'k' is used as phantom type to point to concatenation and iteration positions.
--   * 'c' is the type of capture identifiers.
--   * 'f' is the family of pattern functors over which regular expressions match. In tree regular expression jargon, expresses the set of constructors for nodes.
--   * 'ix' is the index of the data type over which the regular expression matches.
data Regex' (s :: k -> *) (c :: k -> *) (f :: (k -> *) -> k -> *) (ix :: k) where
  Empty   :: Regex' s c f ix
  Any     :: Regex' s c f ix
  Inject  :: f (Regex' s c f) ix -> Regex' s c f ix
  Square  :: s ix -> Regex' s c f ix
  Choice  :: Regex' s c f ix -> Regex' s c f ix -> Regex' s c f ix
  Concat  :: (s xi -> Regex' s c f ix) -> Regex' s c f xi -> Regex' s c f ix
  Capture :: c ix -> Regex' s c f ix -> Regex' s c f ix
-- | Tree regular expressions over mutually recursive data types given by the pattern
--   functor 'f', where the top node is at index 'ix', and with capture identifiers of type 'c'.
newtype Regex c f ix = Regex { unRegex :: forall s. Regex' s c f ix }

-- | Matches no value.
empty_, none :: Regex' k c f ix
empty_ = Empty
none = empty_

-- | Matches any value of the data type.
any_ :: Regex' k c f ix
any_ = Any

-- | Injects a constructor as a regular expression.
--   That is, specifies a tree regular expression whose root is given by a constructor
--   of the corresponding pattern functor, and whose nodes are other tree regular expressions.
--   When matching, fields of types other than 'f' are checked for equality,
--   except when using '__' as the value.
inj :: f (Regex' k c f) ix -> Regex' k c f ix
inj = Inject

-- | Serves as a placeholder for any value in a non-'f'-typed position.
__ :: a
__ = throw DoNotCheckThisException

data DoNotCheckThisException = DoNotCheckThisException deriving (Show, Typeable)
instance Exception DoNotCheckThisException

-- | Indicates the position of a hole in a regular expression.
square, var :: k ix -> Regex' k c f ix
square = Square
var = square

-- | Indicates the position of a hole in a regular expression.
--   This function is meant to be used with the @PostfixOperators@ pragma.
(!) :: k ix -> Regex' k c f ix
(!) = square

-- | Expresses alternation between two tree regular expressions:
--   Data types may match one or the other.
--   When capturing, the first one is given priority.
infixl 3 <||>
choice, (<||>) :: Regex' k c f ix -> Regex' k c f ix -> Regex' k c f ix
choice = Choice
(<||>) = choice

-- | Concatenation: a whole in the first tree regular expression
--   is replaced by the second one.
concat_, (<.>) :: (k xi -> Regex' k c f ix) -> Regex' k c f xi -> Regex' k c f ix
concat_ = Concat
(<.>) = concat_

-- | Repeated replacement of a hole in a tree regular expression.
--   Iteration fulfills the law: @iter r = r \<.\> iter r@.
iter :: (k ix -> Regex' k c f ix) -> Regex' k c f ix
iter r = Concat r (iter r)

-- | Repeated replacement of a hole in a tree regular expression.
--   This function is meant to be used with the @PostfixOperators@ pragma.
(^*) :: (k ix -> Regex' k c f ix) -> Regex' k c f ix
(^*) = iter

-- | Indicates a part of a value that, when matched, should be
--   given a name of type 'c' and saved for querying.
infixl 4 <<-
capture, (<<-) :: c ix -> Regex' k c f ix -> Regex' k c f ix
capture = Capture
(<<-) = capture

-- | Types which can be matched.
type Matchable f = (Generic1m f, MatchG (Rep1m f))

-- | Checks whether a term 't' matches the tree regular expression 'r'.
matches :: Matchable f => Regex c f ix -> Fix f ix -> Bool
r `matches` t = matches' (unRegex r) t 0 []

data CaptureGroup c f m where
  CaptureGroup :: c ix -> m (Fix f ix) -> CaptureGroup c f m

instance (ShowM c, Foldable m, ShowM (Fix f)) => Show (CaptureGroup c f m) where
  show (CaptureGroup ix e) = showM ix ++ " -> { " ++ intercalate ", " (map showM $ toList e) ++ " }"

lookupGroup :: EqM c => c ix -> [CaptureGroup c f m] -> Maybe (m (Fix f ix))
lookupGroup _ [] = Nothing
lookupGroup c (CaptureGroup ix info : rest) | c `eqM` ix = Just (unsafeCoerce info)
                                            | otherwise  = lookupGroup c rest

lookupGroupDef :: (Alternative m, EqM c) => c ix -> [CaptureGroup c f m] -> m (Fix f ix)
lookupGroupDef _ [] = empty
lookupGroupDef c (CaptureGroup ix info : rest) | c `eqM` ix = unsafeCoerce info
                                               | otherwise  = lookupGroupDef c rest

unionGroups :: (EqM c, Alternative m)
            => [CaptureGroup c f m] -> [CaptureGroup c f m]
            -> [CaptureGroup c f m]
unionGroups [] g2 = g2
unionGroups (ge1@(CaptureGroup ix1 info1) : grest1) g2 =
  newG1 ++ unionGroups grest1 newG2
  where (newG1, newG2) = unionGroups' g2 []
        unionGroups' [] accG2 = ([ge1], reverse accG2)
        unionGroups' (ge2@(CaptureGroup ix2 info2) : grest2) accG2
          | ix1 `eqM` ix2 = ([CaptureGroup ix1 (info1 <|> unsafeCoerce info2)], reverse accG2 ++ grest2)
          | otherwise     = unionGroups' grest2 (ge2 : accG2)

-- | Types which can be matched and captured.
type Capturable c f = (Generic1m f, MatchG (Rep1m f), EqM c)

-- | Checks whether a term 't' matches the tree regular expression 'r'.
--   When successful, it returns in addition a map of captured subterms.
--
--   The behaviour of several matches over the same capture identifier
--   is governed by the 'Alternative' functor 'm'. For example, if
--   @m = []@, all matches are returned in prefix-order. If @m = Maybe@,
--   only the first result is returned.
match :: (Capturable c f, Alternative m)
      => Regex c f ix -> Fix f ix -> Maybe [CaptureGroup c f m]
match r t = match' (unRegex r) t 0 []

newtype WrappedInteger a = W Integer

matches' :: Matchable f
         => Regex' WrappedInteger c f ix
         -> Fix f ix
         -> Integer  -- Fresh variable generator
         -> [(Integer, forall xi. Regex' WrappedInteger c f xi)]  -- Ongoing substitution
         -> Bool
matches' Empty             _ _ _ = False
matches' Any               _ _ _ = True
matches' (Inject r)  (Fix t) i s = injesG (from1k r) (from1k t) i s
matches' (Square (W n))    t i s = let Just r = unsafeCoerce (lookup n s) in matches' r t i s
matches' (Choice r1 r2)    t i s = matches' r1 t i s || matches' r2 t i s
matches' (Concat r1 r2)    t i s = matches' (r1 (W i)) t (i+1) ((i, unsafeCoerce r2):s)
matches' (Capture _ r)     t i s = matches' r t i s

match' :: (Capturable c f, Alternative m)
       => Regex' WrappedInteger c f ix
       -> Fix f ix
       -> Integer  -- Fresh variable generator
       -> [(Integer, forall xi. Regex' WrappedInteger c f xi)]  -- Ongoing substitution
       -> Maybe [CaptureGroup c f m]
match' Empty             _ _ _ = Nothing
match' Any               _ _ _ = Just []
match' (Inject r)  (Fix t) i s = injG (from1k r) (from1k t) i s
match' (Square (W n))    t i s = let Just r = unsafeCoerce (lookup n s) in match' r t i s
match' (Choice r1 r2)    t i s = match' r1 t i s <|> match' r2 t i s
match' (Concat r1 r2)    t i s = match' (r1 (W i)) t (i+1) ((i, unsafeCoerce r2):s)
match' (Capture c r)     t i s = unionGroups [CaptureGroup c (pure t)] <$> match' r t i s

class MatchG (f :: (k -> *) -> k -> *) where
  injesG :: Matchable g
         => f (Regex' WrappedInteger c g) ix
         -> f (Fix g) ix
         -> Integer
         -> [(Integer, forall xi. Regex' WrappedInteger c g xi)]
         -> Bool
  injG :: (Capturable c g, Alternative m)
       => f (Regex' WrappedInteger c g) ix
       -> f (Fix g) ix
       -> Integer
       -> [(Integer, forall xi. Regex' WrappedInteger c g xi)]
       -> Maybe [CaptureGroup c g m]

instance MatchG U1m where
  injesG _ _ _ _ = True
  injG   _ _ _ _ = Just []

instance MatchG (Par1m xi) where
  injesG (Par1m r) (Par1m t) = matches' r t
  injG   (Par1m r) (Par1m t) = match' r t

instance (Functor f, Foldable f) => MatchG (Rec1m f xi) where
  injesG (Rec1m rs) (Rec1m ts) i s =
    F.foldr (||) False $ fmap (\r -> F.foldr (&&) True $ fmap (\t -> matches' r t i s) ts) rs
  injG   (Rec1m rs) (Rec1m ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (unionGroups m1 m2)
                                       _                  -> Nothing)
                  (Just [])
                  $ fmap (\t -> match' r t i s) ts) rs

instance Eq c => MatchG (K1m i c) where
  injesG (K1m r) (K1m t) _ _ =
    unsafePerformIO $
      catch (evaluate $ r == t)
            (\(_ :: DoNotCheckThisException) -> return True)
  injG   (K1m r) (K1m t) _ _ =
    unsafePerformIO $
      catch (evaluate $ do guard (r == t) -- Maybe monad
                           return [])
            (\(_ :: DoNotCheckThisException) -> return $ Just [])

instance (MatchG a, MatchG b) => MatchG (a :++: b) where
  injesG (L1m r) (L1m t) i s = injesG r t i s
  injesG (R1m r) (R1m t) i s = injesG r t i s
  injesG _       _       _ _ = False
  injG   (L1m r) (L1m t) i s = injG r t i s
  injG   (R1m r) (R1m t) i s = injG r t i s
  injG   _       _       _ _ = Nothing

instance (MatchG a, MatchG b) => MatchG (a :**: b) where
  injesG (r1 :**: r2) (t1 :**: t2) i s = injesG r1 t1 i s && injesG r2 t2 i s
  injG   (r1 :**: r2) (t1 :**: t2) i s = unionGroups <$> injG r1 t1 i s <*> injG r2 t2 i s

instance MatchG f => MatchG (Tag1m f xi) where
  injesG (Tag1m r) (Tag1m t) = injesG r t
  injG   (Tag1m r) (Tag1m t) = injG r t

-- | Data type used to tag capture identifiers with their expected type.
newtype Wrap c ix = Wrap c deriving (Eq, Ord)

instance Eq c => EqM (Wrap c) where
  eqM (Wrap n1) (Wrap n2) = n1 == n2

instance Show c => ShowM (Wrap c) where
  showM (Wrap n) = show n

-- | Wraps an already existing type to recall extra index information.
(?) :: c -> Wrap c ix
(?) = Wrap

type WI = Wrap Integer

class With f ix fn r | fn -> r where
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
  with :: fn -> Fix f ix -> Maybe r

instance Capturable c f
         => With f ix (Regex c f ix) () where
  with r t = (const ()) <$> (match r t :: Maybe [CaptureGroup c f []])

instance Matchable f
         => With f ix (WI xi -> Regex WI f ix) [Fix f xi] where
  with r t = lookupGroupDef (Wrap 1) <$> match (r (Wrap 1)) t

instance Matchable f
         => With f ix (WI xi1 -> WI xi2 -> Regex WI f ix)
                      ([Fix f xi1], [Fix f xi2]) where
  with r t = (\m -> ( lookupGroupDef (Wrap 1) m
                    , lookupGroupDef (Wrap 2) m) )
             <$> match (r (Wrap 1) (Wrap 2)) t

instance Matchable f
         => With f ix (WI xi1 -> WI xi2 -> WI xi3 -> Regex WI f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3]) where
  with r t = (\m -> ( lookupGroupDef (Wrap 1) m
                    , lookupGroupDef (Wrap 2) m
                    , lookupGroupDef (Wrap 3) m) )
             <$> match (r (Wrap 1) (Wrap 2) (Wrap 3)) t

instance Matchable f
         => With f ix (WI xi1 -> WI xi2 -> WI xi3 -> WI xi4 -> Regex WI f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3], [Fix f xi4]) where
  with r t = (\m -> ( lookupGroupDef (Wrap 1) m
                    , lookupGroupDef (Wrap 2) m
                    , lookupGroupDef (Wrap 3) m
                    , lookupGroupDef (Wrap 4) m) )
             <$> match (r (Wrap 1) (Wrap 2) (Wrap 3) (Wrap 4)) t

instance Matchable f
         => With f ix (WI xi1 -> WI xi2 -> WI xi3 -> WI xi4 -> WI xi5 -> Regex WI f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3], [Fix f xi4], [Fix f xi5]) where
  with r t = (\m -> ( lookupGroupDef (Wrap 1) m
                    , lookupGroupDef (Wrap 2) m
                    , lookupGroupDef (Wrap 3) m
                    , lookupGroupDef (Wrap 4) m
                    , lookupGroupDef (Wrap 5) m))
             <$> match (r (Wrap 1) (Wrap 2) (Wrap 3) (Wrap 4) (Wrap 5)) t

-- | Return a random value which matches the given regular expression.
arbitraryFromRegex :: (Generic1m f, ArbitraryRegexG (Rep1m f)
                      , ArbitraryM (Fix f), SingI ix)
                   => Regex c f ix -> Gen (Fix f ix)
arbitraryFromRegex = arbitraryFromRegexAndGen arbitraryM

-- | Return a random value which matches the given regular expression,
--   and which uses a supplied generator for 'any_'.
arbitraryFromRegexAndGen :: (Generic1m f, ArbitraryRegexG (Rep1m f), SingI ix)
                         => GenM (Fix f) -> Regex c f ix -> Gen (Fix f ix)
arbitraryFromRegexAndGen g r = arbitraryFromRegex_ g (unRegex r) 0 []

arbitraryFromRegex_ :: (Generic1m f, ArbitraryRegexG (Rep1m f), SingI ix)
                    => GenM (Fix f)
                    -> Regex' WrappedInteger c f ix
                    -> Integer
                    -> [(Integer, forall xi. Regex' WrappedInteger c f xi)]
                    -> Gen (Fix f ix)
arbitraryFromRegex_ _ Empty          _ _ = error "Cannot generate empty tree"
arbitraryFromRegex_ g Any            _ _ = g sing
arbitraryFromRegex_ g (Capture _ r)  i s = arbitraryFromRegex_ g r i s
arbitraryFromRegex_ g (Inject r)     i s = Fix . to1k <$> arbG g (from1k r) i s
arbitraryFromRegex_ g (Square (W n)) i s = let Just r = lookup n s in arbitraryFromRegex_ g r i s
arbitraryFromRegex_ g (Concat r1 r2) i s = arbitraryFromRegex_ g (r1 (W i)) (i+1) ((i, unsafeCoerce r2):s)
arbitraryFromRegex_ g r@(Choice _ _) i s = oneof [arbitraryFromRegex_ g rx i s | rx <- toListOfChoices r]

toListOfChoices :: Regex' k c f ix -> [Regex' k c f ix]
toListOfChoices Empty          = []
toListOfChoices Any            = [Any]
toListOfChoices (Capture _ r)  = toListOfChoices r
toListOfChoices (Choice r1 r2) = toListOfChoices r1 ++ toListOfChoices r2
toListOfChoices r              = [r]

class ArbitraryRegexG f where
  arbG :: (Generic1m g, ArbitraryRegexG (Rep1m g))
       => GenM (Fix g)
       -> f (Regex' WrappedInteger c g) ix
       -> Integer
       -> [(Integer, forall xi. Regex' WrappedInteger c g xi)]
       -> Gen (f (Fix g) ix)

instance ArbitraryRegexG U1m where
  arbG _ U1m _ _ = return U1m

instance SingI xi => ArbitraryRegexG (Par1m xi) where
  arbG g (Par1m r) i s = Par1m <$> arbitraryFromRegex_ g r i s

instance Arbitrary c => ArbitraryRegexG (K1m i c) where
  arbG _ (K1m r) _ _ = unsafePerformIO $
                         catch (r `seq` return (return (K1m r)))  -- try to return a constant value
                               (\(_ :: DoNotCheckThisException) -> return (K1m <$> arbitrary))

instance (Foldable f, Arbitrary1 f, SingI xi) => ArbitraryRegexG (Rec1m f xi) where
  arbG g (Rec1m rs) i s = let r:_ = toList rs in Rec1m <$> arbitrary1 (arbitraryFromRegex_ g r i s)

instance ArbitraryRegexG f => ArbitraryRegexG (Tag1m f xi) where
  arbG g (Tag1m r) i s = Tag1m <$> arbG g r i s

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :++: b) where
  arbG g (L1m r) i s = L1m <$> arbG g r i s
  arbG g (R1m r) i s = R1m <$> arbG g r i s

instance (ArbitraryRegexG a, ArbitraryRegexG b) => ArbitraryRegexG (a :**: b) where
  arbG g (r1 :**: r2) i s = (:**:) <$> arbG g r1 i s <*> arbG g r2 i s

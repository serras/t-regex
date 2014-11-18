{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Tree regular expressions over regular data types.
module Data.Regex.Generics (
  -- * Base types
  Regex(Regex),
  Regex'(Inject,Shallow),
  Fix(..),
  
  -- * Constructors
  -- | For a description and study of tree regular expressions, you are invited to read
  --   Chapter 2 of <http://tata.gforge.inria.fr/ Tree Automata Techniques and Applications>.
  
  -- ** Emptiness
  empty_, none,
  -- ** Whole language
  any_,
  -- ** Injection
  inj, shallow, __,
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
  with
) where

import Control.Applicative
import Control.Monad (guard)
import Data.Foldable as F
import Data.Functor.Foldable (Fix(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isJust)
import GHC.Generics

-- | The basic data type for tree regular expressions.
--
--   * 'k' is used as phantom type to point to concatenation and iteration positions.
--   * 'c' is the type of capture identifiers.
--   * 'f' is the pattern functor over which regular expressions match.
--     In tree regular expression jargon, expresses the set of constructors for nodes.
--
-- Note that we differentiate between constructors fully or shallow injected.
-- For fully injected constructors, we check the information inside those fields
-- which are not of type 'f'. With shallow ones, those are not checked.
data Regex' k c (f :: * -> *)
  = Empty
  | Any
  | Inject  (f (Regex' k c f))  -- ^ Useful for defining pattern synonyms for injected full constructors.
  | Shallow (f (Regex' k c f))  -- ^ Useful for defining pattern synonyms for injected shallow constructors.
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

-- | Fully injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are checked for equality.
inj :: f (Regex' k c f) -> Regex' k c f
inj = Inject

-- | Shallow injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are not checked.
shallow :: f (Regex' k c f) -> Regex' k c f
shallow = Shallow

-- | Useful function to combine with 'shallow' and match anything in a non-'f' field.
__ :: a
__ = error "This element should not be checked"

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
match' (Shallow r) (Fix t) i s = shaG (from1 r) (from1 t) i s
match' (Square n)        t i s = let Just r = lookup n s in match' r t i s
match' (Choice r1 r2)    t i s = match' r1 t i s <|> match' r2 t i s
match' (Concat r1 r2)    t i s = match' (r1 i) t (i+1) ((i,r2):s)
match' (Capture c r)     t i s = M.insertWith (<|>) c (pure t) <$> match' r t i s

class MatchG f where
  injG, shaG :: (Ord c, Matchable g, Alternative m)
             => f (Regex' Integer c g) -> f (Fix g)
             -> Integer -> [(Integer, Regex' Integer c g)]
             -> Maybe (Map c (m (Fix g)))

instance MatchG U1 where
  injG _ _ _ _ = Just M.empty
  shaG _ _ _ _ = Just M.empty

instance MatchG Par1 where
  injG (Par1 r) (Par1 t) = match' r t
  shaG (Par1 r) (Par1 t) = match' r t

instance Eq c => MatchG (K1 i c) where
  injG (K1 r) (K1 t) _ _ = do guard (r == t)
                              return M.empty
  shaG _      _      _ _ = return M.empty

instance (Functor f, Foldable f) => MatchG (Rec1 f) where
  injG (Rec1 rs) (Rec1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> match' r t i s) ts) rs
  shaG (Rec1 rs) (Rec1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> match' r t i s) ts) rs

instance MatchG a => MatchG (M1 i c a) where
  injG (M1 r) (M1 t) = injG r t
  shaG (M1 r) (M1 t) = shaG r t

instance (MatchG a, MatchG b) => MatchG (a :+: b) where
  injG (L1 r) (L1 t) i s = injG r t i s
  injG (R1 r) (R1 t) i s = injG r t i s
  injG _      _      _ _ = Nothing
  shaG (L1 r) (L1 t) i s = shaG r t i s
  shaG (R1 r) (R1 t) i s = shaG r t i s
  shaG _      _      _ _ = Nothing

instance (MatchG a, MatchG b) => MatchG (a :*: b) where
  injG (r1 :*: r2) (t1 :*: t2) i s = M.unionWith (<|>) <$> injG r1 t1 i s <*> injG r2 t2 i s
  shaG (r1 :*: r2) (t1 :*: t2) i s = M.unionWith (<|>) <$> shaG r1 t1 i s <*> shaG r2 t2 i s

instance (Functor f, Foldable f, MatchG g) => MatchG (f :.: g) where
  injG (Comp1 rs) (Comp1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> injG r t i s) ts) rs
  shaG (Comp1 rs) (Comp1 ts) i s =
    F.foldr (<|>) Nothing  -- Get only the first option
    $ fmap (\r -> F.foldr (\x1 x2 -> case (x1, x2) of
                                       (Just m1, Just m2) -> Just (M.unionWith (<|>) m1 m2)
                                       _                  -> Nothing)
                  (Just M.empty)
                  $ fmap (\t -> shaG r t i s) ts) rs


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


{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Tree regular expressions over mutually recursive regular data types.
module Data.Regex.MultiGenerics (
  -- * Base types
  Regex(Regex),
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
  matches,
  match,
  -- ** Querying results
  Result(..),
  lookupRSing, lookupR,

  -- * Views
  with,
  Return, (?), (??)
) where

import Control.Applicative
import Control.Monad (MonadPlus, mzero, guard)
import Data.Map (Map)
import qualified Data.Map as M
import Data.MultiGenerics

import Unsafe.Coerce -- :(

-- | The basic data type for tree regular expressions.
--
--   * 'k' is used as phantom type to point to concatenation and iteration positions.
--   * 'c' is the type of capture identifiers.
--   * 'f' is the family of pattern functors over which regular expressions match. In tree regular expression jargon, expresses the set of constructors for nodes.
--   * 'ix' is the index of the data type over which the regular expression matches.
data Regex' (s :: k -> *) c (f :: (k -> *) -> k -> *) (ix :: k) where
  Empty   :: Regex' s c f ix
  Any     :: Regex' s c f ix
  Inject  :: f (Regex' s c f) ix -> Regex' s c f ix
  Shallow :: f (Regex' s c f) ix -> Regex' s c f ix
  Square  :: s ix -> Regex' s c f ix
  Choice  :: Regex' s c f ix -> Regex' s c f ix -> Regex' s c f ix
  Concat  :: (s xi -> Regex' s c f ix) -> Regex' s c f xi -> Regex' s c f ix
  Capture :: c -> Regex' s c f ix -> Regex' s c f ix
-- | Tree regular expressions over mutually recursive data types given by the pattern functor 'f', where the top node is at index 'ix', and with capture identifiers of type 'c'.
newtype Regex c f ix = Regex { unRegex :: forall s. Regex' s c f ix }

-- | Matches no value.
empty_, none :: Regex' k c f ix
empty_ = Empty
none = empty_

-- | Matches any value of the data type.
any_ :: Regex' k c f ix
any_ = Any

-- | Fully injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are checked for equality.
inj :: f (Regex' k c f) ix -> Regex' k c f ix
inj = Inject

-- | Shallow injects a constructor as a regular expression.
-- That is, specifies a tree regular expression whose root is given by a constructor
-- of the corresponding pattern functor, and whose nodes are other tree regular expressions.
-- When matching, fields of types other than 'f' are not checked.
shallow :: f (Regex' k c f) ix -> Regex' k c f ix
shallow = Shallow

-- | Useful function to combine with 'shallow' and match anything in a non-'f' field.
__ :: a
__ = error "This element should not be checked"

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
capture, (<<-) :: c -> Regex' k c f ix -> Regex' k c f ix
capture = Capture
(<<-) = capture


-- | Checks whether a term 't' matches the tree regular expression 'r'.
matches :: (Generic1m f, MatchG (Rep1m f))
        => Regex c f ix -> Fix f ix -> Bool
r `matches` t = matches' (unRegex r) t 0 []

-- | Checks whether a term 't' matches the tree regular expression 'r'.
--   When successful, it returns in addition a map of captured subterms.
--
--   The behaviour of several matches over the same capture identifier
--   is governed by the 'Alternative' functor 'm'. For example, if
--   @m = []@, all matches are returned in prefix-order. If @m = Maybe@,
--   only the first result is returned.
match :: (Ord c, Generic1m f, MatchG (Rep1m f), Alternative m, SingI ix)
      => Regex c f ix -> Fix f ix -> Maybe (Map c (m (Result f)))
match r t = match' (unRegex r) t 0 []

newtype WrappedInteger a = W Integer

matches' :: (Generic1m f, MatchG (Rep1m f))
         => Regex' WrappedInteger c f ix
         -> Fix f ix
         -> Integer  -- Fresh variable generator
         -> [(Integer, forall xi. Regex' WrappedInteger c f xi)]  -- Ongoing substitution
         -> Bool
matches' Empty             _ _ _ = False
matches' Any               _ _ _ = True
matches' (Inject r)  (Fix t) i s = injesG (from1k r) (from1k t) i s
matches' (Shallow r) (Fix t) i s = shaesG (from1k r) (from1k t) i s
matches' (Square (W n))    t i s = let Just r = unsafeCoerce (lookup n s) in matches' r t i s
matches' (Choice r1 r2)    t i s = matches' r1 t i s || matches' r2 t i s
matches' (Concat r1 r2)    t i s = matches' (r1 (W i)) t (i+1) ((i, unsafeCoerce r2):s)
matches' (Capture _ r)     t i s = matches' r t i s

match' :: (Ord c, Generic1m f, MatchG (Rep1m f), Alternative m, SingI ix)
       => Regex' WrappedInteger c f ix
       -> Fix f ix
       -> Integer  -- Fresh variable generator
       -> [(Integer, forall xi. Regex' WrappedInteger c f xi)]  -- Ongoing substitution
       -> Maybe (Map c (m (Result f)))
match' Empty             _ _ _ = Nothing
match' Any               _ _ _ = Just M.empty
match' (Inject r)  (Fix t) i s = injG (from1k r) (from1k t) i s
match' (Shallow r) (Fix t) i s = shaG (from1k r) (from1k t) i s
match' (Square (W n))    t i s = let Just r = unsafeCoerce (lookup n s) in match' r t i s
match' (Choice r1 r2)    t i s = match' r1 t i s <|> match' r2 t i s
match' (Concat r1 r2)    t i s = match' (r1 (W i)) t (i+1) ((i, unsafeCoerce r2):s)
match' (Capture c r)     t i s = M.insertWith (<|>) c (pure (Result sing t)) <$> match' r t i s

class MatchG (f :: (k -> *) -> k -> *) where
  injesG, shaesG :: (Generic1m g, MatchG (Rep1m g))
                 => f (Regex' WrappedInteger c g) ix
                 -> f (Fix g) ix
                 -> Integer
                 -> [(Integer, forall xi. Regex' WrappedInteger c g xi)]
                 -> Bool
  injG, shaG :: (Ord c, Generic1m g, MatchG (Rep1m g), Alternative m, SingI ix)
             => f (Regex' WrappedInteger c g) ix
             -> f (Fix g) ix
             -> Integer
             -> [(Integer, forall xi. Regex' WrappedInteger c g xi)]
             -> Maybe (Map c (m (Result g)))

instance MatchG U1m where
  injesG _ _ _ _ = True
  shaesG _ _ _ _ = True
  injG   _ _ _ _ = Just M.empty
  shaG   _ _ _ _ = Just M.empty

instance SingI xi => MatchG (Par1m xi) where
  injesG (Par1m r) (Par1m t) = matches' r t
  shaesG (Par1m r) (Par1m t) = matches' r t
  injG   (Par1m r) (Par1m t) = match' r t
  shaG   (Par1m r) (Par1m t) = match' r t

instance (MatchG f, SingI xi) => MatchG (Rec1m f xi) where
  injesG (Rec1m r) (Rec1m t) = injesG r t
  shaesG (Rec1m r) (Rec1m t) = shaesG r t
  injG   (Rec1m r) (Rec1m t) = injG r t
  shaG   (Rec1m r) (Rec1m t) = shaG r t

instance Eq c => MatchG (K1m i c) where
  injesG (K1m r) (K1m t) _ _ = r == t
  shaesG (K1m _) (K1m _) _ _ = True
  injG   (K1m r) (K1m t) _ _ = do guard (r == t)
                                  return M.empty
  shaG   (K1m _) (K1m _) _ _ = return M.empty

instance (MatchG a, MatchG b) => MatchG (a :++: b) where
  injesG (L1m r) (L1m t) i s = injesG r t i s
  injesG (R1m r) (R1m t) i s = injesG r t i s
  injesG _       _       _ _ = False
  shaesG (L1m r) (L1m t) i s = shaesG r t i s
  shaesG (R1m r) (R1m t) i s = shaesG r t i s
  shaesG _       _       _ _ = False
  injG   (L1m r) (L1m t) i s = injG r t i s
  injG   (R1m r) (R1m t) i s = injG r t i s
  injG   _       _       _ _ = Nothing
  shaG   (L1m r) (L1m t) i s = shaG r t i s
  shaG   (R1m r) (R1m t) i s = shaG r t i s
  shaG   _       _       _ _ = Nothing

instance (MatchG a, MatchG b) => MatchG (a :**: b) where
  injesG (r1 :**: r2) (t1 :**: t2) i s = injesG r1 t1 i s && injesG r2 t2 i s
  shaesG (r1 :**: r2) (t1 :**: t2) i s = shaesG r1 t1 i s && shaesG r2 t2 i s
  injG   (r1 :**: r2) (t1 :**: t2) i s = M.unionWith (<|>) <$> injG r1 t1 i s <*> injG r2 t2 i s
  shaG   (r1 :**: r2) (t1 :**: t2) i s = M.unionWith (<|>) <$> shaG r1 t1 i s <*> shaG r2 t2 i s

instance (MatchG f, SingI xi) => MatchG (Tag1m f xi) where
  injesG (Tag1m r) (Tag1m t) = injesG r t
  shaesG (Tag1m r) (Tag1m t) = shaesG r t
  injG   (Tag1m r) (Tag1m t) = injG r t
  shaG   (Tag1m r) (Tag1m t) = shaG r t

-- | Combination of a value of the data type expressed by the family of
--   pattern functors 'f' at index 'ix', alongside with a singleton
--   value which encodes the index 'ix' itself.
data Result f where
  Result :: Sing ix -> Fix f ix -> Result f

instance ShowM (Fix f) => Show (Result f) where
  show (Result _ e) = showM e

-- | Looks up the list of results given a capture identifier and
--   a singleton value representing the set of subterms to be returned.
lookupRSing :: (Ord c, MonadPlus m, Eq (Sing ix))
            => Map c (m (Result f))
            -> c -> Sing ix -> m (Fix f ix)
lookupRSing s k ix = [ unsafeCoerce x | Result xi x <- M.findWithDefault mzero k s
                                      , ix == unsafeCoerce xi ]

-- | Looks up the list of results given a capture identifier.
--   The type of the subterms to be returned is inferred from the context.
--   If the inference is not possible, you can specify it directly with
--   a singleton by using 'lookupRSing'.
lookupR :: (Ord c, MonadPlus m, Eq (Sing ix), SingI ix)
        => c -> Map c (m (Result f)) -> m (Fix f ix)
lookupR k s = lookupRSing s k sing


-- | Data type used to tag capture identifiers with their expected type.
newtype Return ix = Return Integer deriving (Eq, Ord)

-- | Gets the capture identifier out of a 'Return'value for use in views.
(?) :: Return ix -> Integer
(?) (Return n) = n

-- | Explicitly typed version of '?' where the index of the captured
--   value is indicated via a singleton.
(??) :: Return ix -> Sing ix -> Integer
(??) (Return n) _ = n

class With f ix fn r | fn -> r where
  -- | Useful function to be used as view pattern.
  --   The first argument should be a function, which indicates those places where captured are found
  --   Those captured are automatically put in a tuple, giving a simpler and type-safer
  --   access to captured subterms that looking inside a map.
  --
  --   As an example, here is how one would use it for capturing two subterms:
  --
  --   > f (with (\x y -> iter $ \k -> (x?) <<- inj One <||> (y?) <<- inj (Two (var k))) -> Just (x, y)) = ... x and y available here ...
  --
  --   Note that you need to add an extra '?' after each capture identifier.
  --   In some cases, the compiler won't be able to infer the types
  --   of all capture identifiers. In that case, you should use the
  --   '??' function instead, to which you can give a singleton for
  --   the index of the expected data type.
  --
  --   For more concise syntax which uses quasi-quotation, check "Data.Regex.TH".
  with :: fn -> Fix f ix -> Maybe r

instance (Generic1m f, MatchG (Rep1m f), Ord c, SingI ix)
         => With f ix (Regex c f ix) () where
  with r t = (const ()) <$> (match r t :: Maybe (Map c [Result f]))

instance (Generic1m f, MatchG (Rep1m f), SingI ix, SingI xi, Eq (Sing xi))
         => With f ix (Return xi -> Regex Integer f ix) [Fix f xi] where
  with r t = lookupR 1 <$> match (r (Return 1)) t

instance (Generic1m f, MatchG (Rep1m f), SingI ix
         , SingI xi1, Eq (Sing xi1), SingI xi2, Eq (Sing xi2))
         => With f ix (Return xi1 -> Return xi2 -> Regex Integer f ix)
                      ([Fix f xi1], [Fix f xi2]) where
  with r t = (\m -> (lookupR 1 m, lookupR 2 m))
             <$> match (r (Return 1) (Return 2)) t

instance (Generic1m f, MatchG (Rep1m f), SingI ix
         , SingI xi1, Eq (Sing xi1), SingI xi2, Eq (Sing xi2), SingI xi3, Eq (Sing xi3))
         => With f ix (Return xi1 -> Return xi2 -> Return xi3 -> Regex Integer f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3]) where
  with r t = (\m -> (lookupR 1 m, lookupR 2 m, lookupR 3 m))
             <$> match (r (Return 1) (Return 2) (Return 3)) t

instance (Generic1m f, MatchG (Rep1m f), SingI ix
         , SingI xi1, Eq (Sing xi1), SingI xi2, Eq (Sing xi2)
         , SingI xi3, Eq (Sing xi3), SingI xi4, Eq (Sing xi4))
         => With f ix (Return xi1 -> Return xi2 -> Return xi3 -> Return xi4 -> Regex Integer f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3], [Fix f xi4]) where
  with r t = (\m -> (lookupR 1 m, lookupR 2 m, lookupR 3 m, lookupR 4 m))
             <$> match (r (Return 1) (Return 2) (Return 3) (Return 4)) t

instance (Generic1m f, MatchG (Rep1m f), SingI ix
         , SingI xi1, Eq (Sing xi1), SingI xi2, Eq (Sing xi2)
         , SingI xi3, Eq (Sing xi3), SingI xi4, Eq (Sing xi4)
         , SingI xi5, Eq (Sing xi5))
         => With f ix (Return xi1 -> Return xi2 -> Return xi3 -> Return xi4 -> Return xi5 -> Regex Integer f ix)
                      ([Fix f xi1], [Fix f xi2], [Fix f xi3], [Fix f xi4], [Fix f xi5]) where
  with r t = (\m -> (lookupR 1 m, lookupR 2 m, lookupR 3 m, lookupR 4 m, lookupR 5 m))
             <$> match (r (Return 1) (Return 2) (Return 3) (Return 4) (Return 5)) t

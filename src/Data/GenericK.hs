{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Data.GenericK where

-- | Representable types of kind * -> *.
-- This class is derivable in GHC with the DeriveGeneric flag on.
class Generic1k (f :: (k -> *) -> k -> *) where
  -- | Generic representation type
  type Rep1k f :: (k -> *) -> k -> *
  -- | Convert from the datatype to its representation
  from1k  :: f a ix -> Rep1k f a ix
  -- | Convert from the representation to the datatype
  to1k    :: Rep1k f a ix -> f a ix

-- | Void: used for datatypes without constructors
data V1k p ix

instance Generic1k V1k where
  type Rep1k V1k = V1k
  from1k = undefined
  to1k   = undefined

-- | Unit: used for constructors without arguments
data U1k p ix = U1k
  deriving (Eq, Ord, Read, Show)

instance Generic1k U1k where
  type Rep1k U1k = U1k
  from1k = id
  to1k   = id

-- | Used for marking occurrences of the parameter
newtype Par1k (xi :: k) (p :: k -> *) (ix :: k)
  = Par1k { unPar1k :: p xi }

instance Generic1k (Par1k xi) where
  type Rep1k (Par1k xi) = Par1k xi
  from1k = id
  to1k   = id

-- | Recursive calls of kind k -> (k -> *) -> *
newtype Rec1k (f :: (k -> *) -> k -> *) (xi :: k) (p :: k -> *) (ix :: k)
  = Rec1k { unRec1k :: f p xi }

instance Generic1k (Rec1k f xi) where
  type Rep1k (Rec1k f xi) = Rec1k f xi
  from1k (Rec1k x) = Rec1k x
  to1k   (Rec1k x) = Rec1k x

-- | Constants, additional parameters and recursion of kind *
newtype K1k i c p ix = K1k { unK1k :: c }
  deriving (Eq, Ord, Read, Show)

instance Generic1k (K1k i c) where
  type Rep1k (K1k i c) = K1k i c
  from1k = id
  to1k   = id

-- | Sums: encode choice between constructors
infixr 5 :++:
data (:++:) (f :: (k -> *) -> k -> *) (g  :: (k -> *) -> k -> *) p ix
  = L1k (f p ix) | R1k (g p ix)
  deriving (Eq, Ord, Read, Show)

instance (Generic1k f, Generic1k g) => Generic1k (f :++: g) where
  type Rep1k (f :++: g) = (f :++: g)
  from1k = id
  to1k   = id

-- | Products: encode multiple arguments to constructors
infixr 6 :**:
data (:**:) f g p ix = f p ix :**: g p ix
  deriving (Eq, Ord, Read, Show)

instance (Generic1k f, Generic1k g) => Generic1k (f :**: g) where
  type Rep1k (f :**: g) = (f :**: g)
  from1k = id
  to1k   = id

--- | Tags
data Tag1k (f :: (k -> *) -> k -> *) (xi :: k) (p :: k -> *) (ix :: k) where
  Tag1k :: f p ix -> Tag1k f ix p ix

instance Generic1k f => Generic1k (Tag1k f xi) where
  type Rep1k (Tag1k f xi) = Tag1k f xi
  from1k = id
  to1k   = id

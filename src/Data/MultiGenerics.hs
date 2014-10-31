{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Data.MultiGenerics where

newtype Fix (f :: (k -> *) -> k -> *) (ix :: k) = Fix { unFix :: f (Fix f) ix }

-- | The singleton kind-indexed data family.
data family Sing (a :: k)

-- | A 'SingI' constraint is essentially an implicitly-passed singleton.
-- If you need to satisfy this constraint with an explicit singleton, please
-- see 'withSingI'.
class SingI (a :: k) where
  -- | Produce the singleton explicitly. You will likely need the @ScopedTypeVariables@
  -- extension to use this method the way you want.
  sing :: Sing a

class ShowM (f :: k -> *) where
  showM :: f ix -> String

-- | Representable types of kind * -> *.
-- This class is derivable in GHC with the DeriveGeneric flag on.
class Generic1m (f :: (k -> *) -> k -> *) where
  -- | Generic representation type
  type Rep1m f :: (k -> *) -> k -> *
  -- | Convert from the datatype to its representation
  from1k  :: f a ix -> Rep1m f a ix
  -- | Convert from the representation to the datatype
  to1k    :: Rep1m f a ix -> f a ix

-- | Void: used for datatypes without constructors
data V1m p ix

instance Generic1m V1m where
  type Rep1m V1m = V1m
  from1k = undefined
  to1k   = undefined

-- | Unit: used for constructors without arguments
data U1m p ix = U1m
  deriving (Eq, Ord, Read, Show)

instance Generic1m U1m where
  type Rep1m U1m = U1m
  from1k = id
  to1k   = id

-- | Used for marking occurrences of the parameter
newtype Par1m (xi :: k) (p :: k -> *) (ix :: k)
  = Par1m { unPar1m :: p xi }

instance Generic1m (Par1m xi) where
  type Rep1m (Par1m xi) = Par1m xi
  from1k = id
  to1k   = id

-- | Recursive calls of kind k -> (k -> *) -> *
newtype Rec1m (f :: (k -> *) -> k -> *) (xi :: k) (p :: k -> *) (ix :: k)
  = Rec1m { unRec1m :: f p xi }

instance Generic1m (Rec1m f xi) where
  type Rep1m (Rec1m f xi) = Rec1m f xi
  from1k (Rec1m x) = Rec1m x
  to1k   (Rec1m x) = Rec1m x

-- | Constants, additional parameters and recursion of kind *
newtype K1m i c p ix = K1m { unK1m :: c }
  deriving (Eq, Ord, Read, Show)

instance Generic1m (K1m i c) where
  type Rep1m (K1m i c) = K1m i c
  from1k = id
  to1k   = id

-- | Sums: encode choice between constructors
infixr 5 :++:
data (:++:) (f :: (k -> *) -> k -> *) (g  :: (k -> *) -> k -> *) p ix
  = L1m (f p ix) | R1m (g p ix)
  deriving (Eq, Ord, Read, Show)

instance (Generic1m f, Generic1m g) => Generic1m (f :++: g) where
  type Rep1m (f :++: g) = (f :++: g)
  from1k = id
  to1k   = id

-- | Products: encode multiple arguments to constructors
infixr 6 :**:
data (:**:) f g p ix = f p ix :**: g p ix
  deriving (Eq, Ord, Read, Show)

instance (Generic1m f, Generic1m g) => Generic1m (f :**: g) where
  type Rep1m (f :**: g) = (f :**: g)
  from1k = id
  to1k   = id

--- | Tags
data Tag1m (f :: (k -> *) -> k -> *) (xi :: k) (p :: k -> *) (ix :: k) where
  Tag1m :: f p ix -> Tag1m f ix p ix

instance Generic1m f => Generic1m (Tag1m f xi) where
  type Rep1m (Tag1m f xi) = Tag1m f xi
  from1k = id
  to1k   = id

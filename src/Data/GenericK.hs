{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.GenericK where

-- | Representable types of kind * -> *.
-- This class is derivable in GHC with the DeriveGeneric flag on.
class Generic1k (f :: (k -> *) -> (k -> *)) where
  -- | Generic representation type
  type Rep1k f (ix :: k) :: * -> *
  -- | Convert from the datatype to its representation
  from1k  :: f a ix -> (Rep1k f ix) (a ix)
  -- | Convert from the representation to the datatype
  to1k    :: (Rep1k f ix) (a ix) -> f a ix

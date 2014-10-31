{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Regex.MultiExample where

import Data.Regex.MultiGenerics
import Data.MultiGenerics

data Ty = One | Two
data instance Sing One = SOne
data instance Sing Two = STwo

instance SingI One where
  sing = SOne
instance SingI Two where
  sing = STwo

data Bis f ix where
  NilOne'  :: Bis f One
  ConsOne' :: Int  -> f Two -> Bis f One
  NilTwo'  :: Bis f Two
  ConsTwo' :: Char -> f One -> Bis f Two

type FixOne = Fix Bis One
type FixTwo = Fix Bis Two

instance ShowM (Fix Bis) where
  showM (Fix NilOne')        = "NilOne"
  showM (Fix (ConsOne' n r)) = "(ConsOne " ++ show n ++ " " ++ showM r ++ ")"
  showM (Fix NilTwo')        = "NilTwo"
  showM (Fix (ConsTwo' c r)) = "(ConsTwo " ++ show c ++ " " ++ showM r ++ ")"

pattern NilOne       = Fix NilOne'
pattern ConsOne x xs = Fix (ConsOne' x xs)
pattern NilTwo       = Fix NilTwo'
pattern ConsTwo x xs = Fix (ConsTwo' x xs)

aBis1 :: FixOne
aBis1 = NilOne

aBis2 :: FixOne
aBis2 = ConsOne 1 (ConsTwo 'a' NilOne)

rBis1 :: Regex Char Bis One
rBis1 = Regex $ capture 'a' $ inj NilOne'

rBis2 :: Regex c Bis One
rBis2 = Regex $ inj (ConsOne' 2 (inj NilTwo'))

rBis3 :: Regex c Bis One
rBis3 = Regex $ inj (ConsOne' 2 (inj (ConsTwo' 'a' (inj NilOne'))))

rBis4 :: Regex c Bis One
rBis4 = Regex $ inj NilOne' <||> inj NilOne'

instance Generic1m Bis where
  type Rep1m Bis =    Tag1m U1m One
                 :++: Tag1m (K1m () Int  :**: Par1m Two) One
                 :++: Tag1m U1m Two
                 :++: Tag1m (K1m () Char :**: Par1m One) Two

  from1k NilOne' = L1m $ Tag1m U1m
  from1k (ConsOne' x xs) = R1m $ L1m $ Tag1m (K1m x :**: Par1m xs)
  from1k NilTwo' = R1m $ R1m $ L1m $ Tag1m U1m
  from1k (ConsTwo' x xs) = R1m $ R1m $ R1m $ Tag1m (K1m x :**: Par1m xs)

  to1k (L1m (Tag1m U1m)) = NilOne'
  to1k (R1m (L1m (Tag1m (K1m x :**: Par1m xs)))) = ConsOne' x xs
  to1k (R1m (R1m (L1m (Tag1m U1m)))) = NilTwo'
  to1k (R1m (R1m (R1m (Tag1m (K1m x :**: Par1m xs))))) = ConsTwo' x xs

-- {-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.TreeRegex.Dump where

import GHC.Generics

data BisOne f = NilOne' | ConsOne' Int (BisTwo f)
  -- deriving Generic1

data BisTwo f = NilTwo' | ConsTwo' Char (BisOne f)
  -- deriving Generic1

instance Generic1 BisOne where
  type Rep1 BisOne = D1 D1BisOne
                        (   C1 C1_0BisOne U1
                        :+: C1 C1_1BisOne (   S1 NoSelector (Rec0 Int)
                                          :*: S1 NoSelector (Rec1 BisTwo)))
  from1 NilOne' = M1 (L1 (M1 U1))
  from1 (ConsOne' g1_a14a g2_a14b)
    = M1 (R1 (M1 ((:*:) (M1 (K1 g1_a14a)) (M1 (Rec1 g2_a14b)))))
  to1 (M1 (L1 (M1 U1))) = NilOne'
  to1 (M1 (R1 (M1 ((:*:) (M1 g1_a14c) (M1 g2_a14d)))))
    = ConsOne' (unK1 g1_a14c) (unRec1 g2_a14d)

instance GHC.Generics.Generic1 BisTwo where
  type Rep1 BisTwo = D1 D1BisTwo
                        (   C1 C1_0BisTwo U1
                        :+: C1 C1_1BisTwo (   S1 NoSelector (Rec0 Char)
                                          :*: S1 NoSelector (Rec1 BisOne)))
  from1 NilTwo' = M1 (L1 (M1 U1))
  from1 (ConsTwo' g1_a146 g2_a147)
    = M1 (R1 (M1 ((:*:) (M1 (K1 g1_a146)) (M1 (Rec1 g2_a147)))))
  to1 (M1 (L1 (M1 U1))) = NilTwo'
  to1 (M1 (R1 (M1 ((:*:) (M1 g1_a148) (M1 g2_a149)))))
    = ConsTwo' (unK1 g1_a148) (unRec1 g2_a149)

data D1BisOne
data C1_0BisOne
data C1_1BisOne
data S1_1_0BisOne
data S1_1_1BisOne

data D1BisTwo
data C1_0BisTwo
data C1_1BisTwo
data S1_1_0BisTwo
data S1_1_1BisTwo

instance Datatype D1BisOne where
  datatypeName _ = "BisOne"
  moduleName _ = "Data.TreeRegex.Dump"
  
instance Constructor C1_0BisOne where
  conName _ = "NilOne'"
  
instance Constructor C1_1BisOne where
  conName _ = "ConsOne'"

instance Datatype D1BisTwo where
  datatypeName _ = "BisTwo"
  moduleName _ = "Data.TreeRegex.Dump"

instance Constructor C1_0BisTwo where
  conName _ = "NilTwo'"

instance Constructor C1_1BisTwo where
  conName _ = "ConsTwo'"

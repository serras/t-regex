{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Attribute grammars with regular expression matching.
module Data.Regex.MultiRules (
  -- * Children maps
  Child(..),
  Children,
  lookupChild,
  -- * Basic blocks
  Action, Rule(..), Grammar,
  eval,
  -- * Nice syntax for defining rules
  rule, rule0,
  -- ** Combinators
  check,
  (->>>), (->>),
  -- ** Special lenses
  this, at,
  inh, syn,
  -- * Index-independent attributes
  IndexIndependent(..),
  IndexIndependentGrammar,
  iieval,
  inh_, syn_
) where

import Control.Applicative
import Control.Monad.State
import Data.Foldable (fold)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.MultiGenerics
import Data.Regex.MultiGenerics
import GHC.Exts (Constraint)

import Unsafe.Coerce

-- | A child records both an actual values and the index it corresponds to.
data Child (c :: k -> *) (attrib :: k -> *) where
  Child :: c ix -> [attrib ix] -> Child c attrib
-- | Children are just a list of 'Child's.
type Children c attrib = [Child c attrib]

lookupChild :: EqM c => c ix -> Children c attrib -> [attrib ix]
lookupChild _ [] = []
lookupChild c (Child ix info : rest) | c `eqM` ix = unsafeCoerce info
                                     | otherwise  = lookupChild c rest

insertChild :: EqM c => c ix -> [attrib ix] -> Children c attrib -> Children c attrib
insertChild k e [] = [Child k e]
insertChild k e (c@(Child ix _) : rest) | k `eqM` ix = Child k e : rest
                                        | otherwise  = c : insertChild k e rest

-- | Actions create new inherited attributes for their children,
--   and synthesized attribute for its own node, from the synthesized
--   attributes of children and the inheritance from its parent.
--   Additionally, actions may include an explicit backtrack.
type Action (c :: k -> *) (f :: (k -> *) -> k -> *) (inh :: k -> *) (syn :: k -> *) (ix :: k) =
  Fix f ix -> inh ix -> Children c syn -> (Bool, Children c inh, syn ix)
-- | A rule comprises the regular expression to match
--   and the action to execute if successful.
data Rule (c :: k -> *) (f :: (k -> *) -> k -> *) (inh :: k -> *) (syn :: k -> *) where
  Rule :: Regex c f ix -> Action c f inh syn ix -> Rule c f inh syn
-- | A grammar is simply a list of rules.
type Grammar (c :: k -> *) (f :: (k -> *) -> k -> *) (inh :: k -> *) (syn :: k -> *) =
  [Rule c f inh syn]

-- | Evaluate an attribute grammar over a certain term.
eval :: forall c f inh syn ix. Capturable c f
     => Grammar c f inh syn -> inh ix -> Fix f ix -> syn ix
eval grammar down term = fromJust $ foldr (<|>) empty $ map evalRule grammar
  where evalRule :: Rule c f inh syn -> Maybe (syn ix)
        evalRule (Rule regex action) = do  -- Maybe monad
          let regex'  = unsafeCoerce regex
              action' = unsafeCoerce action
          (captures :: [CaptureGroup c f []]) <- match regex' term
          let (ok, children, up) = action' term down $ map evalList captures
              evalList (CaptureGroup k subterms) = let [kInh] = lookupChild k children
                                                    in Child k $ map (eval grammar kInh) subterms
          guard ok
          return up


data InhAndSyn inh syn ix = InhAndSyn (inh ix) (syn ix)
data ActionState c inh syn ix = ActionState { _apply :: Bool
                                            , _this :: InhAndSyn inh syn ix
                                            , _rest :: Children c (InhAndSyn inh syn)
                                            }

-- | Lens for the attributes of the current node. To be used in composition with 'inh' or 'syn'.
this :: Functor f
     => (InhAndSyn inh syn ix -> f (InhAndSyn inh syn ix))
     -> ActionState c inh syn ix -> f (ActionState c inh syn ix)
this go (ActionState ok th rs) = (\x -> ActionState ok x rs) <$> go th
{-# INLINE this #-}

-- | Lens the attributes of a child node. To be used in composition with 'inh' or 'syn'.
at :: (EqM c, Functor f)
   => c xi -> (InhAndSyn inh syn xi -> f (InhAndSyn inh syn xi))
   -> ActionState c inh syn ix -> f (ActionState c inh syn ix)
at k go (ActionState ok th rs) = (\x -> ActionState ok th (insertChild k [x] rs)) <$> go (head $ lookupChild k rs)
{-# INLINE at #-}

-- | Lens for the inherited attributes of a node.
--   Use only as getter with 'this' and as setter with 'at'.
inh :: (Functor f) => (inh ix -> f (inh ix))
    -> InhAndSyn inh syn ix -> f (InhAndSyn inh syn ix)
inh go (InhAndSyn i s) = (\x -> InhAndSyn x s) <$> go i
{-# INLINE inh #-}

-- | Lens the inherited synthesized attributes of a node.
--   Use only as setter with 'this' and as getter with 'at'.
syn :: (Functor f) => (syn ix -> f (syn ix))
    -> InhAndSyn inh syn ix -> f (InhAndSyn inh syn ix)
syn go (InhAndSyn i s) = (\x -> InhAndSyn i x) <$> go s
{-# INLINE syn #-}

data IxList (c :: k -> *) :: [k] -> * where
  IxNil  :: IxList c '[]
  IxCons :: c ix -> IxList c rest -> IxList c (ix ': rest)

type family IxListMonoid (c :: k -> *) (ixs :: [k]) :: Constraint where
  IxListMonoid c '[] = ()
  IxListMonoid c (ix ': rest) = (Monoid (c ix), IxListMonoid c rest)

stateToAction :: (EqM c, IxListMonoid inh ixs, Monoid (syn ix), IxListMonoid syn ixs)
              => IxList c ixs
              -> (Fix f ix -> State (ActionState c inh syn ix) ())
              -> Action c f inh syn ix  -- Fix f ix -> inh ix -> Children c syn -> (Bool, Children c inh, syn ix)
stateToAction nodes st term down up = 
  let initialSyn = initialRest nodes up
      initial = ActionState True (InhAndSyn down mempty) initialSyn
      ActionState ok (InhAndSyn _ thisUp) rs = execState (st term) initial
   in (ok, finalDown nodes rs, thisUp)

initialRest :: (EqM c, IxListMonoid inh ixs, IxListMonoid syn ixs)
            => IxList c ixs -> Children c syn -> Children c (InhAndSyn inh syn)
initialRest IxNil _ = []
initialRest (IxCons c rest) children =
  Child c [InhAndSyn mempty (fold $ lookupChild c children)] : initialRest rest children

finalDown :: EqM c => IxList c ixs -> Children c (InhAndSyn inh syn) -> Children c inh
finalDown IxNil _ = []
finalDown (IxCons c rest) children =
  Child c [ firstInh $ lookupChild c children ] : finalDown rest children
  where firstInh [InhAndSyn s _] = s
        firstInh _ = error "This should never happen"

-- | Separates matching and attribute calculation on a rule.
--   The action should take as extra parameter the node which was matched.
(->>>) :: forall f (ix :: k) inh syn (ixs :: [k])
        . (IxListMonoid inh ixs, Monoid (syn ix), IxListMonoid syn ixs)
       => (forall c. Regex' c (Wrap Integer) f ix)
       -> (Fix f ix -> State (ActionState (Wrap Integer) inh syn ix) ())
       -> IxList (Wrap Integer) ixs -> Rule (Wrap Integer) f inh syn
(rx ->>> st) nodes = Rule (Regex rx) (stateToAction nodes st)

-- | Separates matching and attribute calculation on a rule.
(->>) :: forall f (ix :: k) inh syn (ixs :: [k])
       . (IxListMonoid inh ixs, Monoid (syn ix), IxListMonoid syn ixs)
      => (forall c. Regex' c (Wrap Integer) f ix)
      -> State (ActionState (Wrap Integer) inh syn ix) ()
      -> IxList (Wrap Integer) ixs -> Rule (Wrap Integer) f inh syn
(rx ->> st) nodes = (rx ->>> const st) nodes

-- | Makes the attribute calculation fail if the condition is false.
--   This function can be used to add extra conditions over whether
--   a certain rule should be applied (a bit like guards).
check :: Bool -> State (ActionState (Wrap Integer) inh syn ix) ()
check ok = modify (\(ActionState _ th rs) -> ActionState ok th rs)


-- | Utility type which does not distinguish between indices.
newtype IndexIndependent t ix = IndexIndependent t deriving (Show, Eq, Ord, Monoid)

-- | A grammar whose attributes are equal throughout all indices.
type IndexIndependentGrammar c f inh syn = Grammar c f (IndexIndependent inh) (IndexIndependent syn)

-- | Evaluate an index-indendepent grammar.
iieval :: forall c f inh syn ix. Capturable c f
       => IndexIndependentGrammar c f inh syn -> inh -> Fix f ix -> syn
iieval g down t = up where IndexIndependent up = eval g (IndexIndependent down) t

-- | Lens for 'Indexed' inherited attributes of a node.
--   Use only as getter with 'this' and as setter with 'at'.
inh_ :: (Functor f) => (inh -> f inh)
     -> InhAndSyn (IndexIndependent inh) syn ix -> f (InhAndSyn (IndexIndependent inh) syn ix)
inh_ go (InhAndSyn (IndexIndependent i) s) = (\x -> InhAndSyn (IndexIndependent x) s) <$> go i
{-# INLINE inh_ #-}

-- | Lens the 'Indexed' synthesized attributes of a node.
--   Use only as setter with 'this' and as getter with 'at'.
syn_ :: (Functor f) => (syn -> f syn)
     -> InhAndSyn inh (IndexIndependent syn) ix -> f (InhAndSyn inh (IndexIndependent syn) ix)
syn_ go (InhAndSyn i (IndexIndependent s)) = (\x -> InhAndSyn i (IndexIndependent x)) <$> go s
{-# INLINE syn_ #-}


class RuleBuilder (f :: (k -> *) -> k -> *) (inh :: k -> *) (syn :: k -> *) (ixs :: [k]) fn | fn -> ixs where
  -- | Converts a rule description into an actual 'Rule'.
  --   Its use must follow this pattern:
  --
  --     * A block of lambda-bound variables will introduce the capture names,
  --     * A tree regular expression to match should capture using the previous names,
  --     * After '->>>' or '->>', the state calculation should proceed.
  --
  --   > rule $ \c1 c2 ->
  --   >   regex ... c1 <<- ... c2 <<- ... ->> do
  --   >     at c2 . inh .= ...          -- Set inherited for children
  --   >     c1Syn <- use (at c1 . syn)  -- Get synthesized from children
  --   >     this . syn  .= ...          -- Set upwards synthesized attributes
  rule :: (fn -> IxList (Wrap Integer) ixs -> Rule (Wrap Integer) f inh syn) -> Rule (Wrap Integer) f inh syn

{- Does not fulfill coverage condition
instance RuleBuilder f inh syn '[] () where
  rule r = r () IxNil
-}

-- | Special case for rules without capture.
rule0 :: (IxList (Wrap Integer) '[] -> Rule (Wrap Integer) f inh syn) -> Rule (Wrap Integer) f inh syn
rule0 r = r IxNil

instance RuleBuilder f inh syn '[ix1] (Wrap Integer ix1) where
  rule r = r (Wrap 1) (IxCons (Wrap 1) IxNil)

instance RuleBuilder f inh syn '[ix1, ix2] (Wrap Integer ix1, Wrap Integer ix2) where
  rule r = r (Wrap 1, Wrap 2) (IxCons (Wrap 1) ((IxCons (Wrap 2)) IxNil))

instance RuleBuilder f inh syn '[ix1, ix2, ix3]
         (Wrap Integer ix1, Wrap Integer ix2, Wrap Integer ix3) where
  rule r = r (Wrap 1, Wrap 2, Wrap 3) (IxCons (Wrap 1) (IxCons (Wrap 2) (IxCons (Wrap 3) IxNil)))

instance RuleBuilder f inh syn '[ix1, ix2, ix3, ix4]
         (Wrap Integer ix1, Wrap Integer ix2, Wrap Integer ix3, Wrap Integer ix4) where
  rule r = r (Wrap 1, Wrap 2, Wrap 3, Wrap 4)
             (IxCons (Wrap 1) (IxCons (Wrap 2) (IxCons (Wrap 3) (IxCons (Wrap 4) IxNil))))

instance RuleBuilder f inh syn '[ix1, ix2, ix3, ix4, ix5]
         (Wrap Integer ix1, Wrap Integer ix2, Wrap Integer ix3, Wrap Integer ix4, Wrap Integer ix5) where
  rule r = r (Wrap 1, Wrap 2, Wrap 3, Wrap 4, Wrap 5)
             (IxCons (Wrap 1) (IxCons (Wrap 2) (IxCons (Wrap 3) (IxCons (Wrap 4) (IxCons (Wrap 5) IxNil)))))

`t-regex`: matchers and grammars with tree regular expressions
==============================================================

`t-regex` defines a series of combinators to express tree regular
expressions over any Haskell data type. In addition, with the use
of some combinators (and a bit of Template Haskell), it defines
nice syntax for using this tree regular expressions for matching
and computing attributes over a term.

In order to use `t-regex`, you need to define you data type in a
way amenable to inspection. In particular, it means that instead
of a closed data type, you need to define a *pattern functor* in
which recursion is described using the final argument, and which
should instantiate the `Generic1` type class (this can be done
automatically if you are using GHC).

For example, the following block of code defines a `Tree'` data
type in the required fashion:
```haskell
{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics

data Tree' f = Leaf'
             | Branch' { elt :: Int, left :: f, right :: f }
             deriving (Generic1, Show)
```
Notice the `f` argument in the place where `Tree'` would usually be
found. In addition, we have declared the constructors using `'` at
the end, but we will get rid of them soon.

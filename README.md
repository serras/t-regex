`t-regex`: matchers and grammars using tree regular expressions
===============================================================

`t-regex` defines a series of combinators to express tree regular
expressions over any Haskell data type. In addition, with the use
of some combinators (and a bit of Template Haskell), it defines
nice syntax for using this tree regular expressions for matching
and computing attributes over a term.

## Defining your data type

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

Now, if you want to create terms, you need to *close* the type, which
essentially makes the `f` argument refer back to `Tree'`. You do so
by using `Fix`:
```haskell
type Tree = Fix Tree'
```
However, this induces the need to add explicit `Fix` constructors at
each level. To alleviate this problem, let's define *pattern synonyms*,
available from GHC 7.8 on:
```haskell
pattern Leaf = Fix Leaf'
pattern Branch n l r = Fix (Branch' n l r)
```
From an outsider point of view, now your data type is a normal one,
with `Leaf` and `Branch` as its constructors:
```haskell
aTree = Branch 2 (Branch 2 Leaf Leaf) Leaf
```

## Tree regular expressions

Tree regular expressions are parametrized by a pattern functor: in this
way they are flexible enough to be used with different data types,
while keeping our loved Haskell type safety.

The available combinators to build regular expressions follow the syntax
of [Tree Automata Techniques and Applications](http://tata.gforge.inria.fr/),
Cahpter 2.

### Emptiness

The expressions `empty_` and `none` do not match any value. They can be
used to signal an error branch on an expressions.

### Whole language

You can match any possible term using `any_`. It is commonly use in
combination with `capture` to extract information from a term.

### Choice

A regular expression of the form `r1 <||> r2` tries to match `r1`, and if
it not possible, it tries to do so with `r2`. Note than when capturing,
the first regular expression is given priority.

### Iteration and concatenation

Iteration in tree regular expressions is not as easy as in word languages.
The reason is that iteration may occur several times, and in different
positions. For that reason, we need to introduce the notion of *hole*: a
hole is a placeholder where iteration takes place.

In `t-regex` hole names are represented as lambda-bound variables. Then,
you can use any of the functions `square`, `var` or `#` to indicate a
position where the placeholder should be put. Iteration is then indicated
by a call to `iter` or its post-fix version `^*`.

The following two are ways to indicate a `Tree` where all internal nodes
include the number `2`:
```haskell
{-# LANGUAGE PostfixOperators #-}

regex1 = Regex $
           iter $ \k ->
                  inj (Branch' 2 (square k) (square k))
             <||> inj Leaf'

regex2 = Regex $ ( (\k -> inj (Branch' 2 (k#) (k#)) <||> inj Leaf')^* )
```
Notice that the use of `PostfixOperators` enables a much terse language.

## Matching and capturing

## Attribute grammars

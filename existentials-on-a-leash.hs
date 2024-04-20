{- [markdown]
# Existentials on a leash

In this article, I will share a trick to enable for more flexible use of existentially quantified type variables in Haskell.

In short, we can introduce an existentially quantified type variable (let's say existential type) outside of the scope of a function of which we would like the return type to contain an existential type.
This separation allows us to push the hassle of using continuation-passing style (CPS) or wrapping the result in a GADT outward from the usage site of the function.
Linear types are employed to make this safe, though I have not proven anything formally.
Please try to break this stuff if you see some hole I have missed.

At first glance, this separation may only seem like a small convenience, but we will see that being able to wrap a result in a GADT later then would otherwise be necessary can make a real difference for the strictness of a function.

Additionally, there are cases where using CPS or GADT wrappers is too disruptive for a function to be useful.
For example, lenses and other optics are often chained together using `(.)` and it would be very clunky to have to unwrap a GADT in the middle of such a chain.
So, by allowing us to move this unwrapping somewhere else, this pattern allows us to define optics that would otherwise be too awkward to use.

This article also serves as the presentation of an optic combinator that makes use of this technique and I haven't seen anywhere else.
Basically, it's a generalization of [`alongside`](https://hackage.haskell.org/package/lens-5.2.3/docs/Control-Lens-Combinators.html#v:alongside)`:: LensLike (AlongsideLeft f b') s t a b -> LensLike (AlongsideRight f t) s' t' a' b' -> LensLike f (s, s') (t, t') (a, a') (b, b') `  to any traversal.
In category theory jargon, you could say that `alongside` translates a product on lenses to a product on the source and focus types of a lens.
The generalized version does the same for traversals, but since two traversal may target a different number of values, the product on the foci types becomes a (constructor-indexed) variant of [These](https://hackage.haskell.org/package/these-1.2/docs/Data-These.html#t:These).

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs and optics (for the sections pertaining to them) is recommended.

That being said, made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a GitHub Codespace prebuild (EU/NA?) (todo) and GitPod (other continents).
Clicking either of these links will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser.

## Current limitations of existential types

As of GHC 9.10, GHC only supports 2 limited ways of existentially quantifying type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This is equivalent to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

[A proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding existential types to GHC was made a while ago, but the author is now prioritizing other work.
We will reuse the example of length-indexed vectors from the proposal, but first, the language extensions and imports used in this article:

todo: remove ghc-typelits-presburger ghc-typelits-knownnat if not needed
todo: prisms for GADTs
-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall -Wno-missing-signatures -XNoImplicitPrelude #-}

-- These are only used for the examples with length-indexed vectors, not required to use this trick in general
-- {-# OPTIONS_GHC -fplugin Data.Type.Natural.Presburger.MinMaxSolver #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import Control.Lens qualified as Lens
import Data.Sized as Sized
import GHC.TypeNats
import Prelude.Linear
import Unsafe.Coerce (unsafeCoerce)
import Prelude qualified as NL

-- import Data.Type.Natural

import Control.Subcategory
import Data.Kind
import Data.Type.Equality
import Data.Unrestricted.Linear

{- [markdown]
We can use the standard definition of length-indexed vectors:
-}

data Nat' = Zero | Succ Nat'

type Vec :: Nat' -> Type -> Type
data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

{- [markdown]
Suppose we want to define a function to convert a normal list to a length-indexed vector.
Because we don't know the length of the list at the type level, we would like this function to have the type: `fromList :: exists n. [a] -> Vec n a`.
Instead we will have to use either CPS, yielding `fromList :: [a] -> (forall n. Vec n a -> r) -> r`, or a GADT wrapper type, yielding `fromList :: [a] -> SomeVec a`.
Let's work out the second option.
-}

data SomeVec a where
  SomeVec :: forall n a. Vec n a -> SomeVec a

vecFromList :: [a] -> SomeVec a
vecFromList [] = SomeVec VNil
vecFromList (a : as) =
  vecFromList as & \(SomeVec aVec) -> SomeVec $ VCons a aVec

{- [markdown]
While pattern matching on `SomeVec aVec` at every usage site is a bit tedious, what's more important here is that it makes the function "unnecessarily" strict in the length of the list.
We have no other choice though.
`SomeVec $ fromList as & \(SomeVec aVec) -> VCons a aVec` can not be typed because the `n` tied to the unwrapped `SomeVec` would escape its scope.

`vecFromList` would also become lazy if could unwrap the recursive call before we pattern match on the input list, but this is also not possible, because we need the tail of the list to write the recursive application.

It turns out that a CPS-variant would also be useless in this case, because the given continuation needs to applied to the final `Vec`, so we would need to compute that with a function like the one above first.

As the author of the existential types proposal states (for a `filter` function, which has the same problem), it's not possible to define a lazy version of `vecFromList` in GHC's current type system.

> So we have to work around it 😈

## Putting existentials on a leash

Essentially, we *have* to make the length of the vector visible in the return type of `vecFromList`.
GHC only offers universal quantification for such a type variable, but, somehow, we need to make it impossible for the caller of `vecFromList` to choose a specific type for this variable, so `vecFromList` can make this choice.
To accomplish this, we start with a proxy type `Fresh` which can only be introduced with an existential type as parameter.

```haskell
newtype Fresh a = Fresh

withFresh :: (forall a. Fresh a -> r) -> r
withFresh f = Fresh
```

This proxy will serve as a proof-witness that the associated type variable was existentially quantified.
The type of `vecFromList` becomes `forall n a. Fresh n -> [a] -> Vec n a` and the burden of the existential quantification is pushed outward to the caller.
This effectively enlarges the scope of the existential type to wherever the caller (or even its caller) decides to introduce the existential type using `withFresh`.
Through passing the existential quantification witness as an argument to where it is eventually used, we create the leash from which this technique and article get their name.

Now, we need a way for `vecFromList` to choose a type for `n`.
Since it is a concrete type (chosen by the caller according to GHC), our only option is `unsafeCoerce`.

Putting the dangers of this approach aside for a moment, given a value of `Fresh n`, we should allow `n` to be coerced to some other type `b`, but in `vecFromList` we don't have values of type `n`, only `Vec n a`.
We could define `castVec :: Fresh n -> Vec n a -> Vec n' a`, but ideally an existential types workaround would be specific to the example of length-indexed vectors.
This can be accomplished by providing a type equality witness (from `Data.Type.Equality`) instead of a specific casting function.

We arrive at:
```haskell
newtype Fresh a = Fresh (forall b. a :~: b)

withFresh :: (forall a. Fresh a -> r) -> r
withFresh f = f (Fresh $ unsafeCoerce Refl)
```

Using `Data.Type.Equality.castWith`, we can now perform unsafe coercions for any instance of `a` for which we have a `Fresh a`!
Now, we only need to remove the word "unsafe" from that sentence.

I believe it's sufficient to ensure that the existential quantification witness is used at most once.
Until we use the witness, no values of type `a` can exist because it was existentially quantified.
Types `f` that are parameterized by `a` can have values, but such values must be independent of `a` for the same reason.
As long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

However, it is possible to get multiple *different* values of `f b` and until I tried it, I thought that this could lead to contradicting type equalities if `f` was a GADT.
Let me show my attempt:
```haskell
data GADT a where
  Int :: GADT Int
  Char :: GADT Char

data Wrapper where
  Wrapper :: forall a. (Bool -> GADT a) -> Wrapper

wrapper :: Wrapper
wrapper =
  withFresh
    ( \(Fresh fresh :: Fresh a) ->
        Wrapper @a
          ( \b ->
              if b then gcastWith (fresh @Int) Int else gcastWith (fresh @Char) Char
          )
    )

conflict :: Int :~: Char
conflict =
  wrapper & \(Wrapper @a (f :: Bool -> GADT a)) ->
    let
      int = f True :: GADT a
      char = f False :: GADT a
      l = [char, int]
    in trans
      ( case int of
          Int -> Refl :: Int :~: a
      )
      ( case char of
          Char -> Refl :: Char :~: a
      )
```

GHC gives the following type errors:
```
• Couldn't match type ‘b0’ with ‘Int’
  Expected: Int :~: b0
    Actual: Int :~: a
• In the expression: Refl :: Int :~: a
  In a case alternative: Int -> Refl :: Int :~: a
  In the first argument of ‘trans’, namely
    ‘(case int of Int -> Refl :: Int :~: a)’
```

```
• Couldn't match type ‘b0’ with ‘Char’
  Expected: b0 :~: Char
    Actual: Char :~: a
• In the expression: Refl :: Char :~: a
  In a case alternative: Char -> Refl :: Char :~: a
  In the second argument of ‘trans’, namely
    ‘(case char of Char -> Refl :: Char :~: a)’
```

In the pattern match of `Int`, GHC does not generate the constraint `Int ~ a`, but it uses a fresh type variable `b0` and generates `Int ~ b0` instead.
I'm not sure why it does this, but I'm happy it does because otherwise I don't think I can make this trick safe.

Which leaves me to show how to ensure the existential quantification witness is used at most once: linear types.
We finally arrive at the real version of `Fresh` and `withFresh`:
-}

--todo: constructor should be hidden because otherwise it's Dupable
newtype Fresh a = Fresh (forall b. a :~: b)

withFresh :: (forall a. Fresh a %1 -> r) %1 -> r
withFresh f = f $ Fresh NL.$ unsafeCoerce Refl

castFresh :: forall b r a. Fresh a %1 -> ((a ~ b) => r) -> Ur r
castFresh (Fresh (Refl :: a :~: b)) r = Ur r

{- [markdown]
The linear arrow `%1 ->` ensures that `Fresh $ unsafeCoerce Refl` is used exactly once in the function `f` (if the result of type `r` is completely evaluated).

If we try to use it more than once, we get a type error:
```haskell
-- todo: rework to True ~ False
conflict =
  withFresh
    ( \(fresh :: Fresh a) ->
        castFresh @Int @(Int :~: a) fresh Refl & \(Ur intEqualsA) ->
        castFresh @Char @(a :~: Char) fresh Refl & \(Ur aEqualsChar) ->
          let
            Refl = trans intEqualsA aEqualsChar :: Int :~: Char
          in
            error "Int /= Char"
    )
```
```
• Couldn't match type ‘Many’ with ‘One’
    arising from multiplicity of ‘fresh’
• In the pattern: fresh :: Fresh a
  In the first argument of ‘withFresh’, namely
    ‘(\ (fresh :: Fresh a)
        -> castFresh @Int @(Int :~: a) fresh Refl
             & \ (Ur intEqualsA)
                 -> castFresh @Char @(a :~: Char) fresh Refl
                      & \ (Ur aEqualsChar) -> ...)’
  In the expression:
    withFresh
      (\ (fresh :: Fresh a)
         -> castFresh @Int @(Int :~: a) fresh Refl
              & \ (Ur intEqualsA)
                  -> castFresh @Char @(a :~: Char) fresh Refl
                       & \ (Ur aEqualsChar) -> ...)
```
Note that the constructor `Fresh` is linear (because it's a `newtype`).
Therefore, pattern matching on `(Fresh f)` still requires linear use of `f`.

Now we can define a lazy version of `vecFromList`
-}

lazyVecFromList :: Fresh n %1 -> [a] -> Ur (Vec n a)
lazyVecFromList fresh [] = castFresh @Zero fresh VNil
lazyVecFromList fresh (a : as) =
  withFresh
    ( \(freshPredN :: Fresh predN) ->
        lazyVecFromList freshPredN as
          & ( \(Ur asVec) ->
                castFresh @(Succ predN) fresh (VCons a asVec)
            )
    )

tryHead :: Vec n a -> Maybe a
tryHead VNil = Nothing
tryHead (VCons x _) = Just x

lazyVecFromListIsLazy :: Maybe Int
lazyVecFromListIsLazy = unur $ withFresh (\fresh -> lift tryHead $ lazyVecFromList fresh [0, undefined])

-- lTest :: Int -> Fresh n ->  Int
-- lTest x (Fresh f) = 3

-- lTest2 :: Int %1 -> Int
-- lTest2 x = withFresh (\f -> lTest x f)

-- >>> lazyVecFromListIsLazy
-- Just 0

{- [markdown]
The recursive case has become a little more complicated: we need an extra existential type to pass to the recursive application of `lazyVecFromList`.
We can't use the one we got as an argument, because we need it to cast `VCons a (lazyVecFromList freshPredN as) :: Vec (n - 1) a` to `Vec n a` and we can only use it once.

I will admit that linear types are also not an ideal solution, both in theory and in practice.
On the theoretical part, affine types would be much better suited, because an affine function arrow would allow the argument to not be used.
Because linear types require that the argument is used exactly once, we need to use `Ur` everywhere so the caller can use the returned value without restrictions.

On the practical part, it's simply difficult to work with linear types at the moment because the implementation in GHC is still very "bare-bones".
For those unaware, I'll name just a few issues:
  * There is no multiplicity inference yet. In other words, we need to redefine every function we want to use using only linear functions.
  * As you can see above, the error messages don't say exactly where something is wrong. Just that some value was not used linearly.
  * Multiplicity polymorphism is not reliable yet.

todo: linear constraints
Luckily, we can relieve users of functions that use this kind of existential quantification from dealing with linear types, by wrapping the functions in a GADT:
-}

-- data Exists f where
--   Exists :: f a -> Exists f

type family ResultsIn f a where
  ResultsIn f (f a) = f a
  ResultsIn f (a -> b) = a -> ResultsIn f b
  ResultsIn f a = f a

newtype Exists a r = Exists (Fresh a %1 -> r)

-- instance NL.Functor (Exists a) where
--   fmap f (Exists e) = Exists (\fresh -> f $ unurResult $ e fresh)

-- mapExists :: Unrestricting r => (r -> s) -> Exists a r -> Exists a s
-- mapExists f (Exists e) = Exists $ liftToResult f e

class Unrestricting r where
  type UnuredResult r
  type InUr r
  type UnuredResult' r
  type ReplaceResult b r
  unurResult :: r %1 -> UnuredResult r
  liftToResult :: (UnuredResult' r -> b) -> r %1 -> ReplaceResult b r

instance Unrestricting (Ur r) where
  type UnuredResult (Ur r) = r
  type InUr (Ur r) = Ur r
  type UnuredResult' (Ur r) = r
  type ReplaceResult b (Ur r) = Ur b
  unurResult = unur
  liftToResult = lift

instance (Unrestricting b) => Unrestricting (a -> b) where
  type UnuredResult (a -> b) = a -> UnuredResult b
  type InUr (a -> b) = a -> InUr b
  type UnuredResult' (a -> b) = UnuredResult' b
  type ReplaceResult c (a -> b) = a -> ReplaceResult c b
  unurResult f a = unurResult $ f a
  liftToResult mapR f a = liftToResult mapR $ f a

instance Unrestricting b => Unrestricting (a %1 -> b) where
  type UnuredResult (a %1 -> b) = a %1 -> UnuredResult b
  type InUr (a %1 -> b) = a %1 -> InUr b
  type UnuredResult' (a %1 -> b) = UnuredResult' b
  type ReplaceResult c (a %1 -> b) = a %1 -> ReplaceResult c b
  unurResult f a = unurResult $ f a
  liftToResult mapR f a = liftToResult mapR $ f a

-- getExists :: (UnurResult (ResultsIn Ur r)) => (forall a. Exists a r) -> UnuredResult (ResultsIn Ur r)
-- getExists e = unurResult $ withFresh (e & \(Exists f) -> f)

withExists :: (forall a. (Exists a (Ur r), r -> r')) -> r'
withExists t = withFresh (\fresh -> t & \(Exists f, rTor') -> f fresh & \(Ur r) -> rTor' r)

m :: (forall a. Fresh a %1 -> b -> Ur c) -> ((b -> c) -> d) -> d
m f c = c (\b -> unur $ withFresh f b)

lazyVecFromList2 :: Exists n ([a] -> Ur (Vec n a))
lazyVecFromList2 = Exists lazyVecFromList

lazyVecFromListIsLazy2 = m lazyVecFromList (\tov -> tryHead (tov []))

-- lazyVecFromListIsLazy2 :: Maybe Int
-- lazyVecFromListIsLazy2 =
--   let
--     x = lazyVecFromList2 :: forall n a. Exists n ([a] -> Vec n a)
--   in
--     (\vecFromList -> undefined $ tryHead $ vecFromList ['c', undefined]) (getExists x)

-- data VecFromList a where
--   VecFromList :: forall n a. ([a] -> Vec n a) %1 -> VecFromList a

-- lazyVecFromList' :: VecFromList a
-- lazyVecFromList' = withFresh (\(fresh :: Fresh a) -> VecFromList (lazyVecFromList fresh))

-- unsafeListHead =
--   lazyVecFromList' & \(VecFromList vecFromList') -> tryHead' $ vecFromList' unsafeTestList

{- [markdown]
Note that `tryHead'` is not linear.
-}

-- data Batching s a b r = forall n. KnownNat n => Batching (Sized s n a) (Sized s n b -> r)

-- request :: (Dom s a, Dom s b, CPointed s, CFoldable s) => a -> Batching s a b b
-- request a = Batching (singleton a) Sized.head

-- instance Functor (Batching s a b) where
--   fmap f (Batching as bsr) = Batching as (f . bsr)

-- instance (Dom s a, CFreeMonoid s, Dom s b) => Applicative (Batching s a b) where
--   pure x = Batching empty (const x)
--   Batching as1 bsf <*> Batching as2 bsr = Batching (Sized.append as1 as2) $ \bs ->
--     let
--       (bs1, bs2) = Sized.splitAt (Sized.sLength as1) bs
--     in
--     _

-- newtype SizePreservingF g s a b n = SizePreservingF (Sized s n a -> g (Sized s n b))

-- partsOf :: forall f s t a b n. Functor f
--         => Fresh n
--         -> Traversing (->) f s t a b
--         -> LensLike f s t (Sized [] n a) (Sized [] n b)
-- partsOf fresh o f s =
--   let --(t, (aVec, bVec)) = flip runState abList2 $ traverseOf o step s
--     g :: forall z. Sized [] z a -> f (Sized [] z b)
--     g as = innerCoerce (bindFresh fresh) (SizePreservingF f) & \(SizePreservingF h) -> h as
--     x = g empty
--     y = g $ singleton undefined
--     t = undefined
--   in t

{- [markdown]

-}

data TheseTag
  = ThisTag
  | ThatTag
  | TheseTag
  deriving (Show)

-- These with tagged constructors, so a function can only map to the same constructor as the argument it receives
data TaggedThese tag a b where
  This :: a -> TaggedThese 'ThisTag a b
  That :: b -> TaggedThese 'ThatTag a b
  These :: a -> b -> TaggedThese 'TheseTag a b

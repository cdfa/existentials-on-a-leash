{- [markdown]
# Existentials on a leash

In this article, I will share a trick to enable more flexible use of existentially quantified type variables in Haskell, which allows them to appear "naked" (without CPS-style/GADT wrapping) in a type signature.
Furthermore, I demonstrate a method for defining optics over types containing existentially quantified variables (though without having them appear naked in the type signature).

Both these techniques rely on witness-values passed linearly through some function.
I believe the linear use of these witnesses makes the use of unsafe functions in these techniques safe, though I have not proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs and optics (for the sections pertaining to them) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a GitHub Codespace prebuild (EU/NA?) (todo) and GitPod (other continents).
Clicking either of these links will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser.

## Current limitations of existential types

As of GHC 9.12, GHC only supports 2 limited ways of existentially quantifying type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This is equivalent to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

[A proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding existential types to GHC was made a while ago, but the author is now prioritizing other work.
We will reuse the example of length-indexed vectors from the proposal, but first, the language extensions and imports used in this article:

<details>
<summary>Imports</summary>

-}
{-# OPTIONS_GHC -Wall -Wno-missing-signatures -Wno-unused-top-binds -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

{- cabal:
ghc-options: -Wall
default-language: GHC2024
build-depends:
  base,
  linear-base,
  lens,
  batching,
  short-vec,
  fin-int,
-}
{- project:
with-compiler: ghc-9.12.2

semaphore: True

allow-newer:
  base,
  primitive,
  containers,
  deepseq,

constraints:
  constraints >=0.14,
-}

import Control.Batching
import Control.Functor.Linear qualified as Linear.Control
import Control.Lens qualified as Lens
import Data.Char
import Data.Fin.Int
import Data.Function
import Data.Functor ((<&>))
import Data.Functor.Identity
import Data.Kind
import Data.Type.Equality
import Data.Unrestricted.Linear
import Data.Vec.Short qualified as V
import GHC.Base
import Prelude.Linear qualified as L
import Unsafe.Coerce (unsafeCoerce)

{- [markdown]
</details>

Length-indexed vectors as defined in the existential types proposal:

-}

data Nat = Zero | Succ Nat

type Vec :: Nat -> Type -> Type
data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

{- [markdown]
Suppose we want to define a function to convert a normal list to a length-indexed vector.
Because we don't know the length of the list at the type level, we would like this function to have the type: `fromList :: exists n. [a] -> Vec n a`.
Since GHC does not yet support existential types, we will have to use either CPS, yielding `fromList :: [a] -> (forall n. Vec n a -> r) -> r`, or a GADT wrapper type, yielding `fromList :: [a] -> SomeVec a`.
Let's work out the second option.
-}

data SomeVec a where
  SomeVec :: forall n a. Vec n a -> SomeVec a

vecFromList :: [a] -> SomeVec a
vecFromList [] = SomeVec VNil
vecFromList (a : as) =
  vecFromList as & \(SomeVec aVec) -> SomeVec $ VCons a aVec

{- [markdown]
Pattern matching on `SomeVec aVec` at every usage site is not only tedious, but it also makes the function unnecessarily strict in the length of the list.
We have no other choice though.
`SomeVec $ vecFromList as & \(SomeVec aVec) -> VCons a aVec` can not be typed because the `n` tied to the unwrapped `SomeVec` would escape its scope.

It turns out that a CPS-variant would also be useless in this case, because the given continuation can't be applied before the recursive application of `vecFromList`.

As the author of the existential types proposal states (for a `filter` function, which has the same problem), it's not possible to define a lazy version of `vecFromList` in GHC's current type system.

*So we have to work around it.*

## Putting existentials on a leash

Essentially, we *have* to make the length of the vector visible in the return type of `vecFromList`.
GHC only offers universal quantification for such a type variable, but somehow, we need to make it impossible for the caller of `vecFromList` to choose a specific type for this variable, so `vecFromList` can make this choice.
To accomplish this, we start with a proxy type `Fresh` which can only be introduced with an existential type as parameter.

```haskell
newtype Fresh a = Fresh

withFresh :: (forall a. Fresh a -> r) -> r
withFresh f = Fresh
```

This proxy will serve as a proof-witness that the associated type variable was existentially quantified.
The type of `vecFromList` becomes `forall n a. Fresh n -> [a] -> Vec n a` and the burden of the existential quantification is pushed outward to the caller.
This effectively enlarges the scope of the existential type to wherever the caller (or even its caller) decides to introduce the existential type using `withFresh`.
By passing the existential quantification witness as an argument to where it is eventually used, we create the leash from which this technique and article get their name.

Now, we need a way for `vecFromList` to choose a type for `n`.
Since it is a concrete type (instantiated at the call site), our only option is `unsafeCoerce`.

Putting the dangers of this approach aside for a moment, given a value of `Fresh n`, we should allow `n` to be coerced to some other type `b`, but in `vecFromList` we don't have values of type `n`, only `Vec n a`.
We could define `castVec :: Fresh n -> Vec n a -> Vec n' a`, but ideally an existential types workaround would not be specific to the example of length-indexed vectors.
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
Values of a types `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
As long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

We can ensure this by requiring that a `Fresh a` is used linearly and hiding the constructor, like so:
-}

newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

withFresh :: (forall a. Fresh a %1 -> r) %1 -> r
withFresh f = f L.$ Fresh $ unsafeCoerce Refl

castFresh :: forall b r a. Fresh a %1 -> ((a ~ b) => r) -> Ur r
castFresh (Fresh (Refl :: a :~: b)) r = Ur r

{- [markdown]
The function `castFresh` is needed to replace `Data.Type.Equality.castWith` since the user can't get the `a :~: b` from `Fresh` anymore since the constructor is hidden.

I spent some time trying to find a way this is unsafe, and I think one attempt is worth showing because I was surprised that it failed.
While the linear function prevents using the existential quantification witness more than once, it can be used differently in different branches of the program and I thought one could use this to generate incorrect type equalities.
For example, GHC does not allow a function like `test`:

<!-- ```haskell -->
-}
data GADT a where
  Int :: GADT Int
  Char :: GADT Char

-- test :: Bool -> GADT a
-- test b = if b then Int else Char
{-
```

However, using an existential quantification witness, something like that becomes possible:

<!-- ```haskell -->
-}
data Wrapper where
  Wrapper :: forall a. (Bool -> GADT a) %1 -> Wrapper

wrapper :: Wrapper
wrapper =
  withFresh
    ( \(fresh :: Fresh a) ->
        Wrapper @a
          ( test fresh
          )
    )

test :: Fresh a %1 -> Bool -> GADT a
test fresh b = unur L.$ if b then castFresh @Int fresh Int else castFresh @Char fresh Char

conflict :: Int :~: Char
conflict =
  wrapper & \(Wrapper @a (f :: Bool -> GADT a)) ->
    let
      int = f True :: GADT a
      char = f False :: GADT a
    in trans @Int @a @Char
      ( case int of
          Int -> Refl :: Int :~: a
      )
      ( case char of
          Char -> Refl :: a :~: Char
      )
{-
<!-- ``` -->

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

Which leaves me to show how to ensure the existential quantification witness is used at most once: linear functions.
We finally arrive at the real definition of `Fresh` and `withFresh`:
-}

-- newtype Fresh a = Fresh (forall b. a :~: b)

-- withFresh :: (forall a. Fresh a %1 -> r) %1 -> r
-- withFresh f = f L.$ Fresh $ unsafeCoerce Refl

-- byFresh :: forall b a. Fresh a %1 -> Ur (a :~: b)
-- byFresh (Fresh (Refl :: a :~: b)) = Ur Refl

-- castFresh :: forall b r a. Fresh a %1 -> ((a ~ b) => r) -> Ur r
-- castFresh (Fresh (Refl :: a :~: b)) r = Ur r

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

type Exists a b = Fresh a %1 -> Ur b

lazyVecFromList :: [a] -> Exists n (Vec n a)
lazyVecFromList [] fresh = castFresh @Zero fresh VNil
lazyVecFromList (a : as) fresh =
  withFresh
    ( \(freshPredN :: Fresh predN) ->
        lazyVecFromList as freshPredN
          L.& ( \(Ur asVec) ->
                  castFresh @(Succ predN) fresh (VCons a asVec)
              )
    )

tryHead :: Vec n a -> Maybe a
tryHead VNil = Nothing
tryHead (VCons x _) = Just x

lazyVecFromListIsLazy :: Maybe Int
lazyVecFromListIsLazy = unur L.$ withFresh (lift tryHead L.. lazyVecFromList [0, undefined])

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
  * There is no multiplicity inference yet. In other words, even if a function from a library is linear, we need to redefine it to get a linear type for it.
  * As you can see above, the error messages don't say exactly where something is wrong. Just that some value was not used linearly.
  * Multiplicity polymorphism is not reliable yet.

We can recover the original type of `vecFromList` though:
-}

lazyVecFromList2 :: [a] -> SomeVec a
lazyVecFromList2 xs = unur L.$ withFresh (lift SomeVec L.. lazyVecFromList xs)

{- [markdown]
Now, the use of linear types in the implementation of `lazyVecFromList2` is completely hidden from the user and they don't have to deal with the difficulties surrounding linear types.

## Invisible type preservation with linear control functors

I discovered the trick above almost 2 years ago.
I put it on GitHub, but never mentioned it because I had not yet succeeded in my actual goal: to make a safe version of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.
The hard thing about this is that to enable it to change the types of the foci of the argument `Traversable`, we need to ensure that the lists in the focus of `partsOf` are of the same length, and at the same time, this length cannot be known by the caller.
In other words, a perfect use case for existential types where a rank-2-type or GADT-wrapper wouldn't work.
I thought I could use the trick with a linear `Fresh`, but when I tried it `partsOf :: Functor f => Traversing (->) f s t a b -> Fresh n %1 -> LensLike f (Ur s) (Ur t) (Vec n a) (Vec n b)`, the fact that the resulting optic must be used linearly, makes it just as unusable as the rank-2-type version.

To be clear, if you unfold the `LensLike f s t (Vec n a) (Vec n b)` to `(forall n. Vec n a -> f (Vec n b)) -> s -> f t` (i.e. use a rank-2-type), you can implement `partsOf` just fine, but this optic can't be used function like `traverseOf` or pre-composed with other optics with `.`.
For a long time, I banged my head against the wall trying to think of a way to make a type-changing `partsOf` that would be compatible with the rest of the `lens` package, but I've finally given up.
I think it's impossible.

However, we *can* solve the `.`-pre-composition issue with linear optics, which the rest if this section will demonstrate.

The first idea to make this work is that instead of having an existential type `n` for the length of the vector exposed in the type signature of `partsOf`, we hide it using a type called `WitnessIndexed`, so the focus type of the optic becomes `WitnessIndexed Vec a`.
The second idea is that a function that takes a value `Witness x`, with `x` universally quantified and no other sources of any `Witness` in scope, and which must produce some `Witness y` value, with `y` existentially quantified, can only return the original `Witness x` value. Thus we can infer `y ~ x`.
I don't have a formal proof of this either, but hopefully it will become clear when I show the implementation.

Let's start with a definition for `WitnessIndexed`.
We don't want it to be specific to vectors, or even types with kind `k -> Type -> Type`.
At least we also want to support types that take multiple non-index arguments.
For this I've devised the type family `ApplyList` which takes a type `f` with kind `k -> l`, a list of `k`'s and applies all `k`'s to `f`:
-}

type ApplyList :: forall k l m. (k -> l) -> [k] -> m
type family ApplyList f xs where
  ApplyList f '[] = f
  ApplyList f '[x] = f x -- not sure why this is needed, but it's required to compile
  ApplyList f (x : xs) = ApplyList (f x) xs

{- [markdown]
This permits the following definition of `WitnessIndexed`:
-}

data Witness x = Witness -- constructor would normally be hidden

data WitnessIndexed f xs where
  WitnessIndexed :: Witness y %1 -> ApplyList (f y) xs -> WitnessIndexed f xs -- Note the linear arrow for `Witness x`

{- [markdown]
Now we can make the functions meant in the second idea concrete. An example would be a function with type `forall x. Witness x -> Some g ys`.
Let's consider the ways a function can produce values of `WitnessIndexed g ys` (without unsafe functions).
Producing `WitnessIndexed` requires a `Witness` value, so we must consider the ways of obtaining this.
Since there are no other sources of `Witness` in scope, the only way to obtain a `Witness` value is from the argument of the function.
Because the `Witness y` in the produced `WitnessIndexed` must be the original `Witness x`, the `y` in `ApplyList (f y) xs` in the `WitnessIndexed` must be equal to `x`.

QED.

Now let's extend this slightly by allowing the function to take additional arguments, e.g. `forall x. Witness x -> ApplyList (f y) xs -> Some g ys`.
This adds a potential source of `Witness` values, since `f` is universally quantified.
To make it impossible for Witness values to be passed to the function through the additional argument, we must make it impossible for the given value to appear in the result anywhere else then in the first argument of `WitnessIndexed`.
This is relatively easy to achieve by making the arrow that takes `Witness x` linear, i.e. `forall x. Witness x -> ApplyList (f y) xs -> Some g ys`.

This only allow us to make `Setter` optics though, which is a bit disappointing.
We need to extend the "proof" further to allow functions that produce a functorial context of `WitnessIndexed`, like `forall x. Witness x -> ApplyList (f y) xs -> h (Some g ys)`.
This is tricky because `h` is universally quantified and could be chosen to be something like
-}

data ConstWitness a where
  ConstWitness :: Witness x %1 -> ConstWitness a

{- [markdown]
which would allow the Witness value to enter `forall x. Witness x -> ApplyList (f y) xs -> h (Some g ys)`-functions elsewhere.
To prevent this, we need to require `h (WitnessIndexed f x)` to contain at least one `WitnessIndexed f x` which requires the `Witness`.
Luckily, a solution for this already exists: linear control functors.
I'd never heard about them before this project and I only ran into them because I was confused which `Functor` module from `linear-base` I needed to import.
I'd recommend reading [Arnaud's blogpost](https://www.tweag.io/blog/2020-01-16-data-vs-control/) on them if you're unfamiliar, but I'll also briefly explain here.

In short, in the linear world, there are 2 types of functors: data functors and control functors.
The type of `Control.Functor.Linear.fmap` is `(a %1 -> b) %1 -> f a %1 -> f b`.
The key difference with data functors is that a control functors consumes it's argument function linearly (`%1` on the second arrow) while data functors don't.
Thus, only functors that contain their argument type exactly once can be control functors.
For example `State` and `IO` are control functors, while `[]` and `Const` aren't.

This gives us exactly what we need.
Let's finally write a function that makes use of all these properties:
-}

withWitness
  :: forall h f g xs ys a
   . (Linear.Control.Functor h, Functor h) -- For some reason, the normal non-linear Functor is not a superclass of Linear.Control.Functor.
  => (forall x. Witness x %1 -> ApplyList (f x) xs -> h (WitnessIndexed g ys))
  -> ApplyList (f a) xs
  -> h (ApplyList (g a) ys)
withWitness f x = f @a Witness x <&> \(WitnessIndexed Witness y) -> unsafeCoerce y

{- [markdown]
I think this `unsafeCoerce` is safe due to the limitations described above.
Just like with `castFresh`, f you can find a way to break it, please let me know!

Due to the type families, this function is hopelessly ambiguous (as in almost none of the type variables can be inferred from it's usage, thus required `AllowAmbiguousTypes`).
Let's make it a bit easier to use and demonstrate conversion between rank-2 based existentials:
-}

expose
  :: forall h f g xs ys x
   . (Linear.Control.Functor h, Functor h)
  => (WitnessIndexed f xs %1 -> h (WitnessIndexed g ys)) -> ApplyList (f x) xs -> h (ApplyList (g x) ys)
expose f = withWitness @_ @f @g @xs @ys @x $ \w x -> f (WitnessIndexed w x)

hide
  :: forall h f g xs ys
   . (Linear.Control.Functor h, Functor h) -- This use of Linear.Control.Functor is actually independent from the one guaranteeing safety in `withWitness`. This function uses it to actually move the received Witness into h.
  => (forall x. ApplyList (f x) xs -> h (ApplyList (g x) ys))
  -> WitnessIndexed f xs
  %1 -> h (WitnessIndexed g ys)
hide f (WitnessIndexed @x w x) = Linear.Control.fmap (\(Ur y) -> WitnessIndexed w y) L.$ Ur <$> f @x x

{- [markdown]
The function `expose` exposes the existential type hidden in `WitnessIndexed`, while `hide` hides a type in `WitnessIndexed`.
Now we can move on to the optics bit.

Instead of the `BazaarT` based implementation that's used in `lens`' `partsOf`, I will use the `Batching` functor from ['batching`](https://hackage.haskell.org/package/batching-0.1.0.0).
This is mostly out of convenience.
I don't know what half of the function names used in the implementation of `partsOf` in `lens` mean, and `Batching` gives me the vector-based transformation that I need.
-}

batching
  :: (Functor f)
  => Lens.LensLike (Batching a b) s t a b
  -> (forall n. V.Vec n a -> f (V.Vec n b))
  -> s
  -> f t
batching o f = runBatching (fmap V.rev . f . V.rev) . Lens.traverseOf o request -- The Vec from `runBatching` is reversed for some reason.

type PreservingLensLike h s t f xs g ys =
  (Linear.Control.Functor h, Functor h) => Lens.Over (FUN One) h s t (WitnessIndexed f xs) (WitnessIndexed g ys) -- = (WitnessIndexed f xs %1 -> h (WitnessIndexed g ys)) -> s -> h t

partsOf
  :: (Linear.Control.Functor f, Functor f)
  => Lens.LensLike (Batching a b) s t a b -> PreservingLensLike f s t V.Vec '[a] V.Vec '[b]
partsOf o f = batching o $ expose f

pTraverseOf
  :: forall xs ys h f g s t
   . (Applicative h, Linear.Control.Functor h)
  => (forall m. (Applicative m) => PreservingLensLike m s t f xs g ys)
  -> (forall x. ApplyList (f x) xs -> h (ApplyList (g x) ys))
  -> s
  -> h t
pTraverseOf o f = o $ hide $ \ @n -> f @n -- This is syntax from the TypeAbstractions extension

-- This replaces all the `Char`s in a `[Either Char String]` with a `String` consisting of all the `Char`s in the list.
demo1 :: [Either Bool String]
demo1 =
  runIdentity $
    pTraverseOf
      (partsOf (Lens.traversed . Lens._Right))
      (\chars -> Identity $ fmap (const $ foldMap (: []) chars) chars)
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo
-- This causes a segfault in HLS and GHCi. Will create an issue later.

-- main = print demo
-- prints [Left True,Right "hi",Left False,Right "hi"]

{- [markdown]
I'll admit, the demo is not the most useful application, but the point is that this shows how `partsOf` allows one to work over each element of a traversal with the context of all visited elements.
And I lied.
The type-changing `partsOf` was not my actual goal.
I need it for something I plan to write an article about later™.
(Spoiler: it's more fancy optics).

Something else worth noting about the code block above is that we can actually define `PreservingLensLike` using an existing type from `lens`.
Some optic combinators already abstract over the profunctor in the optics transformation, so some combinators like [`taking`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:taking) and [`failing`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:failing) should also work with "preserving" optics.

Speaking of standard optics, wouldn't it be nice if we could use them on `WitnessIndexed` and compose them with preserving optics?
-}

hidden
  :: forall f s t xs ys a b
   . (Linear.Control.Functor f, Functor f)
  => (forall x. (a -> f b) -> ApplyList (s x) xs -> f (ApplyList (t x) ys))
  -> (a -> f b)
  -> WitnessIndexed s xs
  %1 -> f (WitnessIndexed t ys)
hidden o f = hide $ \ @n -> o @n f

demo2 :: [Either Bool Char]
demo2 =
  runIdentity $
    Lens.traverseOf
      (partsOf (Lens.traversed . Lens._Right) . hidden (Lens.ix (unsafeFin @Int 1))) -- Can't use normal `fin` because `runBatching` does not provide `KnownNat n`
      (Identity . toUpper)
      [Left True, Right 'h', Left False, Right 'i']

-- main = print demo2
-- prints [Left True,Right 'h',Left False,Right 'I']

{- [markdown]

<details>
<summary>Required orphans</summary>

-}

type instance Lens.Index (V.Vec n a) = Fin n
type instance Lens.IxValue (V.Vec n a) = a

instance Lens.Ixed (V.Vec n a) where
  ix i f v = f (v V.! i) <&> \b -> V.overIx i (const b) v

{- [markdown]
</details>

As shown we can run standard optics like `Lens.ix` on `WitnessIndexed` foci using the `hidden` combinator.
Furthermore, we could compose `hidden` with other standard optics (like `hidden (...) . standardOptic`) because the arrow in `(a -> f b)` in `preserving`'s type is not linear nor does it contain a `forall`.

Finally, I'd also like to show how to define `Getter`s for preserving optics, because such a thing was not possible with some of my failed ideas for preserving optics.
-}

data Some f xs where
  Some :: forall x f xs. ApplyList (f x) xs -> Some f xs

type PreservingLensLike' h s f xs = PreservingLensLike h s s f xs f xs

type PreservingGetter r s f xs = PreservingLensLike' ((,) r) s f xs

pView :: PreservingGetter (Some f xs) s f xs -> s -> Some f xs
pView o s = fst $ o (hide (\ @x x -> (Some @x x, x))) s

{- [markdown]
## Conclusion

library

-}

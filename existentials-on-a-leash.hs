{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{- [markdown]
# Existentials on a leash

In this article, I will first share a trick to enable more flexible use of "existentially quantified" type variables in Haskell, which allows them to appear "naked" (without CPS-style/GADT wrapping) in a type signature.
Second, the article demonstrates a method for defining optics over types containing existentially quantified variables (though without having them appear naked in the type signature).

Both these techniques rely on witness-values passed linearly through some function.
I believe the linear use of these witnesses makes the use of unsafe functions in these techniques safe, though I have not proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs, linear types and optics (for the sections pertaining to them) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a GitHub Codespace prebuild (EU/NA?) (todo) and GitPod (other continents).
Clicking either of these links will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser.

## Current limitations of existential types

As of GHC 9.12, GHC only supports 2 ways of "existentially quantifying" type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This corresponds to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

Both these techniques do not actually use existential quantification, but instead encode it through negated universal quantification.
Wrapping and unwrapping existential types using these techniques is not just cumbersome, but they're also insufficient for defining optics with existentially quantified foci, such as prisms for constructors of GADTs with existentially quantified fields.

[A proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding first-class existential types to GHC was written a while ago, but the author seems to be prioritizing other work.
The proposal also shows a simpler example of a function that is impossible to write using the current workarounds: a function that converts a list to a vector lazily, i.e. one where `head $ vecFromList (1 : undefined)` produces `Just 1`.

This article introduces 2 new workarounds (it turns out the first one I came up with didn't work so well for defining optics with existentially quantified types).

But first, the language extensions and imports used in this article.
The main thing to remember is that we use `L` and `NL` to disambiguate linear and non-linear functions, respectively, where needed.

<details>
<summary>Imports and language extensions</summary>

-}
{-# OPTIONS_GHC -Wall -Wno-missing-signatures -Wno-unused-top-binds -Wno-orphans #-}

{- cabal:
ghc-options: -Wall
default-language: GHC2024
build-depends:
  base,
  linear-base,
  lens,
  mtl,
  profunctors,
-}
{- project:
with-compiler: ghc-9.12.2

semaphore: True
-}

import Control.Functor.Linear qualified as Linear.Control
import Control.Lens qualified as Lens
import Control.Lens.Internal.Bazaar qualified as Lens
import Control.Lens.Internal.Context qualified as Lens
import Control.Monad.State.Lazy qualified as NL
import Data.Bifunctor.Linear
import Data.Char
import Data.Functor ((<&>))
import Data.Functor.Identity
import Data.Functor.Linear qualified as L
import Data.Kind
import Data.List as NL
import Data.Maybe
import Data.Profunctor.Rep qualified as Lens
import Data.Type.Equality
import Data.Unrestricted.Linear
import GHC.Base (Multiplicity (..), TYPE)
import Prelude.Linear hiding (fst, ($), (.))
import Prelude.Linear qualified as L (($))
import Unsafe.Coerce (unsafeCoerce)
import Prelude as NL (Applicative (..), Functor (..), fst, ($), (<$>))

-- Multiplicity polymorphic version of . which works in most non-linear code as well.
(.) :: forall {rep} b (c :: TYPE rep) a m n. (b %m -> c) %n -> (a %m -> b) %m -> a %m -> c
(.) f g x = f (g x)
infixr 9 .

{- [markdown]
</details>

Length-indexed vectors as defined in the existential types proposal:

-}

data Nat = Zero | Succ Nat

type Vec :: Nat -> Type -> Type
data Vec n a where
  VNil :: Vec Zero a
  VCons :: a %1 -> Vec n a %1 -> Vec (Succ n) a

{- [markdown]
Suppose we want to define a function to convert a normal list to a length-indexed vector.
Because we don't know the length of the list at the type level, we would like this function to have the type: `fromList :: exists n. [a] -> Vec n a`.
Since GHC does not yet support existential types, we will have to use either CPS, yielding `fromList :: [a] -> (forall n. Vec n a -> r) -> r`, or a GADT wrapper type, yielding `fromList :: [a] -> SomeVec a`.
Let's work out the second option.
-}

data SomeVec a where
  SomeVec :: forall n a. Vec n a %1 -> SomeVec a

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

\*So we have to work around it.*

## Putting existentials on a leash

Essentially, we *have* to make the length of the vector visible in the return type of `vecFromList`.
GHC only offers universal quantification for such a type variable, but somehow, we need to make it impossible for the caller of `vecFromList` to choose a specific type for this variable, so `vecFromList` can make this choice.
To accomplish this, we start with a proxy type `Fresh` which can only be introduced with an existential type as parameter.

-}
data Fresh0 a = Fresh0

unpack0 :: (forall a. Fresh0 a -> r) -> r
unpack0 f = f Fresh0

{- [markdown]

This proxy will serve as a proof-witness that the associated type variable was existentially quantified elsewhere in the program.
The type of `vecFromList` becomes `forall n a. [a] -> Fresh n -> Vec n a` and the burden of the existential quantification is pushed outward to the caller.
This effectively enlarges the scope of the existential type to wherever the caller (or even its caller) decides to introduce the existential type using `unpack`.
By passing the existential quantification witness as an argument to where it is eventually used, we create the leash from which this technique and article get their name.

Now, we need a way for `vecFromList` to choose a type for `n`.
Since it is a concrete type (instantiated at the call site), our only option is `unsafeCoerce`.

Putting the dangers of this approach aside for a moment, given a value of `Fresh n`, we should allow `n` to be coerced to some other type `b`, but in `vecFromList` we don't have values of type `n`, only `Vec n a`.
We could define `packVec :: Vec n a -> Fresh n' -> Vec n' a`, but ideally such a function would not be specific to the example of length-indexed vectors.
This can be accomplished by providing a type equality witness (from `Data.Type.Equality`) instead of a specific casting function.

We arrive at:
-}
newtype Fresh1 a = Fresh1 (forall b. a :~: b)

unpack1 :: (forall a. Fresh1 a -> r) -> r
unpack1 f = f (Fresh1 $ unsafeCoerce Refl)

{- [markdown]

Using `Data.Type.Equality.castWith`, we can now perform unsafe coercions for any instance of `a` for which we have a `Fresh a`!
Now, we only need to remove the word "unsafe" from that sentence.

--todo
I believe it's sufficient to ensure that the existential quantification witness is used at most once.
Until we use the witness, no values of type `a` can exist because it was existentially quantified.
Values of a types `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
As long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

The first steps to this are to require that a `Fresh a` is used linearly in the continuation passed to `unpack` and hiding the constructor `Fresh`, like so:
-}

newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

-- todo: should have forall
type Exists a b = Fresh a %1 -> b

unpack2 :: (forall a. Exists a r) %1 -> r
unpack2 f = f L.$ Fresh $ unsafeCoerce Refl

pack :: forall b r a. (a ~ b => r) %1 -> Exists a r
pack r (Fresh (Refl :: a :~: b)) = r

{- [markdown]
The function `pack` is needed to replace `Data.Type.Equality.castWith` since the user can't get the `a :~: b` from pattern matching on `Fresh` anymore.

However, this is not sufficient to guarantee only one `a ~ b` equality.
Even with the linear arrow in `unpack`, the existential quantification witness can be used differently in different branches of the program.
The following example shows how this can be used to generate incorrect type equalities.
-}

data GADT a where
  Int :: GADT Int
  Char :: GADT Char

data Wrapper where
  Wrapper :: forall a. (Bool -> GADT a) %1 -> Wrapper

wrapper :: Wrapper
wrapper =
  unpack2
    ( \(fresh :: Fresh a) ->
        Wrapper @a
          (\b -> if b then pack @Int Int fresh else pack @Char Char fresh)
    )

{- [markdown]

```haskell
conflict :: Int :~: Char
conflict =
  wrapper & \(Wrapper @a (f :: Bool -> GADT a)) ->
    let
      int = f True :: GADT a
      char = f False :: GADT a
    in
      trans @Int @a @Char -- trans :: (a :~: b) -> (b :~: c) -> a :~: c
        ( case int of
            Int -> Refl :: Int :~: a
        )
        ( case char of
            Char -> Refl :: a :~: Char
        )
```

todo: `Fresh`-value
In essence, the `Fresh` escapes its linear scope through `Wrapper`.
Because `Wrapper` does not need to be consumed linearly outside with `unpack` call, we can use the embedded function (and thus the captured `Fresh` inside) twice.
I think the trick to prevent this is pretty neat: we can't ensure the result `r` of `unpack` is consumed linearly, so we must put a constraint on `r` that ensures it can not be used to duplicate a `Fresh`.
Counterintuitively, we must require that `r` *can* be duplicated, i.e. it's an instance of [`Dupable`](https://hackage-content.haskell.org/package/linear-base-0.7.0/docs/Data-Unrestricted-Linear.html#t:Dupable).

To understand why, we must realize 2 things:
1. A `Fresh` can only be captured by a linear field (like `(Bool -> GADT a)` in `Wrapper`). Otherwise the `Fresh`-value would not be consumed linearly.
2. A type that is `Dupable` can only contain a linear field when values in that field can be duplicated, but a function can not (even if it's input is `Bounded`, because the function must be consumed linearly and finding the different outputs requires applying it multiple times).

Therefore it is safe to duplicate a `Dupable` value after it's produced by `unpack`.
In other words, we prevent unsafe duplication of `Fresh` by requiring that all values that leave `Fresh` can be duplicated.

Thus we finally arrive at the final (and as far as I understand, safe) version of `unpack`:
-}

unpack :: Dupable r => (forall a. Exists a r) %1 -> r
unpack f = f L.$ Fresh $ unsafeCoerce Refl

{- [markdown]
Now we can also define a lazy version of `vecFromList`
-}

infix 3 `SuchThat`
data SuchThat a c where
  SuchThat :: c => a %1 -> SuchThat a c

-- Explicit projection function because multiplicity-parametric record projections are not yet implemented
unSuchThat :: SuchThat a c %1 -> a
unSuchThat (SuchThat a) = a

lazyVecFromList :: [a] -> Exists n (Vec n (Ur a))
lazyVecFromList [] n = pack @Zero VNil n
lazyVecFromList (a : as) n =
  unpack
    ( \ @predN freshPredN ->
        -- TypeAbstractions syntax
        pack @(Succ predN) (VCons (Ur a) L.$ lazyVecFromList as freshPredN) n
    )

-- bonus example using SuchThat
vecNonEmpty :: forall n m a. Vec n a %1 -> Exists m (Maybe (Vec (Succ m) a `SuchThat` n ~ Succ m))
vecNonEmpty VNil = flip lseq Nothing
vecNonEmpty (VCons @_ @o x xs) = pack @o (Just L.$ SuchThat (VCons x xs))

vecUncons :: Vec (Succ n) a %1 -> (a, Vec n a)
vecUncons (VCons a as) = (a, as)

lazyVecFromListIsLazy :: Maybe Int
lazyVecFromListIsLazy =
  unpack
    ( \n ->
        unpack
          ( L.fmap (second SomeVec . vecUncons . unSuchThat)
              . vecNonEmpty (lazyVecFromList (0 : error "second element evaluated") n)
          )
    )
    <&> (\(Ur a, _) -> a)

-- >>> lazyVecFromListIsLazy
-- This causes a segfault in HLS and GHCi. Will create an issue later.

-- main = print lazyVecFromListIsLazy
-- prints "Just 0"

{- [markdown]

<details>
<summary>Required Consumable/Dupable instances</summary>

Nothing special going on here. They just have to be written out manually because `Vec` and `SomeVec` are a GADTs.
-}

instance Consumable a => Consumable (Vec n a) where
  consume VNil = ()
  consume (VCons x xs) = lseq x L.$ consume xs

instance Dupable a => Dupable (Vec n a) where
  dupR VNil = L.pure VNil
  dupR (VCons x xs) = VCons L.<$> dupR x L.<*> dupR xs

instance Consumable a => Consumable (SomeVec a) where
  consume (SomeVec v) = consume v

instance Dupable a => Dupable (SomeVec a) where
  dupR (SomeVec v) = SomeVec L.<$> dupR v

instance L.Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons x xs) = VCons (f x) L.$ L.fmap f xs

instance Consumable (Fresh a) where
  consume (Fresh Refl) = ()

{- [markdown]
</details>

The recursive case has become a little more complicated: we need an extra existential type to pass to the recursive application of `lazyVecFromList`.
We can't use the one we got as an argument, because the recursive call should produce a vector of type `Vec predN a` instead of `Vec n a`.

The test `lazyVecFromListIsLazy` shows that that `lazyVecFromList` is lazy (shocker, I know) by getting the head

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
lazyVecFromList2 xs =
  unpack (SomeVec . lazyVecFromList xs)
    & \(SomeVec vec) -> SomeVec $ L.fmap unur vec

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
Just like with `pack`, f you can find a way to break it, please let me know!

Due to the type families, this function is hopelessly ambiguous (as in almost none of the type variables can be inferred from it's usage, thus required `AllowAmbiguousTypes`).
Let's make it a bit easier to use and demonstrate conversion between rank-2 based existentials:
-}

expose
  :: forall x h f g xs ys
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
-}

vecToList :: Vec n a -> [a]
vecToList VNil = []
vecToList (VCons a as) = a : vecToList as

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a as) = VCons (f a) (fmap f as)

type PreservingLensLike h s t f xs g ys =
  (Linear.Control.Functor h, Functor h) => Lens.Over (FUN One) h s t (WitnessIndexed f xs) (WitnessIndexed g ys) -- = (WitnessIndexed f xs %1 -> h (WitnessIndexed g ys)) -> s -> h t

partsOf
  :: (Linear.Control.Functor f, Functor f)
  => Lens.Traversing (->) f s t a b -> PreservingLensLike f s t Vec '[a] Vec '[b]
partsOf o f s =
  lazyVecFromList2 (ins b)
    & \(SomeVec @n v) ->
      unsafeOuts b . vecToList <$> expose @n f v
 where
  b = o Lens.sell s
  ins = Lens.toListOf (Lens.getting Lens.bazaar)
  unsafeOuts = NL.evalState `Lens.rmap` Lens.bazaar (Lens.cotabulate (\_ -> NL.state (fromJust . NL.uncons)))

pTraverseOf
  :: forall xs ys h f g s t
   . (Applicative h, Linear.Control.Functor h)
  => (forall m. Applicative m => PreservingLensLike m s t f xs g ys)
  -> (forall x. ApplyList (f x) xs -> h (ApplyList (g x) ys))
  -> s
  -> h t
pTraverseOf o f = o $ hide $ \ @n -> f @n

-- This replaces all the `Char`s in a `[Either Char String]` with a `String` consisting of all the `Char`s in the list.
demo1 :: [Either Bool String]
demo1 =
  runIdentity $
    pTraverseOf
      (partsOf (Lens.traversed . Lens._Right))
      (\chars -> Identity $ fmap (const $ vecToList chars) chars)
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo
-- This causes a segfault in HLS and GHCi. Will create an issue later.

-- main = print demo1
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
      (partsOf (Lens.traversed . Lens._Right) . hidden (Lens.ix 1)) -- Can't use normal `fin` because `runBatching` does not provide `KnownNat n`
      (Identity . toUpper)
      [Left True, Right 'h', Left False, Right 'i']

-- main = print demo2
-- prints [Left True,Right 'h',Left False,Right 'I']

{- [markdown]

<details>
<summary>Required orphans</summary>

-}

type instance Lens.Index (Vec n a) = Int
type instance Lens.IxValue (Vec n a) = a

instance Lens.Ixed (Vec n a) where
  ix 0 f (VCons a as) = flip VCons as <$> f a
  ix i f (VCons a as) = VCons a <$> Lens.ix i f as
  ix _ _ VNil = pure VNil

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
pView o s = NL.fst $ o (hide (\ @x x -> (Some @x x, x))) s

{- [markdown]
## Conclusion

library

-}

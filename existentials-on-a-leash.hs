{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{- [markdown]
# Existentials on a leash

In this article, I will share 2 new workarounds for (the lack of) existentially quantified type variables in Haskell
The first workaround allows them to appear "naked" (without CPS-style/GADT wrapping) in a type signature, while the second allows for defining optics over types containing existentially quantified variables (though without having them appear naked in the type signature).

Both these techniques rely on witness-values passed linearly through some function.
I believe the linear use of these witnesses makes the use of unsafe functions in these techniques safe, though I have not proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs, linear types and optics (for the sections pertaining to them) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a GitHub Codespace prebuild (EU/NA?) (todo) and GitPod (other continents).
Clicking either of these links will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser.
It might even be a nice way to read the article because you can hover over values to see their types for example.

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
  kind-apply,
-}
{- project:
with-compiler: ghc-9.12.2

index-state: 2026-03-18T08:38:52Z

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
import Data.PolyKinded hiding (Nat)
import Data.Profunctor.Rep qualified as Lens
import Data.Type.Equality
import Data.Unrestricted.Linear
import GHC.Base (Multiplicity (..), TYPE)
import Prelude.Linear hiding (fst, ($), (.))
import Prelude.Linear qualified as L
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

Putting the dangers of this approach aside for a moment, given a value of type `Fresh n`, we should allow `n` to be coerced to some other type `b`, but in `vecFromList` we don't have values of type `n`, only `Vec n a`.
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

I believe it's sufficient to ensure such a coercion always targets the same type for each `Fresh`-value.
Until we use the witness, no values of type `a` can exist because it was existentially quantified.
Values of a types `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
So as long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

The first steps to this are to hide the constructor `Fresh` and to require that a `Fresh`-value is used linearly in the continuation passed to `unpack`, like so:
-}

newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

type Exists a b = Fresh a %1 -> b -- conceptually this should be `forall a. Fresh a %1 -> b`, but that prevents `a` from being used in `b` and defeats the entire point.

unpack2 :: (forall a. Exists a r) %1 -> r
unpack2 f = f L.$ Fresh $ unsafeCoerce Refl

pack :: forall b r a. (a ~ b => r) %1 -> Exists a r
pack r (Fresh (Refl :: a :~: b)) = r

{- [markdown]
The function `pack` is needed to replace `Data.Type.Equality.castWith` since the user can't get the `a :~: b` from pattern matching on a `Fresh`-value anymore.

However, this is not sufficient to ensure a `pack`-coercion always targets the same type for each `Fresh`-value.
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

In essence, the `Fresh`-value escapes its linear scope through `Wrapper`.
Because `Wrapper` does not need to be consumed linearly outside with `unpack` call, we can use the embedded function (and thus the captured `Fresh`-value inside) twice.
I think the trick to prevent this is pretty neat: we must require that `r` produced by `unpack` *can* be linearly duplicated, i.e. it's an instance of [`Dupable`](https://hackage-content.haskell.org/package/linear-base-0.7.0/docs/Data-Unrestricted-Linear.html#t:Dupable).

To understand why, we must realize 3 things:
1. A `Fresh`-value can only be captured by a *linear* field (like `(Bool -> GADT a)` in `Wrapper`). Otherwise the `Fresh`-value would not be consumed linearly.
2. A type that is `Dupable` can only contain a linear field when that field is also `Dupable`, but a function is not (even if it's input is `Bounded`, because the function must be consumed linearly and finding the different outputs requires applying it multiple times).
3. `Fresh` is not `Dupable`, because of 1. and 2. it can not occur in a `Dupable` value.

Therefore it is safe to duplicate a `Dupable` value after it's produced by `unpack` and we arrive at the final version of `unpack`:
-}

unpack :: Dupable r => (forall a. Exists a r) %1 -> r
unpack f = f L.$ Fresh $ unsafeCoerce Refl

{- [markdown]
So is this completely safe now?
Well, only if `Dupable r` is a faithful instance of `Dupable`.
If you implement `dup` as `error "this is never used anyway"` for a linearly captured function, you could still write the `conflict` expression from before and you'd get away with it.
We could have `unpack` call `dup` to verify this does not happen, but that would make it so strict that it becomes useless for implementing a lazy `vecFromList`.

Alternatively, we could define a closed type family `ClosedDupable` which uses [`RepK`](todo) from `kind-generics` to see if the representation of a type contains a linear function field (if you don't know `kind-generics`, it extends the language of `GHC.Generics` such that GADTs can also get a generic representation).
The drawback here is that this requires users to derive `RepK` using template haskell or define it manually, and I don't think that's worth the extra safety.

Another alternative I'v considered is to use the property of `Fresh`-values that the `a` in `Fresh a` is always existential.
We can prevent a GADT occurring in `r` from capturing it by using a similar type family to inspect the generic representation as mentioned above.
This might be good solution for when you do need to have a function as a linear field in `r`, but generally I think it's a more severe restriction that `Dupable`.

In summary, I believe `unpack` is only unsafe when used in combination with other unsafe functions (in the implementation of `Dupable`).
To me, that's acceptable.
There are some safer alternatives, but they require more effort from the user and don't justify the cost.

Now lets continue and finally define a lazy `vecFromList`:
-}

lazyVecFromList0 :: [a] -> Exists n (Vec n (Ur a))
lazyVecFromList0 [] n = pack @Zero VNil n
lazyVecFromList0 (a : as) n =
  -- This `unpack` actually unpacks the `Vec` produced by the recursive call, not the one `pack`ed immediately below
  unpack
    -- TypeAbstractions syntax
    ( \ @predN predN ->
        pack @(Succ predN) (VCons (Ur a) L.$ lazyVecFromList0 as predN) n
    )

{- [markdown]
The manual `pack`ing and `unpack`ing makes the definition significantly more verbose, but I believe they are all necessary.
The `pack`s are needed because neither `VNil` nor `VCons` produce vectors of arbitrary length, and we can't remove the `unpack` because we can't use the same `Fresh`-value for coercing the `VCons`

However, as you'll see in the next code block, we can abstract some of the verbosity away.

We should also test that this definition is actually lazy.
This is actually much more work than I hoped because the produced vector actually also has to be consumed linearly (until it escapes the `unpack` that provides the initial `Fresh`-value that's used).
That's because linear arrows don't just require that the argument is consumed exactly once.
They actually say that if the caller evaluates the produced value to normal form, then the function will evaluate the argument to normal form exactly once.
So a function that takes a `Fresh`-value in `unpack` and passed it to `lazyVecFromList0` must also treat the produced vector linearly (i.e. use it for the function's result in some way).

You might also have noticed that the produced vector has elements of type `Ur a` instead of just `a`.
For those unfamiliar with `linear-base`, `Ur` is a very simple type (`data Ur a = Ur a`), which is non-linear in the captured `a`-value.
This allows linear functions to produce values of which some parts are unrestricted (hence the name `Ur`).

It would be much nicer if we could have `lazyVecFromList0 :: [a] -> Exists n (Ur (Vec n a))`.
That's no problem for the `[]`-case, but it would mean that we have to pattern match on `Ur` in the recursive case, which in turn means the function always evaluates until the final `Ur` produced in the `[]`-case, which would make the function strict in the length of the list.

Now that's all cleared up, here is the small `pack`/`unpack` abstraction I promised:
-}

repack :: forall f n a. Dupable a => (forall m. n ~ f m => Exists m a) -> Exists n a
repack f n = unpack (\ @m m -> pack @(f m) (f m) n)

lazyVecFromList1 :: [a] -> Exists n (Vec n (Ur a))
lazyVecFromList1 [] = pack @Zero VNil
lazyVecFromList1 (a : as) = repack (VCons (Ur a) . lazyVecFromList1 as)

{- [markdown]
I'm actually quite surprised the recursive case does not need any type arguments despite `f` only occurring in a constraint.

Now for the laziness test:
-}

infix 3 `SuchThat`
data SuchThat a c where
  SuchThat :: c => a %1 -> SuchThat a c

-- Explicit projection function because multiplicity-parametric record projections are not yet implemented
unSuchThat :: SuchThat a c %1 -> a
unSuchThat (SuchThat a) = a

-- bonus example example of a function producing an existential value, which also demonstrates the use of `SuchThat`
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
              . vecNonEmpty (lazyVecFromList1 (0 : error "second element evaluated") n)
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

And thus we prove the laziness of `lazyVecFromList1`.
[But what did it cost?](https://preview.redd.it/what-did-it-cost-everything-v0-6iqdlya6n9161.png?width=1080&crop=smart&auto=webp&s=05f747638b1524811324eb29c0c6435404930287)
  * As explained before, we must consume the vector produced by `lazyVecFromList1` linearly, which means we can't simply pattern match and discard the tail (because the tail of `Vec` is a linear field). We also can't use [`consume`](https://hackage-content.haskell.org/package/linear-base-0.7.0/docs/Data-Unrestricted-Linear.html#v:consume) because it is strict for vectors, so it would evaluate the `error "second element evaluated"`. Instead we must transform the first `VCons` to a data structure of which the fields are linear when used in a linear context, but unrestricted when used in an unrestricted context. This magical data structure is a tuple, and we get it from `vecUncons`.
  * To use `vecUncons`, we need a vector that contains at least one element, which we get from `vecNonEmpty`. That also introduces a `SuchThat` which we simply discard (I could have left it out of the definition of `vecNonEmpty` to simplify a little bit, but it felt wrong not to include it and would be a waste of an opportunity to demonstrate it.)
  * Additionally, we need to fall back to the GADT-wrapper workaround for existential types (i.e. `SomeVec`) to let the tail of the vector escape the `unpack`.
  * Generally, the 2 `unpacks` make the whole thing pretty verbose.

And I haven't even mentioned the general inconveniences of working with linear types:
  * There is no multiplicity inference yet. This means that most existing Haskell code is unusable, even if the implementation of a function is actually linear.
  * The error messages don't say where a value is not used linearly, only which variable.
  * All the other limitations mentioned in the [docs](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html#limitations).

So while this linear-existentiality-witness-techinique allows some things that are not possible with the existing existential-type-workarounds, I can't recommend using it outside of cases that are very limited in scope like `lazyVecFromList1`.

Luckily, we can define a `lazyVecFromList` that hides all of the linear-types complexity and falls back to GADT-wrapper workaround:
-}

lazyVecFromList2 :: [a] -> SomeVec a
lazyVecFromList2 xs =
  unpack (SomeVec . lazyVecFromList1 xs)
    & \(SomeVec vec) -> SomeVec $ L.fmap unur vec

{- [markdown]

## Invisible type preservation with linear control functors

*I discovered the trick above almost 2 years ago.*

I put it on GitHub, but never mentioned it because I had not yet succeeded in my actual goal: to make a safe version of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.
The hard thing about this is that to enable it to change the types of the foci of the argument `Traversable`, we need to ensure that the lists in the focus of `partsOf` are of the same length, and at the same time, this length cannot be known by the caller.
In other words, a perfect use case for existential types where a rank-2-type or GADT-wrapper wouldn't work.
I thought I could use the trick with a linear `Fresh`, but when I tried it `partsOf :: Functor f => Traversing (->) f s t a b -> Fresh n %1 -> LensLike f s t (Vec n (Ur a)) (Vec n (Ur b))`, the fact that the resulting optic must be used linearly, makes it just as unusable as the rank-2-type version.

To be clear, if you unfold the `LensLike f s t (Vec n a) (Vec n b)` to `(forall n. Vec n a -> f (Vec n b)) -> s -> f t` (i.e. use a rank-2-type), you can implement `partsOf` just fine, but this optic can't be used function like `traverseOf` or pre-composed with other optics with `.`.
For a long time, I banged my head against the wall trying to think of a way to make a type-changing `partsOf` that would be compatible with the rest of the `lens` package, and so the project stayed on my list of things to get back to at some point.
It's somewhat regrettable that I didn't just publish the first part of this article anyway, but on the other hand I found quite a few serious mistakes when I came back to it, so I'm also happy I caught those before publishing.

I now think making a safe type-changing `partsOf` that is compatible with all the functions from `lens` is impossible, but I did find a way to solve the `.`-pre-composition issue, again using linear functions
The rest of this section is dedicated to this technique.

The first idea to make this work is that instead of having an existential type `n` for the length of the vector exposed in the type signature of `partsOf`, we hide it using a type called `ExistentiallyIndexed`, so the focus type of the optic becomes something like `ExistentiallyIndexed Vec a`.
The second idea is that a function that takes a value `Witness x`, with `x` universally quantified and no other sources of any `Witness` in scope, and which must produce some `Witness y` value, with `y` existentially quantified, can only return the original `Witness x` value. Thus we can infer `y ~ x`.
I don't have a formal proof of this either, but hopefully it will become clear when I show the implementation.

Let's start with a definition for `ExistentiallyIndexed`.
We don't want it to be specific to vectors, or even types with kind `k -> Type -> Type`.
We will use the kind-heterogeneous type-level lists from `kind-apply`, named [`LoT`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t:LoT) and the operator [`:@@:`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t::-64--64-:) which applies a type level list to a type constructor.
This permits the following definition of `ExistentiallyIndexed`:
-}

data Witness x = Witness -- constructor would normally be hidden

data ExistentiallyIndexed f xs where
  ExistentiallyIndexed :: Witness y %1 -> f y :@@: xs -> ExistentiallyIndexed f xs -- Note the linear arrow for `Witness x`

{- [markdown]
Now we can make the functions meant in the second idea concrete. An example would be a function with type `forall x y. Witness x -> Exists y (Witness y)`.
Let's consider the ways a function can produce values of `Exists y (Witness y)` (without unsafe functions).
Since there are no other sources of `Witness` in scope, the only way to obtain a `Witness` value is from the argument of the function.
Hence we have `x ~ y`.

QED.

Now let's extend this slightly by allowing the function to take and produce additional values, e.g. `forall x f g xs ys. Witness x -> f x :@@: xs -> ExistentiallyIndexed g ys`.
This adds a potential source of `Witness` values, since `f` is universally quantified.
To make it impossible for Witness values to be passed to the function through the additional argument, we must make it impossible for the given value to appear in the result anywhere else then in the first field of `ExistentiallyIndexed`.
This is relatively easy to achieve by making the arrow that takes `Witness x` linear, i.e. `forall x f g xs ys. Witness x %1 -> f x :@@: xs -> ExistentiallyIndexed g ys`.

This only allow us to make `Setter` optics though, which is a bit disappointing.
We need to extend the "proof" further to allow functions that produce a functorial context of `ExistentiallyIndexed`, like `forall x f g h xs ys. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys)`.
This is tricky because `h` is also universally quantified and could be chosen to be something like
-}

data ConstWitness a where
  ConstWitness :: Witness x %1 -> ConstWitness a

{- [markdown]
which would allow the Witness value to enter `Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys)`-functions elsewhere, e.g. through `f x :@@: xs`.
To prevent this, we need to require `h (ExistentiallyIndexed f x)` to contain at least one `ExistentiallyIndexed f x` which requires the `Witness`.
Luckily, a solution for this already exists: linear control functors.
I'd never heard about them before this project and I only ran into them because I was confused which `Functor` module from `linear-base` I needed to import.
I'd recommend reading [Arnaud's blogpost](https://www.tweag.io/blog/2020-01-16-data-vs-control/) on them if you're unfamiliar, but I'll also briefly explain here.

In short, in the linear world, there are 2 types of functors: data functors and control functors.
The type of `Control.Functor.Linear.fmap` is `(a %1 -> b) %1 -> f a %1 -> f b`.
The key difference with data functors is that a control functor consumes it's argument function linearly (`%1` on the second arrow) while data functors don't.
Thus, only functors that contain their argument type exactly once can be control functors.
For example `State` and `IO` are control functors, while `[]` and `Const` aren't.

This gives us exactly what we need.
Let's finally write a function that makes use of all these properties:
-}

withWitness
  :: forall h f g xs ys a
   . (Linear.Control.Functor h, Functor h) -- For some reason, the normal non-linear Functor is not a superclass of Linear.Control.Functor, so we need to add both.
  => (forall x. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys))
  -> f a :@@: xs
  -> h (g a :@@: ys)
withWitness f x = f @a Witness x <&> \(ExistentiallyIndexed Witness y) -> unsafeCoerce y

{- [markdown]
I think this `unsafeCoerce` is safe due to the restrictions described above.
Just like with `unpack`, if you can find a way to break it, please let me know!

Due to the type families, this function is hopelessly ambiguous (as in almost none of the type variables can be inferred from it's usage).
Let's make it a bit easier to use and demonstrate conversion between rank-2 based existentials:
-}

expose
  :: forall x h f g xs ys
   . (Linear.Control.Functor h, Functor h)
  => (ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)) -> f x :@@: xs -> h (g x :@@: ys)
expose f = withWitness @_ @f @g @xs @ys @x $ \w x -> f (ExistentiallyIndexed w x)

hide
  :: forall h f g xs ys
   . (Linear.Control.Functor h, Functor h) -- This use of Linear.Control.Functor is actually independent from the one guaranteeing safety in `withWitness`. This function uses it to actually move the received Witness into h.
  => (forall x. f x :@@: xs -> h (g x :@@: ys))
  -> ExistentiallyIndexed f xs
  %1 -> h (ExistentiallyIndexed g ys)
hide f (ExistentiallyIndexed @x w x) = Linear.Control.fmap (\(Ur y) -> ExistentiallyIndexed w y) L.$ Ur <$> f @x x

{- [markdown]
The function `expose` exposes the existential type hidden in `ExistentiallyIndexed`, while `hide` hides a type in `ExistentiallyIndexed`.
Now we can move on to the optics bit.
-}

vecToList :: Vec n a -> [a]
vecToList VNil = []
vecToList (VCons a as) = a : vecToList as

instance Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a as) = VCons (f a) (fmap f as)

-- Like `LensLike`, but it preserves the hidden index in the foci.
type PreservingLensLike h s t f xs g ys =
  (Linear.Control.Functor h, Functor h) => Lens.Over (FUN One) h s t (ExistentiallyIndexed f xs) (ExistentiallyIndexed g ys) -- = (ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)) -> s -> h t

partsOf
  :: (Linear.Control.Functor f, Functor f)
  => Lens.Traversing (->) f s t a b -> PreservingLensLike f s t Vec (LoT1 a) Vec (LoT1 b)
partsOf o f s =
  lazyVecFromList2 (ins b) -- Surprise! We actually need `lazyVecFromList2` to make `partsOf` lazy.
    & \(SomeVec @n v) ->
      -- `unsafeOuts` should be safe because `f` preserves the length of the vector.
      unsafeOuts b . vecToList <$> expose @n f v
 where
  b = o Lens.sell s
  ins = Lens.toListOf (Lens.getting Lens.bazaar)
  unsafeOuts = NL.evalState `Lens.rmap` Lens.bazaar (Lens.cotabulate (\_ -> NL.state (fromJust . NL.uncons)))

pTraverseOf
  :: forall xs ys h f g s t
   . (Applicative h, Linear.Control.Functor h)
  => (forall m. Applicative m => PreservingLensLike m s t f xs g ys)
  -> (forall x. f x :@@: xs -> h (g x :@@: ys))
  -> s
  -> h t
pTraverseOf o f = o $ hide $ \ @n -> f @n

-- This replaces all the `Char`s in a `[Either Bool Char]` with a `String` consisting of all the `Char`s in the list.
demo1 :: [Either Bool String]
demo1 =
  runIdentity $
    pTraverseOf
      (partsOf (Lens.traversed . Lens._Right))
      (\chars -> Identity $ fmap (const $ vecToList chars) chars)
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo1
-- This also segfaults in HLS and GHCi.

-- main = print demo1
-- prints [Left True,Right "hi",Left False,Right "hi"]

{- [markdown]
I'll admit, the demo is a bit contrived, but the point is that this shows how `partsOf` allows one to work over each element of a traversal with the context of all visited elements.
I also don't know the internals of `lens` well enough to say that this is the best way to implement `partsOf`.
I just took the current implementation and added conversions to and from vectors, but maybe there's a way to make the `Bazaar` use vectors directly or something like that.

And I lied.
The type-changing `partsOf` was not my actual goal.
I need it for something I plan to write an article about later™.
(Spoiler: it's more fancy optics).

Something else worth noting about the code block above is that we can actually define `PreservingLensLike` using an existing type from `lens`.
Some optic combinators already abstract over the profunctor in the optics transformation, so some combinators like [`taking`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:taking) and [`failing`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:failing) should also work with "preserving" optics.

Speaking of standard optics, wouldn't it be nice if we could use them on `ExistentiallyIndexed` and compose them with preserving optics?
-}

type instance Lens.Index (Vec n a) = Int
type instance Lens.IxValue (Vec n a) = a

instance Lens.Ixed (Vec n a) where
  ix 0 f (VCons a as) = flip VCons as <$> f a
  ix i f (VCons a as) = VCons a <$> Lens.ix i f as
  ix _ _ VNil = pure VNil

hidden
  :: forall f s t xs ys a b
   . (Linear.Control.Functor f, Functor f)
  => (forall x. (a -> f b) -> s x :@@: xs -> f (t x :@@: ys))
  -> (a -> f b)
  -> ExistentiallyIndexed s xs
  %1 -> f (ExistentiallyIndexed t ys)
hidden o f = hide $ \ @n -> o @n f

demo2 :: [Either Bool Char]
demo2 =
  runIdentity $
    Lens.traverseOf
      (partsOf (Lens.traversed . Lens._Right) . hidden (Lens.ix 1))
      (Identity . toUpper)
      [Left True, Right 'h', Left False, Right 'i']

-- main = print demo2
-- prints [Left True,Right 'h',Left False,Right 'I']
-- notice how the "i" at the end is now capitalized

{- [markdown]
As shown we can run standard optics like `Lens.ix` on `ExistentiallyIndexed` foci using the `hidden` combinator.
And while the example does not show it, you can see from the type of hidden that we could precompose it with standard optics (like `hidden (...) . standardOptic`), because the arrow in `(a -> f b)` in `hidden`'s type is not linear.

Finally, I'd also like to show how to define `Getter`s for preserving optics, because such a thing was not possible with some of my failed ideas for preserving optics.
-}

data Some f xs where
  Some :: forall x f xs. f x :@@: xs -> Some f xs

type PreservingLensLike' h s f xs = PreservingLensLike h s s f xs f xs

type PreservingGetter r s f xs = PreservingLensLike' ((,) r) s f xs

pView :: PreservingGetter (Some f xs) s f xs -> s -> Some f xs
pView o s = NL.fst $ o (hide (\ @x x -> (Some @x x, x))) s

{- [markdown]
## Wrapping up

The purpose of this article is put these ideas out there and see if someone sees any safety issues that I have overlooked.
As I mentioned in the introduction, you can play with the code in your browser using todo.
If you find something, please create a an issue [on GitHub](https://github.com/cdfa/existentials-on-a-leash/issues).

If no serious issues are found, I'll publish a small library containing the core types and functions to Hackage after a few weeks.
In the mean time, I'll continue working on the other optics I needed these techniques for.

Thanks for reading and have fun experimenting!

~cdfa
-}

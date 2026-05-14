{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{- [markdown]
# Existentials on a leash

In this article, I will share 2 new workarounds for (the lack of) existentially quantified type variables in Haskell.
The first workaround allows them to appear "naked" (without CPS-style/GADT wrapping) in a type signature, while the second allows for defining optics over types containing existentially quantified variables (though without having them appear naked in the type signature).

Both these techniques rely on witness-values passed linearly through some function.
I believe the linear use of these witnesses makes the use of unsafe functions in these techniques safe, though I have not proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs, linear types and optics (for the sections pertaining to them) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a [GitHub Codespace](https://codespaces.new/cdfa/existentials-on-a-leash?quickstart=1) prebuild (hint: use "Preview embedded markdown" to see the .hs file with its markdown version to the side).
Clicking that link will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser (or from a container on your computer).
It might even be a nice way to read the article because you can hover over values to see their types for example.

## Current limitations of existential types

As of GHC 9.12, GHC only supports 2 ways of "existentially quantifying" type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This corresponds to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

Both these techniques do not actually use existential quantification, but instead encode it through negated universal quantification.
Wrapping and unwrapping existential types using these techniques is not just cumbersome, but they're also insufficient for defining optics with existentially quantified foci, such as prisms for constructors of GADTs with existentially quantified fields.

[A proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding first-class existential types to GHC was written a while ago, but the author seems to be prioritizing other work.
The proposal also shows a simple example of a function that is impossible to write using the current workarounds: a lazy `filter :: (a -> Bool) -> Vec n a -> exists m. Vec m a`.

This article introduces 2 new workarounds.
The first can be used to implement some of the motivating examples from the proposal.
However, instead a lazy `filter`, I demonstrate the capability for functions that lazily produce an existentially-indexed type by defining a function `lazyVecFromList :: [a] -> Exists m (Vec m a)`.
My initial reason for this was that when I started this project, I was using vectors from an external package which did not export its constructors, and to test a lazy `filter` I also needed a lazy way to create vectors.
I didn't end up needing so many existing functions on vectors, so the article now defines its own vectors, but the example stayed.

And since that first workaround did not work so well for defining optics with existentially quantified types, I also demonstrate a second independent existential-types workaround that makes such optics possible.

But before we start looking at those workarounds, let's see why they are needed for a lazy `vecFromList`.
As mentioned before, we currently have to choose between using a rank-2-type and wrapping the vector in a GADT.
We'll work out the second option, but first we need to enable some language extensions and import some stuff.

<details>
<summary>Imports and language extensions</summary>

-}
{-# OPTIONS_GHC -Wall -Wno-missing-signatures -Wno-unused-top-binds -Wno-orphans #-}

{- HLINT ignore "Use first" -}

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

import Control.Functor.Linear hiding (Applicative (..), Functor (..), (<$>))
import Control.Functor.Linear qualified as Control
import Control.Lens qualified as Lens
import Control.Lens.Internal.Bazaar qualified as Lens
import Control.Lens.Internal.Context qualified as Lens
import Control.Monad.Except
import Control.Monad.State.Lazy qualified as NL
import Data.Bifunctor.Linear
import Data.Char
import Data.Functor qualified as NL
import Data.Functor.Identity
import Data.Functor.Linear qualified as L
import Data.Kind
import Data.List as NL
import Data.Maybe
import Data.PolyKinded hiding (Nat)
import Data.Profunctor.Rep qualified as Lens
import Data.Tuple qualified as NL
import Data.Type.Equality
import Data.Unrestricted.Linear
import GHC.Base (Multiplicity (..), TYPE)
import Prelude.Linear hiding (fst, ($), (.))
import Prelude.Linear qualified as L
import Unsafe.Coerce (unsafeCoerce)
import Prelude as NL (Applicative (..), Functor (..), const, ($), (<$>))

-- Multiplicity polymorphic version of `(.)` which works in most non-linear code as well.
(.) :: forall {rep} b (c :: TYPE rep) a m n. (b %m -> c) %n -> (a %m -> b) %m -> a %m -> c
(.) f g x = f (g x)
infixr 9 .

{- [markdown]
</details>

The main thing to remember is that we use `L` and `NL` to disambiguate linear and non-linear functions, respectively, where needed.

Now we can define our vectors and `vecFromList`:
-}

data Nat = Zero | Succ Nat

data Vec n a where
  VNil :: Vec Zero a
  VCons :: a %1 -> Vec n a %1 -> Vec (Succ n) a

data SomeVec a where
  SomeVec :: forall n a. Vec n a %1 -> SomeVec a

vecFromList :: [a] -> SomeVec a
vecFromList [] = SomeVec VNil
vecFromList (a : as) =
  vecFromList as & \(SomeVec aVec) -> SomeVec $ VCons a aVec

{- [markdown]
If you've never seen the `%1` used the definition for `VCons`, you can ignore them for now.
This marks the fields of the constructor as linear, which will be explained more later.

Pattern matching on `SomeVec aVec` at every usage site of `vecFromList` is not only tedious, but it also makes the function strict in the length of the list.
We have no other choice though.
`SomeVec $ vecFromList as & \(SomeVec @n aVec) -> VCons a aVec` can not be typed because the `n` tied to the unwrapped `SomeVec` would escape its scope.

The CPS-variant would not help either for a similar reason: the continuation can't be applied before the recursive application of `vecFromList`.

As the author of the existential types proposal states for the `filter` function, it's not possible to define a lazy version in GHC's current type system.

 *So we have to work around it.*

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

Putting the dangers of this approach aside for a moment, given a value of type `Fresh n`, we should allow `n` to be coerced to some other type `b`.
But in `vecFromList` we don't have values of type `n`, only `Vec n a`.
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
Values of a type `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
So as long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

The first steps to this are (1) to hide the constructor `Fresh` and (2) to require that a `Fresh`-value is used linearly in the continuation passed to `unpack`, like so:
-}

newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

type Exists a b = Fresh a %1 -> b -- conceptually this should be `forall a. Fresh a %1 -> b`, but that prevents `a` from being used in `b` and defeats the entire point.

unpack2 :: (forall a. Exists a r) %1 -> r
unpack2 f = f L.$ Fresh $ unsafeCoerce Refl

pack :: forall b r a. (a ~ b => r) %1 -> Exists a r
pack r (Fresh (Refl :: a :~: b)) = r

{- [markdown]
The `%1` in `type Exists a b = Fresh a %1 -> b` demands that the function is linear.
This means that the compiler will verify that such a function will evaluate the argument exactly once if the result of the function is evaluated to normal form.
These annotations can also be used in the types for GADT constructors (like `VCons`).
In that case, the values in those fields must be used linearly when you pattern match on that constructor in a linear function.

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
I think the trick to prevent this is pretty neat: we must require that `r` produced by `unpack` *can* be linearly duplicated, i.e., it's an instance of [`Dupable`](https://hackage-content.haskell.org/package/linear-base-0.7.0/docs/Data-Unrestricted-Linear.html#t:Dupable).

To understand why, we must realize 3 things:
1. A `Fresh`-value can only be captured by a *linear* field (like `(Bool -> GADT a)` in `Wrapper`). Otherwise the `Fresh`-value would not be consumed linearly.
2. A type that is `Dupable` can only contain a linear field when that field is also `Dupable`, but a function is not (even if it's input is `Bounded`, because finding the different outputs requires applying the function multiple times).
3. `Fresh` is not `Dupable`, so because of 1. and 2. it can not occur in a `Dupable` value.

Therefore, it is safe to duplicate a `Dupable` value after it's produced by `unpack` and we arrive at the final version of `unpack`:
-}

unpack :: Dupable r => (forall a. Exists a r) %1 -> r
unpack f = f L.$ Fresh $ unsafeCoerce Refl

{- [markdown]
So is this completely safe now?
Well, only if `Dupable r` is a faithful instance of `Dupable`.
If you implement `dup` as `error "this is never used anyway"` for a linearly captured function, you'd get away with it and you could still write the `conflict` expression from before.
We could have `unpack` call `dup` to verify this does not happen, but that would make it so strict that it becomes useless for implementing a lazy `vecFromList`.

Alternatively, we could define a closed type family `ClosedDupable` which uses a generic representation of a type (like `GHC.Generics.Rep`) to see if it contains a linear function field (if you don't know `kind-generics`, it extends the language of `GHC.Generics` such that GADTs can also get a generic representation).
However, `Rep` can currently not be defined for GADTs, so this would severely limit the values that can can escape `unpack`.
This can be solved by using [`RepK`](https://hackage.haskell.org/package/kind-generics-0.5.0.0/docs/Generics-Kind.html#t:RepK) from `kind-generics`, but the drawback there is that this requires users to derive `RepK` using template haskell or define it manually, and I don't think that's worth the extra safety.

Another alternative I've considered is to use the property of `Fresh`-values that the `a` in `Fresh a` is always existential.
We can prevent a GADT from capturing it by using a similar type family to inspect the generic representation as mentioned above.
This might be good solution for when you do need to have a function as a linear field in `r`, but generally I think it's a more severe restriction that `Dupable`.

In summary, I believe `unpack` is only unsafe when used in combination with other unsafe functions (in the implementation of `Dupable`).
To me, that's acceptable.
There are some safer alternatives, but they require more effort from the user and don't justify the cost.

Now let's continue and finally define a lazy `vecFromList`:
-}

lazyVecFromList0 :: Dupable a => [a] %m -> Exists n (Vec n a)
lazyVecFromList0 [] n = pack @Zero VNil n
lazyVecFromList0 (a : as) n =
  -- This `unpack` actually unpacks the `Vec` produced by the recursive call, not the one `pack`ed immediately below
  unpack
    -- TypeAbstractions syntax
    ( \ @predN predN ->
        pack @(Succ predN) (VCons a L.$ lazyVecFromList0 as predN) n
    )

{- [markdown]
The manual `pack`ing and `unpack`ing makes the definition adds significant verbosity, but I believe each use is necessary.
The `pack`s are needed because neither `VNil` nor `VCons` produce vectors of arbitrary length, and we can't remove the `unpack` because we can't use the same `Fresh`-value for coercing the `VCons`.

However, as you'll see in the next code block, we can abstract some of the verbosity away.

We should also test that this definition is actually lazy.
Sadly this is a little more complicated than I hoped because the produced vector also has to be consumed linearly (until it escapes the `unpack` that provides the initial `Fresh`-value that's used).
That's because linear arrows don't just require that the argument is consumed exactly once.
They say that if the caller evaluates the produced value to normal form, then the function will evaluate the argument to normal form exactly once.
So a function `f` that takes a `Fresh`-value in `unpack` and passed it to `lazyVecFromList0` must also treat the produced vector linearly (i.e. use it for the `f`'s result in some way).

You might also have noticed that there is a multiplicity polymorphic arrow (`%m ->`) after `[a]` in the type annotation of `lazyVecFromList0`.
This means that the function can be used as either a linear or a non-linear one.
We could've used a linear arrow as well, but then we'd have to convert the function to a non-linear one when used in such a context.
That isn't hard, but it means extra boiler-plate.

As an aside, in an ideal world, the multiplicity of all functions would just be inferred to the strictest possibility.
Then we wouldn't have to redefine existing functions just to give them a linear or multiplicity-polymorphic type annotation.
This might never happen, because then even people who don't use linear types pay the computing cost of inferring the linear type.
Since Haskell people usually compile all dependencies locally anyway, I think there is a way to avoid this where the automatic inference is only enabled for any dependency or dependent module of a module that uses linear types, but that would require some magic on Cabal's side that I don't see happening any time soon.

What's more important is that the linear arrow in `Exists` demands that when the function is called with a linear `Fresh`-value (which is always, due to `unpack` being the only way of getting a `Fresh`), the produced vector is treated linearly as well until it escapes the scope of `unpack`.
It would be much nicer if we could have `lazyVecFromList0 :: [a] -> Exists n (Ur (Vec n a))`  (where `Ur` (for Unrestricted) is a simple non-linear wrapper for any value).
That's no problem for the `[]`-case, but it would mean that we have to pattern match on `Ur` in the recursive case, which in turn means the function always evaluates until the final `Ur` produced in the `[]`-case, which would make the function strict in the length of the list.

Now that's all cleared up, here is the small `pack`/`unpack` abstraction I promised:
-}

repack :: forall f n a. Dupable a => (forall m. n ~ f m => Exists m a) %1 -> Exists n a
repack f n = unpack (\ @m m -> pack @(f m) (f m) n)

lazyVecFromList1 :: Dupable a => [a] %m -> Exists n (Vec n a)
lazyVecFromList1 [] = pack @Zero VNil
lazyVecFromList1 (a : as) = repack (VCons a . lazyVecFromList1 as)

{- [markdown]
I'm actually quite surprised the recursive case does not need any type arguments despite `f` only occurring in a constraint.

Now for the laziness test:
-}

lazyVecFromListIsLazy :: Maybe Int
lazyVecFromListIsLazy =
  unpack (SomeVec . lazyVecFromList1 (0 : error "second element evaluated")) & \case
    (SomeVec (VCons a _)) -> Just a
    _ -> Nothing

-- >>> lazyVecFromListIsLazy
-- Just 0

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

deriving instance Show a => Show (Vec n a)
deriving instance Show a => Show (SomeVec a)
deriving instance Show a => Show (Ur a)

{- [markdown]
</details>

And thus we prove the laziness of `lazyVecFromList1`!
We do need a GADT wrapper to use it though, because otherwise the `Fresh`-variable would escape its scope.
We also can't pattern match inside `unpack` because we have to discard the tail of the vector.
Inside `unpack` we'd have to do that linearly, which is possible to do with `consume` (from a superclass of `Dupable`), but that would break the test by evaluating the tail to normal form.

-- todo: change title
### Constraints on existential type variables

Aside from the `exists` quantifier, the existential types proposal also proposes a type level operator `(/\) :: Constraint -> Type -> Type` that puts constraints on a given type.
This operator gets some special treatment during type checking, but when `pack`/`unpacking` is explicit like in our implementation, it seems the current type checking algorithm already does quite well!
-}

data (/\) c a where
  SuchThat :: c => a %1 -> c /\ a

infix 3 `SuchThat`
type SuchThat a c = c /\ a

vecNonEmpty :: forall n m a. Vec n a %1 -> Exists m (Maybe (Vec (Succ m) a `SuchThat` n ~ Succ m))
vecNonEmpty VNil = flip lseq Nothing
vecNonEmpty (VCons @_ @o x xs) = pack @o (Just L.$ SuchThat (VCons x xs))

vecUncons :: Vec (Succ n) a %1 -> (a, Vec n a)
vecUncons (VCons a as) = (a, as)

demo0 :: Maybe (Integer, SomeVec Integer)
demo0 =
  unpack
    ( \n ->
        unpack
          ( \m ->
              let
                !(v1, v2) = dup L.$ lazyVecFromList1 [0 .. 3] n
              in
                case vecNonEmpty v1 m of
                  Just (SuchThat v3) -> lseq v3 L.$ Just L.$ second SomeVec L.$ vecUncons v2 -- we can use v2 here since we have `n ~ Succ m` from `vecNonEmpty`!
                  Nothing -> lseq v2 Nothing
          )
    )

-- >>> demo0
-- This segfaults in HLS and GHCi. Will create an issue later.

-- main = print demo0
-- prints "Just (0,SomeVec (VCons 1 (VCons 2 (VCons 3 VNil))))"
{- [markdown]
This demo is a bit contrived because I wanted to use the `n ~ Succ m` explicitly and linear types force the explicit duplication and consumption of values, but I think the point should be clear: no explicit type annotations outside those of functions signatures were needed to make GHC resolve all constraints correctly!

While that "inconvenience" is by design, there are also still a lot of unintentional difficulties with working with linear types:
  * There is no multiplicity inference yet. This means that most existing Haskell code is unusable, even if the implementation of a function is actually linear.
  * The error messages don't say where a value is not used linearly, only which variable.
  * Even if a function only captures `Consumable` or `Dupable` values in it's closure, it's not `Consumable` or `Dupable`.
  * Linear pattern synonyms are not supported yet.
  * All the other limitations mentioned in the [docs](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html#limitations).

So while this linear-existentiality-witness-techinique allows some things that are not possible with the existing existential-type-workarounds, I can't recommend using it outside of cases that are very limited in scope like `lazyVecFromList`.

Luckily, we can define a `lazyVecFromList` that hides all of the linear-types complexity and falls back to GADT-wrapper workaround:
-}

lazyVecFromList :: [a] -> SomeVec a
lazyVecFromList xs =
  unpack (SomeVec L.. lazyVecFromList1 (fmap Ur xs))
    & \(SomeVec vec) -> SomeVec $ L.fmap unur vec

{- [markdown]

todo: title
## Invisible type preservation with linear control functors

 *I discovered the trick above almost 2 years ago.*

I put it on GitHub, but never mentioned it because I had not yet succeeded in my actual goal: to make a safe version of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.
The hard thing about this is that to enable it to change the types of the foci of the argument `Traversable`, we need to ensure that the lists in the focus of `partsOf` are of the same length, while at the same time, this length cannot be known by the caller.
Because I wanted the optic to be compatible with the existing `lens` ecosystem, a rank-2-type or GADT-wrapper wouldn't work.
I thought I could use the linear-existentiality-witness-techinique , but when I tried it in `partsOf :: Functor f => Traversing (->) f s t a b -> Fresh n %1 -> LensLike f s t (Vec n a) (Vec n b)`, the fact that the resulting optic must be used linearly, makes it just as incompatible with `lens` as the rank-2-type version.

To be clear, if you unfold the `LensLike f s t (Vec n a) (Vec n b)` to `(forall n. Vec n a -> f (Vec n b)) -> s -> f t` (i.e. use a rank-2-type), you can implement `partsOf` just fine, but this optic can't be used in functions like `traverseOf` or pre-composed with other optics with `.`.
For a long time, I banged my head against the wall trying to think of a way to make a type-changing `partsOf` that would be compatible with the rest of `lens`, and so the project stayed on my list of things to get back to at some point.
It's somewhat regrettable that I didn't just publish the first part of this article anyway, but on the other hand I found quite a few serious mistakes when I came back to it, so I'm also happy I caught those before publishing.

I now think making a safe type-changing `partsOf` that is compatible with all the functions from `lens` is impossible, but I did find a way to solve the `.`-pre-composition issue, again using linear functions.
The rest of this section is dedicated to this technique.

The first idea to make this work is that instead of having an existential type `n` for the length of the vector exposed in the type signature of `partsOf`, we hide it using a type called `ExistentiallyIndexed`, so the focus type of the optic becomes something like `ExistentiallyIndexed Vec a`.
The second idea is that a function that takes a value `Witness x`, with `x` universally quantified and no other sources of any `Witness` in scope, and which must produce some `Witness y` value, with `y` existentially quantified, can only produce the original `Witness x` value. Thus we can infer `y ~ x`.
I don't have a formal proof of this either, but hopefully it will become clear when I show the implementation.

Let's start with a definition for `ExistentiallyIndexed`.
We don't want it to be specific to vectors, or even types with kind `k -> Type -> Type`.
We will use the kind-heterogeneous type-level lists from `kind-apply`, named [`LoT`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t:LoT) and the operator [`:@@:`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t::-64--64-:) which applies a type level list to a type constructor.
This permits the following definition of `ExistentiallyIndexed`:
-}

data Witness x = Witness -- consider the constructor hidden
  deriving (Show)

data ExistentiallyIndexed f xs where
  ExistentiallyIndexed :: Witness y %1 -> f y :@@: xs -> ExistentiallyIndexed f xs -- Note the linear arrow for `Witness x`
  {- [markdown]
  Now we can make the functions meant in the second idea concrete. An example would be a function with type `forall x y. Witness x -> Exists y (Witness y)`.
  Since there are no other sources of `Witness` in scope, the only way to obtain a `Witness` value is from the argument of the function.
  Hence we can derive `x ~ y`.

  Now let's extend this "proof" slightly by allowing the function to take and produce additional values, e.g. `forall x f g xs ys. Witness x -> f x :@@: xs -> ExistentiallyIndexed g ys`.
  This adds a potential source of `Witness` values, since `f` is universally quantified.
  To make it impossible for Witness values to be passed to the function through the additional argument, we must make it impossible for the given value to appear in the result anywhere else than in the first field of `ExistentiallyIndexed`.
  This is relatively easy to achieve by making the arrow that takes `Witness x` linear, i.e., `forall x f g xs ys. Witness x %1 -> f x :@@: xs -> ExistentiallyIndexed g ys`.

  This only permits `Setter` optics though, which is a bit disappointing.
  We need to extend the "proof" further to allow functions that produce a functorial context of `ExistentiallyIndexed`, like `forall x f g h xs ys. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys)`.
  This is tricky because `h` is also universally quantified and could be chosen to be something like
  -}

data ConstWitness a where
  ConstWitness :: Witness x %1 -> ConstWitness a

{- [markdown]
which would allow the Witness value to enter `Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys)`-functions elsewhere, e.g. through `f x :@@: xs`.
To prevent this, we need to require `h (ExistentiallyIndexed f x)` to contain at least one `ExistentiallyIndexed f x`.
Luckily, a solution for this already exists: linear control functors.
I'd never heard about them before this project and I only ran into them because I was confused which `Functor` module from `linear-base` I needed to import.
I recommend reading [Arnaud's blogpost](https://www.tweag.io/blog/2020-01-16-data-vs-control/) on them if you're unfamiliar, but I'll also briefly explain here.

In short, in the linear world, there are 2 types of functors: data functors and control functors.
The type of `Control.Functor.Linear.fmap` is `(a %1 -> b) %1 -> f a %1 -> f b`, while the type of `Data.Functor.Linear.fmap` is `(a %1 -> b) -> f a %1 -> f b`.
The key difference with data functors is that a control functor consumes its argument function linearly (`%1` on the second arrow) while data functors don't.
Thus, only functors that contain their argument type exactly once can be control functors.
For example `State` and `IO` are control functors, while `[]` and `Const` aren't.

In a strict programming language, the above would be enough.
To show why it is not, I first need to write a function that actually uses the "proof":
-}

-- todo: check linearity of all functions
-- todo: rename witness

preserving0
  :: forall h f g xs ys a
   . (Control.Functor h, Functor h) -- The normal non-linear Functor is not a superclass of Control.Functor, so we need to add both.
  => (forall x. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys))
  -> f a :@@: xs
  -> h (g a :@@: ys)
preserving0 f x = f @a Witness x NL.<&> \(ExistentiallyIndexed Witness y) -> unsafeCoerce y

problem =
  NL.fst $
    preserving0 @((,) (ExistentiallyIndexed Vec (LoT1 Int))) @Vec @_ @(LoT1 Int) @_
      (\w l -> (ExistentiallyIndexed w l, error "The consequences of my actions"))
      VNil

-- very specific simple Show instance for the purpose of this example
instance Show a => Show (ExistentiallyIndexed Vec (LoT1 a)) where
  show (ExistentiallyIndexed w x) = show (w, x)

-- >>> problem
-- (Witness,VNil)
{- [markdown]
We have successfully ignored the consequences of our actions and thus obtained an unrestricted `Witness`-value!
That could be abused to cause all sorts of mayhem in other uses of `preserving0`.

As mentioned before, the problem lies with strictness, or rather laziness in this case.
The caller of `preserving0` can always choose not to evaluate the `ExistentiallyIndexed` in the right side of the tuple, and thus the passed witness can escape.
It's not enough to call `deepseq` on the produced `h (ExistentiallyIndexed g ys)`, because if we take `h` as `State s` for example, `deepseq` would not ensure `g a :@@: ys` is evaluated to weak-head-normal-form before the tuple in the definition of `State` is created (and the `NFData` instance for `a -> b` has been deprecated for a while anyway).
Moreover, we don't want to force the entire `h (ExistentiallyIndexed g ys)`-value.

We need a `fmap` that allows evaluating a part of the `a` in `f a` to weak-head-normal-form before producing an `f b` (or the result of a function that produces `b` in cases that embed a function like `StateT s m`).
It must be "a part of `a`", because if we implement this for `StateT s m`, we need to recursively apply the function to `m (a, s)`, and we want to evaluate a part of that `a`, not `m`'s "element" (the tuple `(a, s)`).

We'll accomplish this with a new class called `SeqElement` (name is subject to change):
-}
class L.Functor f => SeqElement f where
  mapAndSeq :: Consumable c => (a %1 -> (b, Maybe c)) -> f a %1 -> f b

{- [markdown]
Let't check that we can define instances for `SeqElement` for some common functors.
-}

instance SeqElement Identity where
  mapAndSeq extract (Identity a) = extract a & \(b, c) -> lseq c L.$ Identity b

instance SeqElement m => SeqElement (StateT s m) where
  mapAndSeq extract (StateT f) = StateT L.$ mapAndSeq extract' . f
   where
    extract' (a, s) = extract a & \(b, c) -> ((b, s), c)

instance SeqElement m => SeqElement (ExceptT e m) where
  mapAndSeq extract (ExceptT m) = ExceptT L.$ flip mapAndSeq m L.$ \case
    Left e -> (Left e, Nothing)
    Right a -> first Right L.$ extract a

instance SeqElement ((,) a) where
  mapAndSeq extract (a, b) = extract b & \(d, c) -> lseq c (a, d)

{- [markdown]
So far so good!
Let's check that this solves our `problem`.
-}

seqAndMap :: (SeqElement f, Consumable c) => f a %1 -> (a %1 -> (b, Maybe c)) -> f b
seqAndMap = flip mapAndSeq

preserving1
  :: forall h f g xs ys a
   . (Control.Functor h, SeqElement h)
  => (forall x. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys))
  -> f a :@@: xs
  -> h (g a :@@: ys)
preserving1 f x = f @a Witness x `seqAndMap` \(ExistentiallyIndexed Witness y) -> (unsafeCoerce y, Just ())

problemSolved =
  NL.fst $
    preserving1 @((,) (ExistentiallyIndexed Vec (LoT1 Int))) @Vec @_ @(LoT1 Int) @_
      (\w l -> (ExistentiallyIndexed w l, error "The consequences of my actions"))
      VNil

-- >>> problemSolved
-- The consequences of my actions

{- [markdown]
Calling a problem "solved" when your function returns an `error` instead of a proper value feels odd, but that's what you get when working with unsafe primitives.

With this, I believe we've finally neutralized the dangers of the `unsafeCoerce` in `preserving`!
I wasn't quite satisfied though.
Our current definition requires that `h` is a linear control functor, but that's actually quite a severe limitation.
For example, `Either e` and `ExceptT m e` are excluded.
Also conceptually, our requirement of `h` that it contains at least one element `a` is conceptually more strict than necessary.
For example, it's fine if `h` does not contain `a` when `h ()` is `Dupable`, because that would prevent `h` from containing a `Witness`.
But `StateT s m ()` is not `Dupable` despite not containing a `Witness`, so that rule is also overly restrictive.

To discover a more suitable general rule, let's first look at conversions between `ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)`-functions and rank-2 based existentials:
-}

expose0
  :: forall x h f g xs ys
   . (Control.Functor h, SeqElement h)
  => (ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)) -> f x :@@: xs -> h (g x :@@: ys)
expose0 f = preserving1 @_ @f @g @xs @ys @x $ \w x -> f (ExistentiallyIndexed w x)

hide0
  :: forall h f g xs ys
   . (Control.Functor h, Functor h)
  => (forall x. f x :@@: xs -> h (g x :@@: ys))
  -> ExistentiallyIndexed f xs
  %1 -> h (ExistentiallyIndexed g ys)
hide0 f (ExistentiallyIndexed @x w x) = Control.fmap (\(Ur y) -> ExistentiallyIndexed w y) L.$ Ur <$> f @x x
{- [markdown]
The function `expose0` exposes the existential type hidden in `ExistentiallyIndexed`, while `hide0` hides a type in `ExistentiallyIndexed`.
Note that `hide0` actually uses the `Control.Functor h` constraint to move the linear `Witness` w into `h`.

The insight that leads to a looser requirement for safe `h`'s is that there is a another way to move a linear value into a functor: `L.liftA2 (\w' (Ur y) -> ExistentiallyIndexed w' y) (Control.pure w) hy`.
That uses `Control.pure` from `Control.Applicative`, which is of course a subclass of `Control.Functor`, so it does not help yet.
`Control.pure` can not be implemented for something like `ConstWitness`, so requiring an implementation for `h` guards against some bad cases, but not all yet: 

 also guards against these cases that let the `Witness` escape, even without the `Control.Functor` superclass.
Because of that, we can split `Control.pure` out into a separate class that does not extend `Control.Functor`.
This has been done for the non-linear pure as well, and it's called [`Pointed`](https://hackage.haskell.org/package/pointed-5.0.5/docs/Data-Pointed.html).
We'll define our own linear version:
-}

class L.Functor f => Pointed f where
  point :: a %1 -> f a

{- [markdown]

<details>
<summary>Instances</summary>

-}

instance Pointed Identity where
  point = Identity

instance Pointed m => Pointed (StateT s m) where
  point a = StateT L.$ \s -> point (a, s)

instance Pointed m => Pointed (ExceptT e m) where
  point a = ExceptT L.$ point L.$ Right a
{- [markdown]
</details>


-}


class AffineFunctor f where
  aMap :: Consumable a => (a %1 -> b) -> f a %1 -> f b

instance AffineFunctor (Either e) where
  aMap _ (Left e) = Left e
  aMap f (Right a) = Right L.$ f a

instance L.Functor m => AffineFunctor (ExceptT e m) where
  aMap f (ExceptT m) = ExceptT L.$ L.fmap (L.fmap f) m

instance L.Functor m => AffineFunctor (StateT s m) where
  aMap f (StateT t) = StateT L.$ L.fmap (first f) . t

class AffineFunctor f => AffineApplicative f where
  aPure :: a %1 -> f a
  aLiftA2
    :: (Consumable a, Consumable b)
    => (a %1 -> b %1 -> c) -> f a %1 -> f b %1 -> f c

instance Consumable e => AffineApplicative (Either e) where
  aPure = Right
  aLiftA2 _ (Left e) r = lseq r L.$ Left e
  aLiftA2 _ l (Left e) = lseq l L.$ Left e
  aLiftA2 f (Right a) (Right b) = Right L.$ f a b

instance (AffineApplicative m, L.Functor m, Consumable e) => AffineApplicative (ExceptT e m) where
  aPure = ExceptT . aPure . Right
  aLiftA2 f (ExceptT m) (ExceptT n) = ExceptT L.$ aLiftA2 (aLiftA2 f) m n

instance Control.Monad m => AffineApplicative (StateT s m) where
  aPure a = StateT L.$ \s -> Control.pure (a, s)
  aLiftA2 f (StateT ta) tb = StateT L.$ \s0 -> do
    ta s0 >>= \(a, s1) ->
      Control.fmap (\(b, s2) -> (f a b, s2)) L.$ runStateT tb s1

data Dict :: Constraint -> Type where
  Dict :: a => Dict a

class SeqElement f => Capturing f where
  applicativeOrControl :: Either (Dict (AffineApplicative f, Pointed f)) (Dict (Control.Functor f))

instance Capturing Identity where
  applicativeOrControl = Right Dict -- We pick the linear control functor option because it's more efficient than AffineApplicative+Pointed

instance (Control.Functor m, SeqElement m) => Capturing (StateT s m) where
  applicativeOrControl = Right Dict -- the `AffineApplicative` for `StateT s m` requires `Control.Monad m`, so even if `applicativeOrControl @m` is `Left`, using `Right` for `StateT s m` leads to the least stringent constraints.

instance Capturing ((,) a) where
  applicativeOrControl = Right Dict

instance
  ( AffineApplicative m
  , Consumable e
  , Pointed m
  , SeqElement m
  )
  => Capturing (ExceptT e m)
  where
  applicativeOrControl = Left Dict

preserving
  :: forall h f g xs ys a
   . Capturing h
  => (forall x. Witness x %1 -> f x :@@: xs -> h (ExistentiallyIndexed g ys))
  -> f a :@@: xs
  -> h (g a :@@: ys)
preserving f x = f @a Witness x `seqAndMap` \(ExistentiallyIndexed Witness y) -> (unsafeCoerce y, Just ())

expose
  :: forall x h f g xs ys
   . (Capturing h, Functor h)
  => (ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)) -> f x :@@: xs -> h (g x :@@: ys)
expose f = preserving @_ @f @g @xs @ys @x $ \w x -> f (ExistentiallyIndexed w x)

hide
  :: forall h f g xs ys
   . (Capturing h, Functor h)
  => (forall x. f x :@@: xs -> h (g x :@@: ys))
  -> ExistentiallyIndexed f xs
  %1 -> h (ExistentiallyIndexed g ys)
hide f (ExistentiallyIndexed @x w x) =
  let
    hy = Ur <$> f @x x
  in
    case applicativeOrControl @h of
      Left Dict -> aLiftA2 (\w' (Ur y) -> ExistentiallyIndexed w' y) (point w) hy
      Right Dict -> Control.fmap (\(Ur y) -> ExistentiallyIndexed w y) hy

instance Consumable (Witness x) where
  consume Witness = ()

instance Consumable (ExistentiallyIndexed f xs) where
  consume (ExistentiallyIndexed w _) = consume w

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
  Capturing h
  => Lens.Over (FUN One) h s t (ExistentiallyIndexed f xs) (ExistentiallyIndexed g ys) -- = (ExistentiallyIndexed f xs %1 -> h (ExistentiallyIndexed g ys)) -> s -> h t

partsOf
  :: (Capturing f, Functor f, Capturing f)
  => Lens.Traversing (->) f s t a b -> PreservingLensLike f s t Vec (LoT1 a) Vec (LoT1 b)
partsOf o f s =
  lazyVecFromList (ins b) -- Surprise! We actually need `lazyVecFromList2` to make `partsOf` lazy.
    & \(SomeVec @n v) ->
      -- `unsafeOuts` should be safe because `f` preserves the length of the vector.
      unsafeOuts b . vecToList <$> expose @n f v
 where
  b = o Lens.sell s
  ins = Lens.toListOf (Lens.getting Lens.bazaar)
  unsafeOuts = NL.evalState `Lens.rmap` Lens.bazaar (Lens.cotabulate (\_ -> NL.state (fromJust . NL.uncons)))

pTraverseOf
  :: forall xs ys h f g s t
   . (Applicative h, Capturing h)
  => (forall m. (Applicative m, Capturing m, Capturing m) => PreservingLensLike m s t f xs g ys)
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
      (\chars -> Identity $ fmap (NL.const $ vecToList chars) chars)
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo1
-- This also segfaults in HLS and GHCi.

-- main = print demo1
-- prints [Left True,Right "hi",Left False,Right "hi"]
{- [markdown]
I'll admit, the demo is a bit contrived again, but the point is that this shows how `partsOf` allows you to work over each element of a traversal with the context of all visited elements.
I also don't know the internals of `lens` well enough to say that this is the best way to implement `partsOf`.
I just took the current implementation and added conversions to and from vectors, but maybe there's a way to make the `Bazaar` use vectors directly.
I'm not even sure that would be a good thing.

And I lied.
The type-changing `partsOf` was not my actual goal.
I need it for something I plan to write an article about later™.
(Spoiler: it's more fancy optics).

Something else worth noting about the code block above is that we can actually define `PreservingLensLike` using an existing type from `lens`.
Some optic combinators already abstract in the profunctor in the optics transformation, so combinators like [`taking`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:taking) and [`failing`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:failing) should also work with "preserving" optics.

Speaking of standard optics, wouldn't it be nice if we could use them on `ExistentiallyIndexed` and compose them with preserving optics?
-}

type instance Lens.Index (Vec n a) = Int
type instance Lens.IxValue (Vec n a) = a

instance Lens.Ixed (Vec n a) where
  ix 0 f (VCons a as) = flip VCons as <$> f a
  ix i f (VCons a as) = VCons a <$> Lens.ix (pred i) f as
  ix _ _ VNil = error "a proper `ix` for vectors would use some integral type with a type-level upper bound"

hidden
  :: forall f s t xs ys a b
   . (Capturing f, Functor f)
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

main = print demo2

-- prints [Left True,Right 'h',Left False,Right 'I']
-- notice how the "i" at the end is now capitalized
{- [markdown]
As shown we can run standard optics like `Lens.ix` on `ExistentiallyIndexed` foci using the `hidden` combinator.
And while the example does not show it, you can see from the type of hidden that we could precompose it with standard optics (like `hidden (...) . standardOptic`), because the arrow in `(a -> f b)` in `hidden`'s type is not linear.

Finally, I'd also like to show how to define `Getter`s for preserving optics, because this was not possible with some of my failed ideas for preserving optics.
-}

data Some f xs where
  Some :: forall x f xs. f x :@@: xs -> Some f xs

type PreservingLensLike' h s f xs = PreservingLensLike h s s f xs f xs

type PreservingGetter r s f xs = PreservingLensLike' ((,) r) s f xs

pView :: Dupable (Some f xs) => PreservingGetter (Some f xs) s f xs -> s -> Some f xs
pView o s = NL.fst $ o (hide (\ @x x -> (Some @x x, x))) s

{- [markdown]
## Wrapping up

The purpose of this article is put these ideas out there and see if someone sees any safety issues that I have overlooked.
As I mentioned in the introduction, you can play with the code in your browser using a [GitHub Codespace](https://codespaces.new/cdfa/existentials-on-a-leash?quickstart=1).
If you find something, please create an issue [on GitHub](https://github.com/cdfa/existentials-on-a-leash/issues).

If no serious issues are found after a few weeks, I'll publish a small library containing the core types and functions to Hackage.
In the meantime, I'll continue working on the other optics I needed these techniques for.

Thanks for reading and have fun experimenting!

~cdfa
-}

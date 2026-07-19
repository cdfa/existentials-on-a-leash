{- [markdown]
# Existentials on a leash

In this article, I will share a new workaround for the limited nature of existential quantification in current Haskell.
Specifically, I will show the implementation of an `Exists` quantifier that relieves us from having to wrap existential type variables with a GADT constructor or with a higher-rank function (CPS-style), and instead allows them to appear "naked" in types.
The quantifier is implemented as a type synonym for a function that linearly consumes a proof-token that ensures proper treatment of existentially typed values.

Additionally, I share an independent technique that ensures functions instantiate hidden ("non-naked") existential types in their result with the same type as its input type is instantiated, i.e. they preserve the instantiation of hidden type variables.
This technique also relies on linear types, but not the existential quantifier mentioned before.
I will demonstrate this technique by implementing a safe variant of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.

Both techniques use `unsafeCoerce`.
I explain why I believe the coercions are safe, but I haven't proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what linear types are, this article is not meant as a general introduction to this concept.
Familiarity with GADTs, linear types and optics (for the sections pertaining to those) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a [GitHub Codespace](https://codespaces.new/cdfa/existentials-on-a-leash?quickstart=1) prebuild (hint: use "Preview embedded markdown" to see the .hs file with its markdown version to the side).
Clicking that link will allow you to tinker with the code with the support of the Haskell Language Server without needing to install anything.
It might even be a nice way to read the article because you can hover over variables and functions to see their types for example.

## Current limitations of existential types

As of GHC 9.14, GHC only supports 2 ways of "existentially quantifying" type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This corresponds to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

Both these techniques do not actually use existential quantification, but instead encode it through negated universal quantification.
Wrapping and unwrapping existential types using these techniques is not just cumbersome, but they're also insufficient for defining optics with existentially quantified foci, such as prisms for constructors of GADTs with existentially quantified fields.

[A GHC proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding first-class existential types to GHC was written a while ago, but the author seems to be prioritizing other work.
The proposal also shows a simple example of a function that is impossible to write using the current workarounds: a lazy `filter :: (a -> Bool) -> Vec n a -> exists m. Vec m a`.

This article introduces 2 new (as far as I am aware) techniques.
The first can be used to implement some of the motivating examples from the GHC proposal.
However, instead a lazy `filter`, I demonstrate the capability for functions to lazily produce an existentially indexed type by defining a function `lazyVecFromList :: [a] -> Exists m (Vec m a)`.
My initial reason for this was that when I started this project, I was using vectors from an external package which did not export its constructors, and to test a lazy `filter` I also needed a lazy way to create vectors.
I didn't end up needing so many existing functions on vectors, so the article now defines its own vectors, but the example stayed.

And since that first technique did not work so well for defining optics with existentially quantified types, I also demonstrate a second independent technique that makes such optics possible.

But before we start looking at those workarounds, let's see why we can't write a lazy `vecFromList` without them.
As mentioned before, we currently have to choose between using a rank-2-type and wrapping the vector in a GADT.
We'll work out the second option, but first we need to enable some language extensions and import some stuff.
I also define my own `.` because the version from `linear-base` is not as polymorphic as I'd like it to be.

<details>
<summary>Imports and language extensions</summary>

-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
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
with-compiler: ghc-9.12.3

index-state: 2026-03-18T08:38:52Z

semaphore: True
-}

import Control.Functor.Linear (Monad (..))
import Control.Functor.Linear qualified as Control
import Control.Lens qualified as Lens
import Control.Monad.Except
import Control.Monad.State.Lazy qualified as NL
import Control.Optics.Linear
import Data.Bifunctor.Linear
import Data.Char
import Data.Functor qualified as NL
import Data.Functor.Identity
import Data.Functor.Linear
import Data.Kind
import Data.Maybe
import Data.PolyKinded hiding (Nat)
import Data.Profunctor.Kleisli.Linear
import Data.Type.Equality
import Data.Unrestricted.Linear
import Prelude.Linear hiding (Any, any, forget, fst, ($), (.))
import Prelude.Linear qualified as L hiding (Any, any)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Linear qualified as Unsafe
import Prelude (($))
import Prelude qualified as NL

-- Multiplicity polymorphic version of `(.)` which works in most non-linear code as well.
(.) :: forall b c a m n. (b %m -> c) %n -> (a %m -> b) %m -> a %m -> c
(.) f g x = f (g x)
infixr 9 .

forget :: (a %1 -> b) %m -> a -> b
forget f x = f x

(<&>) :: Functor f => f a %1 -> (a %1 -> b) -> f b
(<&>) = flip (<$>)

main = print $ demo2 @Int

{- [markdown]
</details>

The main thing to remember is that we use `L` and `NL` to disambiguate linear and non-linear functions, respectively, where needed.
Functions from `linear-base` are usually not qualified.

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
`SomeVec $ vecFromList as & \(SomeVec @n aVec) -> VCons a aVec` cannot be typed because the `n` tied to the unwrapped `SomeVec` would escape its scope.

The CPS-variant does not help for a similar reason: the continuation can't be applied before the recursive application of `vecFromList`.

As the author of the existential types proposal states for the `filter` function, it's not possible to define a lazy version in GHC's current type system.

*So we have to work around it.*

## Putting existentials on a leash

Essentially, we *have* to make the length of the vector visible in the return type of `vecFromList`.
GHC only offers universal quantification for such a type variable, but somehow, we need to make it impossible for the caller of `vecFromList` to choose a specific type for this variable, so `vecFromList` can make this choice.
To accomplish this, we start with a proxy type `Fresh` which can only be introduced with an existential type as parameter.

-}
data Fresh0 a = Fresh0 -- consider the constructor hidden

unpack0 :: (forall a. Fresh0 a -> r) -> r
unpack0 f = f Fresh0
{- [markdown]

This proxy will serve as a proof-witness that the associated type variable was "existentially quantified" elsewhere in the program.
The type of `vecFromList` becomes `forall n a. [a] -> Fresh n -> Vec n a` and the burden of the existential quantification is pushed outward to the caller.
This effectively enlarges the scope of the existential type to wherever the caller (or even its caller) decides to introduce the existential type using `unpack0`.
By passing the existential quantification witness as an argument to where it is eventually used, we create the leash from which this technique and article get their name.

Now, we need a way for `vecFromList` to choose a type for `n`.
Since it is a concrete type (instantiated at the call site), our only option is `unsafeCoerce`.

Putting the dangers of this approach aside for a moment, given a value of type `Fresh n`, we should allow `n` to be coerced to some other type `b`.
This can be accomplished by providing a type equality witness (from `Data.Type.Equality`).

We arrive at:
-}

newtype Fresh1 a = Fresh1 (forall b. a :~: b) -- consider the constructor hidden

unpack1 :: (forall a. Fresh1 a -> r) -> r
unpack1 f = f (Fresh1 $ unsafeCoerce Refl)
{- [markdown]

Using `Data.Type.Equality.castWith`, we can now perform unsafe coercions for any instance of `a` for which we have a `Fresh a`!
Now, we only need to remove the word "unsafe" from that sentence.

In order to make this safe, I believe it's sufficient to ensure such a coercion always targets the same type for each `Fresh`-value.
Until we use the witness, no values of type `a` can exist because it was existentially quantified.
Values of a type `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
So as long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

The first steps to this are (1) to hide the constructor `Fresh` and (2) to require that a `Fresh`-value is used linearly in the continuation passed to `unpack1`, like so:
-}

newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

type Exists a b = Fresh a %1 -> b -- conceptually this should be `forall a. Fresh a %1 -> b`, but that prevents `a` from being used in `b` and defeats the entire point.

unpack2 :: (forall a. Exists a r) %1 -> r
unpack2 f = f L.$ Fresh $ unsafeCoerce Refl

pack :: forall b r a. (a ~ b => r) %1 -> Exists a r
pack r (Fresh (Refl :: a :~: b)) = r
{- [markdown]
The `%1` in `type Exists a b = Fresh a %1 -> b` demands that the function is linear.
This means that the compiler will verify that such a function will consume the argument exactly once if the result of the function is consumed completely.
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
1. A `Fresh`-value can only be captured by a *linear* field (like `(Bool -> GADT a)` in `Wrapper`). Otherwise, the `Fresh`-value would not be consumed linearly.
2. A type that is `Dupable` can only contain a linear field when that field is also `Dupable`, but a function is not (even if it's input is `Bounded`, because finding the different outputs requires applying the function multiple times).
3. `Fresh` is also not `Dupable`, so because of 1. and 2. it can not occur in a `Dupable` value.

Therefore, it is safe to duplicate a `Dupable` value after it's produced by `unpack` and we arrive at the final version of `unpack`:
-}

unpack :: Dupable r => (forall a. Exists a r) %1 -> r
unpack f = f L.$ Fresh $ unsafeCoerce Refl

{- [markdown]
So is this completely safe now?
Well, only if `Dupable r` is a faithful instance of `Dupable`.
If you implement `dup` as `error "this is never used anyway"` for a linearly captured function, you'd get away with it, and you could still write the `conflict` expression from before.
We could have `unpack` call `dup` to verify this does not happen, but that would make it so strict that it becomes useless for implementing a lazy `vecFromList`.

Alternatively, we could define a closed type family `ClosedDupable` which uses a generic representation of a type (like `GHC.Generics.Rep`) to see if it contains a linear function field.
However, `Rep` currently cannot be defined for GADTs, so this would severely limit the values that can can escape `unpack`.
This can be solved by using [`RepK`](https://hackage.haskell.org/package/kind-generics-0.5.0.0/docs/Generics-Kind.html#t:RepK) from `kind-generics`, but the drawback there is that this requires users to derive `RepK` using template haskell or define it manually, and I am not convinced that's worth the extra safety.

Another alternative I've considered is to use the property of `Fresh`-values that the `a` in `Fresh a` is always existential.
We can prevent a GADT from capturing it by using a similar type family to inspect the generic representation as mentioned above.
This might be a good solution for when you do need to have a function as a linear field in `r`, but generally, I think it's a more stringent restriction than `Dupable`.

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
The manual `pack`ing and `unpack`ing adds significant verbosity, but I believe each use is necessary.
The `pack`s are needed because neither `VNil` nor `VCons` produce vectors of arbitrary length, and we can't remove the `unpack` because we can't use the same `Fresh`-value for coercing the `VCons`.

However, as you'll see in the next code block, we can abstract some of the verbosity away:
-}

repack :: forall f n a. Dupable a => (forall m. n ~ f m => Exists m a) %1 -> Exists n a
repack f n = unpack (\ @m m -> pack @(f m) (f m) n)

lazyVecFromList1 :: Dupable a => [a] %m -> Exists n (Vec n a)
lazyVecFromList1 [] = pack @Zero VNil
lazyVecFromList1 (a : as) = repack (VCons a . lazyVecFromList1 as)
{- [markdown]
I'm actually quite surprised the recursive case does not need any type arguments despite `f` only occurring in a constraint.

You might also have noticed that there is a multiplicity polymorphic arrow (`%m ->`) after `[a]` in the type annotation of `lazyVecFromList1`.
This means that the function can be used as either a linear or a non-linear one.
We could've used a linear arrow as well, but then we'd have to convert the function to a non-linear one when used in such a context.
That isn't hard, but it means extra boilerplate.

We should also test that this definition is actually lazy.
Sadly, this is a little more complicated than I hoped because the linear arrow in `Exists` demands that when the function is called with a linear `Fresh`-value (which is always, due to `unpack` being the only way of getting a `Fresh`), the produced vector is treated linearly as well until it escapes the scope of `unpack`.
It would be much nicer if we could have `lazyVecFromList0 :: [a] -> Exists n (Ur (Vec n a))`  (where `Ur` (for Unrestricted) is a simple non-linear wrapper for any value).
That's no problem for the `[]`-case, but it would mean that we have to pattern match on `Ur` in the recursive case, which in turn means the function always evaluates until the final `Ur` produced in the `[]`-case, which would make the function strict in the length of the list.

Anyway, here's the test:
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

Nothing special going on here. They just have to be written out manually because `Vec` and `SomeVec` are GADTs.
-}

instance Consumable a => Consumable (Vec n a) where
  consume VNil = ()
  consume (VCons x xs) = lseq x L.$ consume xs

instance Dupable a => Dupable (Vec n a) where
  dupR VNil = pure VNil
  dupR (VCons x xs) = VCons <$> dupR x <*> dupR xs

instance Consumable a => Consumable (SomeVec a) where
  consume (SomeVec v) = consume v

instance Dupable a => Dupable (SomeVec a) where
  dupR (SomeVec v) = SomeVec <$> dupR v

instance Consumable (Fresh a) where
  consume (Fresh Refl) = ()

deriving instance Show a => Show (Vec n a)
deriving instance Show a => Show (SomeVec a)
deriving instance Show a => Show (Ur a)

{- [markdown]
</details>

And thus we prove the laziness of `lazyVecFromList1`!

We do need `SomeVec` as a GADT wrapper to use it though, because otherwise the type variable from `Fresh` would escape its scope.
We also can't pattern match inside `unpack` because we have to discard the tail of the vector.
Inside `unpack` we'd have to do that linearly, which is possible to do with `consume` (from a superclass of `Dupable`), but that would break the test by evaluating the tail to normal form.

### Constraints on existential type variables

Aside from the `exists` quantifier, the existential types proposal also proposes a type level operator `(/\) :: Constraint -> Type -> Type` that puts constraints on a given type.
This operator gets some special treatment during type checking, but when `pack`/`unpacking` is explicit like in our implementation, it seems the current type checking algorithm already does quite well!
-}

data (/\) c a where
  SuchThat :: c => a %1 -> c /\ a

infix 3 `SuchThat`
type SuchThat a c = c /\ a

vecNonEmpty :: Vec n a %1 -> Exists m (Maybe (Vec n a `SuchThat` n ~ Succ m))
vecNonEmpty VNil = flip lseq Nothing
vecNonEmpty (VCons @_ @m x xs) = pack @m (Just L.$ SuchThat (VCons x xs))

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
-- Just (0,SomeVec (VCons 1 (VCons 2 (VCons 3 VNil))))
{- [markdown]
This demo is a bit contrived because I wanted to use the `n ~ Succ m` explicitly and linear types force the explicit duplication and consumption of values, but I think the point should be clear: no explicit type annotations outside those of functions signatures were needed to make GHC resolve all constraints correctly!

While that "inconvenience" of duping/consuming is by design, there are also still many unintentional difficulties with working with linear types:
  * Multiplicity inference is not enabled by default. This means that most existing Haskell code is unusable, even if the implementation of a function is actually linear.
  * The error messages don't say where a value is used non-linearly, only which variable.
  * Even if a function only captures `Consumable` or `Dupable` values in it's closure, it's not `Consumable` or `Dupable`.
  * Linear pattern synonyms are not supported yet.
  * All the other limitations mentioned in the [docs](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html#limitations).

So while this linear-existentiality-witness-techinique allows some things that are not possible with the existing existential-type-workarounds, I can't recommend using it outside of cases that are very limited in scope like `lazyVecFromList`.

Luckily, we can define a `lazyVecFromList` that hides all the linear-types complexity and falls back to GADT-wrapper workaround, while still being lazy:
-}

lazyVecFromList :: [a] -> SomeVec a
lazyVecFromList xs =
  unpack (SomeVec L.. lazyVecFromList1 (NL.fmap Ur xs))
    & \(SomeVec vec) -> SomeVec $ NL.fmap (forget unur) vec
{- [markdown]

## Invisible type preservation with linear functions

*I discovered the technique above almost 2 years ago.*

I put it on GitHub, but never mentioned it because I had not yet succeeded in my actual goal: to make a safe version of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.
The hard thing about this is that to enable it to change the types of the foci of the argument traversal (from `a` to `b`), we need to ensure that `[a]` and `[b]` have the same length.
Because I wanted the optic to be compatible with the existing `lens` ecosystem, a rank-2-type or GADT-wrapper wouldn't work.
I thought I could use the linear-existentiality-witness-technique, but when I tried it in `partsOf :: Functor f => Traversing (->) f s t a b -> Fresh n %1 -> LensLike f s t (Vec n a) (Vec n b)`, the fact that the resulting optic must be used linearly, makes it just as incompatible with `lens` as the rank-2-type version.

To be clear, if you unfold the `LensLike f s t (Vec n a) (Vec n b)` to `(Vec n a -> f (Vec n b)) -> s -> f t`, you could change it to `(forall n. Vec n a -> f (Vec n b)) -> s -> f t` (i.e. use a rank-2-type) and implement `partsOf` just fine, but this optic can't be used in functions like `traverseOf`, nor can it be pre-composed with other optics with `.` (because the `forall n` messes with type inference).

For a long time, I banged my head against the wall trying to think of a way to make a type-changing `partsOf` that would be compatible with the rest of `lens`, and so the project stayed on my list of things to get back to at some point.
It's somewhat regrettable that I didn't just publish the first part of this article anyway, but on the other hand, I found quite a few serious mistakes when I came back to it, so I'm also happy I caught those before publishing.

I now think making a safe type-changing `partsOf` that is compatible with all the functions from `lens` is impossible.
We could solve the precomposition issue by wrapping the `(forall n. Vec n a -> f (Vec n b))` in a wrapper that hides the `forall`, but it would still require its own `traverseOf` (and its own dedicated `lens` ecosystem).

The solution I will present in the rest of article has the same issue, but I think it's a better abstraction to build an alternative `lens` ecosystem around.
In fact, such an ecosystem already partly exists in the form of linear profunctors and linear optics.

First, we have to wrap the focus in a type like `data Some f = forall x. Some (f x)`.
Then, if a function `fun` that produces a `Some`-value, can only do so by returning a `Some`-value that it received as an argument, we can infer that the `x` inside the produced `Some` must be the same as the `x` in the received `Some`.
Written out in code, we would have `expose :: (Some f -> Some g) -> f x -> g x` defined as `expose f x = f (Some x) & \(Some y) -> unsafeCoerce y`, with some constraints on `(Some f -> Some g)` to ensure it has to return the value given as an argument.

Obviously, the `Some` constructor needs to be hidden, but we also need to prevent `Some`-values from being reused or swapped with `Some`-value with a different origin.
Making `fun` linear achieves this, but without any constructors for `Some` in scope, this also reduces the space of possible functions to the identity function.

Since it's not very interesting to apply optics to the identity function, there should at least be a function `mapSome :: (forall x. f x %1 -> g x) -> Some f %1 -> Some g`.
That still only allows `Setter` optics though.

For most optics we need something like `traverseSome :: Functor h => (forall x. f x %1 -> h (g x)) -> Some f %1 -> h (Some g)` (which we will call `hide` from now on).
This also requires adapting `expose`, changing its type to `(Some f %1 -> h (Some g)) -> f x -> h (g x)`
Without additional constraints, both `expose` and `hide` defined like this are unsafe:
* if `h` is chosen to be something like `Const (Some f)`, `expose` could let a `Some`-value escape and be used non-linearly. We could apply our previous trick and require that `h ()` is `Dupable`, but that would preclude using `StateT` and other functors which contain a function.
* if `h` and `g` are chosen to be something like `[]` and `Const ()`, respectively, `hide` could duplicate `Some`-values.

I think we can solve both issues by requiring that `h` is a linear control functor and an instance of a linear version of [`Alt`](https://hackage-content.haskell.org/package/semigroupoids-6.0.2/docs/Data-Functor-Alt.html)
-}

-- This "Functor" is the linear data Functor
class Functor f => Alt f where
  (<!>) :: Consumable a => f a %1 -> f a %1 -> f a

{- [markdown]
An `Alt` instance makes `expose` safe while a `Control.Functor` instance makes `hide` safe.
Let's focus on `Alt` and `expose` first.

Functors that store any non-`Consumable` data other than their element `a` cannot be an instance of `Alt` due to the "left catch" and "left distribution" laws (instances of `Alt` must satisfy at least one of the two):
* left catch: `pure a <!> b = pure a`
* left distribution regarding `<*>`: `(a <!> b) <*> c = (a <*> c) <!> (b <*> c)`

The reason that these laws exclude functors with non-`Consumable` data is simplest for the left catch law: `<!>` must be able to consume/discard any `b`.
Instances that satisfy the left distribution law must do the same because any data from `c` that is not consumed/discarded is duplicated on the right side of the `=`-sign.

Because of this, we can be sure that an `h` produced by `expose` does not contain any `Some`-values.
Thus, functors like `Const (Some f)` and `Either (Some f)` are forbidden while `Const e` and `Either e` with some `Consumable` `e` are still allowed.

Now let's look at `Control.Functor`.
If you don't know about linear control functors and the difference with linear data functors, I recommend reading [Arnaud's blogpost](https://www.tweag.io/blog/2020-01-16-data-vs-control/).
The gist is that linear control functors are required to use the function `f` that `fmap` is applied to exactly once.
This prevents duplication of `Some` values through functors like `[]`.
In theory, we could be a little more lenient here and say that the `fmap` only needs to use `f` *at most* once, but the linear instance of `Strong` for `Kleisli f` requires that `f` is a linear control functor anyway.

There is just one small thing to get out of the way before we go to the implementation of `hide` and `expose`: we don't want `Some` to work only for types of kind `k -> Type`.
We will use the kind-heterogeneous type-level lists from `kind-apply`, named [`LoT`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t:LoT) (for List of Types) and the operator [`:@@:`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t::-64--64-:) which applies a type constructor to a `LoT`.
-}

data Some f xs where
  Some :: forall x f xs. f x :@@: xs %1 -> Some f xs -- consider the constructor hidden

hide
  :: Control.Functor h
  => (forall x. f x :@@: xs %m -> h (g x :@@: ys)) %1 -> Some f xs %m -> h (Some g ys)
hide f (Some @x x) = Some @x <$> f @x x

expose
  :: forall x h f g xs ys
   . Alt h
  => (Some f xs %1 -> h (Some g ys)) -> f x :@@: xs %1 -> h (g x :@@: ys)
expose f x = f (Some @x x) <&> \(Some y) -> Unsafe.coerce y
{- [markdown]

<details>
<summary>Some example instances of `Alt` and `AffineFunctor` to check the most common functors admit an instance.</summary>

-}
instance Alt Identity where
  (<!>) = flip lseq

instance Consumable a => Consumable (Identity a) where
  consume (Identity a) = consume a

instance (Alt m, Consumable s) => Alt (NL.StateT s m) where
  NL.StateT f <!> NL.StateT g = NL.StateT L.$ \s -> f s <!> g s

instance Functor m => Functor (NL.StateT s m) where
  fmap f (NL.StateT t) = NL.StateT L.$ \s -> fmap (first f) L.$ t s

instance Consumable e => Alt (Either e) where
  Left e1 <!> Left e2 = lseq e2 L.$ Left e1
  Left e1 <!> r = lseq e1 r
  Right a <!> r = lseq r L.$ Right a

instance (Monad m, Alt m, Consumable e) => Alt (ExceptT e m) where
  ExceptT m <!> ExceptT n =
    ExceptT L.$ m >>= \case
      Right a -> Control.pure (Right a) <!> n -- have to consume n with <!> due to linearity. Using lseq is to restrictive.
      -- because of the case above, this instance only satisfies the left catch law when m satisfies the left catch law, and it only satisfies the left distribution law when m satisfies the left distribution law.
      -- In turn, the case below must satisfy both laws and can not mappend the e from m to another e from n, like the `Alt ExceptT` instance in semigroupoids does.
      Left e -> lseq e n
{- [markdown]

</details>

Now we can move on to the optics bit.
First, we'll finally have our type-changing safe `partsOf`:
-}

partsOf
  :: (Alt f, Control.Functor f)
  => Traversal s t a b
  -> Optic_ (Kleisli f) s t (Some Vec (LoT1 a)) (Some Vec (LoT1 b))
partsOf (Optical o) = Optical $ \(Kleisli f) -> Kleisli L.$ \s ->
  runBatching (expose f) L.$ runKleisli (o (Kleisli request)) s

-- Taken from the `batching` package: https://hackage.haskell.org/package/batching
data Batching req resp res where
  Batching :: KnownNat n => Vec n req %1 -> (Vec n resp %1 -> res) %1 -> Batching req resp res

runBatching :: Control.Functor f => (forall n. Vec n req %1 -> f (Vec n resp)) %1 -> Batching req resp res %1 -> f res
runBatching f (Batching reqs toRes) = toRes Control.<$> f reqs

request :: req %1 -> Batching req resp resp
request req = Batching (VCons req VNil) L.$ \resps ->
  let
    !(resp, VNil) = vecUncons resps
  in resp

moved :: Movable a => (a -> b) -> a %1 -> b
moved f = unur . lift f . move

vecToList :: Vec n a -> [a]
vecToList VNil = []
vecToList (VCons a as) = a : vecToList as

-- This replaces all the `Char`s in a `[Either Bool Char]` with a `String` consisting of all the `Char`s in the list.
demo1 :: [Either Bool String]
demo1 =
  runIdentity $
    traverseOf
      (partsOf (traversed .> _Right))
      (hide (moved $ \chars -> Identity $ NL.fmap (NL.const $ vecToList chars) chars))
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo1
-- [Left True,Right "hi",Left False,Right "hi"]
{- [markdown]
<details>
<summary>Required instances and helper functions</summary>

-}

data Dict :: Constraint -> Type where
  Dict :: c => Dict c

instance NL.Functor (Vec n) where
  fmap _ VNil = VNil
  fmap f (VCons a as) = VCons (f a) (NL.fmap f as)

instance Movable a => Movable (Vec n a) where
  move VNil = Ur VNil
  move (VCons a as) =
    let
      !(Ur a') = move a
      !(Ur as') = move as
    in Ur $ VCons a' as'

instance Functor (Batching req resp) where
  fmap = forget Control.fmap

instance Control.Functor (Batching req resp) where
  fmap f (Batching reqs toRes) = Batching reqs (f . toRes)

instance Applicative (Batching req resp) where
  pure = forget Control.pure
  (<*>) = (Control.<*>)

instance Control.Applicative (Batching req resp) where
  pure a = Batching VNil L.$ \VNil -> a
  Batching @n reqsf toResf <*> Batching @m reqsa toResa =
    case knownNatPlus @n @m of
      Dict ->
        Batching (append reqsf reqsa) L.$ \resps ->
          let
            !(respsf, respsa) = split resps
          in toResf respsf L.$ toResa respsa

type family Plus (x :: Nat) (y :: Nat) where
  Plus Zero x = x
  Plus (Succ x) y = Succ (Plus x y)

data SNat n where
  SZero :: SNat Zero
  SSucc :: KnownNat n => SNat (Succ n)

class KnownNat (n :: Nat) where
  natSing :: SNat n

instance KnownNat Zero where
  natSing = SZero

instance KnownNat n => KnownNat (Succ n) where
  natSing = SSucc

-- proof that when n and m are KnownNat, n `Plus` m is also KnownNat
knownNatPlus :: forall n m. (KnownNat n, KnownNat m) => Dict (KnownNat (n `Plus` m))
knownNatPlus = case natSing @n of
  SZero -> Dict
  SSucc @x -> case knownNatPlus @x @m of
    Dict -> Dict

append :: Vec n a %1 -> Vec m a %1 -> Vec (n `Plus` m) a
append VNil v = v
append (VCons a as) v = VCons a L.$ append as v

split :: forall n m a. KnownNat n => Vec (n `Plus` m) a %1 -> (Vec n a, Vec m a)
split v =
  case (natSing @n, v) of
    (SZero, w) -> (VNil, w)
    (SSucc @l, VCons a as) -> split @l as & \(as1, as2) -> (VCons a as1, as2)
{- [markdown]

</details>

I'll admit, the demo is a bit contrived again, but the point is that `partsOf` allows you to work over each element of a traversal with the context of all visited elements.

I should also note that the implementation of `Batching` and it's instances is much less efficient than it could be.
See [the implementation in the `batching` package](https://hackage.haskell.org/package/batching-0.1.0.0/docs/src/Control.Batching.html#Batching) for a more optimised version.

And I lied.
The type-changing `partsOf` was not my actual goal.
I need it for something I plan to write an article about later™.
(Spoiler: it's more fancy optics).

Now let's see how we can use the version of `partsOf` with non-linear optics.
-}

vecHead :: Traversal' (Vec n a) a
vecHead = traversal $ \f v -> case v of
  VNil -> pure VNil
  VCons a as -> flip VCons as Control.<$> f a

runBatchingNonLinear :: NL.Functor f => (forall n. Vec n req -> f (Vec n resp)) -> Batching req resp res -> f res
runBatchingNonLinear f (Batching as toRes) = forget toRes NL.<$> f as

traversalForget
  :: NL.Applicative f => Optic_ (Kleisli (Batching a b)) s t a b -> Lens.LensLike f s t a b
traversalForget (Optical o) f s = runBatchingNonLinear (NL.traverse f) (runKleisli (o $ Kleisli request) s)

hidden
  :: forall f s t xs ys a b
   . Control.Functor f
  => (forall x. Optic_ (Kleisli f) (s x :@@: xs) (t x :@@: ys) a b)
  -> Optic_ (Kleisli f) (Some s xs) (Some t ys) a b
hidden o = Optical L.$ \(Kleisli f) -> Kleisli L.$ hide (\ @n -> traverseOf (o @n) f)

demo2 :: Consumable e => Except e [Either Bool String]
demo2 =
  Lens.traverseOf
    (traversalForget (partsOf (traversed .> _Right) .> hidden vecHead))
    (NL.pure . NL.map toUpper)
    [Left True, Right "hi", Left False, Right "hi"]

-- >>> demo2
-- ExceptT (Identity (Right [Left True,Right "HI",Left False,Right "hi"]))

-- notice how the first "hi" at the end is now capitalized
{- [markdown]
<details>
<summary>Required instances and helper functions</summary>

-}

class Any a where
  any :: a

instance Any [a] where
  any = []

instance (Consumable a, Any b) => Alt (Batching a b) where
  l <!> Batching a bt = lseq a L.$ lseq (bt L.$ vecReplicate any) l

instance NL.Foldable (Vec n) where
  foldMap _ VNil = NL.mempty
  foldMap f (VCons a as) = f a NL.<> NL.foldMap f as

instance NL.Traversable (Vec n) where
  traverse _ VNil = NL.pure VNil
  traverse f (VCons a as) = NL.liftA2 VCons (f a) (NL.traverse f as)

vecReplicate :: forall n a. KnownNat n => a -> Vec n a
vecReplicate a = case natSing @n of
  SZero -> VNil
  SSucc -> VCons a L.$ vecReplicate a
{- [markdown]

</details>

The demo shows we can convert linear traversals to non-linear ones using `traversalForget` under some constraints incurred through the use of `Batching`.
Notably, no linear constraints from the linear optic are carried over.

However, a limitation remains in that we are required to focus on some part of the `Some` focus of `partsOf` before we can escape the linear realm, because the `Alt` instance for `Batching a b` required `a` to be `Consumable`, which `Some` is explicitly not.

## Wrapping up

The purpose of this article is to put these ideas out there and see if someone sees any safety issues that I have overlooked.
Additionally, I think it would be interesting to hear the perspective from someone with a more theoretical background than me.
Is there a theoretical connection between linear types and existential types?
Is there a kind of quantification that would allow the length-indices now hidden in `Some` in optics to be exposed in a type like `Lens.LensLike`?

As I mentioned in the introduction, you can play with the code in your browser using a [GitHub Codespace](https://codespaces.new/cdfa/existentials-on-a-leash?quickstart=1).
If you find something, please create an issue [on GitHub](https://github.com/cdfa/existentials-on-a-leash/issues).

If no serious issues are found after a few weeks, I'll publish a small library containing the core types and functions on Hackage.
In the meantime, I'll continue working on the other optics I needed these techniques for.

Thanks for reading and have fun experimenting!

~cdfa
-}

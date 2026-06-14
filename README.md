
# Existentials on a leash

In this article, I will share a new workaround for the lack of existential quantification in Haskell.
Specifically, I will show the implementation of an `Exists` quantifier that allows existential type variables to appear "naked" (without CPS-style/GADT wrapping) in types.
The quantifier is implemented as a type synonym for functions that linearly consume a proof-token that ensures proper treatment of existentially typed values.

Additionally, I share an independent technique that ensures functions instantiate existential types in their result with the same type as its input type is instantiated, i.e. they preserve the instantiation of hidden type variables.
This technique also relies on linear types, but not the existential quantifier mentioned before.
I will demonstrate this technique by implementing a safe variant of the [`unsafePartsOf`](https://hackage-content.haskell.org/package/lens-5.3.6/docs/Control-Lens-Combinators.html#v:unsafePartsOf)`:: Functor f => Traversing (->) f s t a b -> LensLike f s t [a] [b]` optic combinator.

Both techniques use `unsafeCoerce`.
I explain why I believe the coercions are safe, but I haven't proven anything formally.
Please try to break this stuff if you see some hole I have missed.

While I will briefly explain what existential types and linear types are, this article is not meant as a general introduction to these language features.
Familiarity with GADTs, linear types and optics (for the sections pertaining to those) is recommended.

That being said, I made it as easy as I can for the reader to tinker with the code and interactively learn about these concepts by providing a [GitHub Codespace](https://codespaces.new/cdfa/existentials-on-a-leash?quickstart=1) prebuild (hint: use "Preview embedded markdown" to see the .hs file with its markdown version to the side).
Clicking that link will allow you to tinker with the code with the support of the Haskell Language Server from a Visual Studio Code instance running in your browser (or from a container on your computer).
It might even be a nice way to read the article because you can hover over variables and functions to see their types for example.

## Current limitations of existential types

As of GHC 9.14, GHC only supports 2 ways of "existentially quantifying" type variables:
1. With a rank-2 type: `(forall a. a -> r) -> r`. This corresponds to `exists a. (a -> r) -> r`.
2. Using a GADT: `data Wrapper where Wrapper :: forall a. a -> Wrapper`. When pattern matching on `Wrapper`, `a` will be existentially quantified.

Both these techniques do not actually use existential quantification, but instead encode it through negated universal quantification.
Wrapping and unwrapping existential types using these techniques is not just cumbersome, but they're also insufficient for defining optics with existentially quantified foci, such as prisms for constructors of GADTs with existentially quantified fields.

[A proposal](https://github.com/goldfirere/ghc-proposals/blob/existentials/proposals/0473-existentials.rst) for adding first-class existential types to GHC was written a while ago, but the author seems to be prioritizing other work.
The proposal also shows a simple example of a function that is impossible to write using the current workarounds: a lazy `filter :: (a -> Bool) -> Vec n a -> exists m. Vec m a`.

This article introduces 2 new (as far as I am aware) techniques.
The first can be used to implement some of the motivating examples from the proposal.
However, instead a lazy `filter`, I demonstrate the capability for functions to lazily produce an existentially indexed type by defining a function `lazyVecFromList :: [a] -> Exists m (Vec m a)`.
My initial reason for this was that when I started this project, I was using vectors from an external package which did not export its constructors, and to test a lazy `filter` I also needed a lazy way to create vectors.
I didn't end up needing so many existing functions on vectors, so the article now defines its own vectors, but the example stayed.

And since that first technique did not work so well for defining optics with existentially quantified types, I also demonstrate a second independent technique that makes such optics possible.

But before we start looking at those workarounds, let's see why they are needed for a lazy `vecFromList`.
As mentioned before, we currently have to choose between using a rank-2-type and wrapping the vector in a GADT.
We'll work out the second option, but first we need to enable some language extensions and import some stuff.
I also define my own `.` because the version from `linear-base` is not as polymorphic as I'd like it to be.

<details>
<summary>Imports and language extensions</summary>


``` haskell
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

import Control.Functor.Linear (Monad (..), StateT (..))
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
import Data.Tuple qualified as NL
import Data.Type.Equality
import Data.Unrestricted.Linear
import Prelude.Linear hiding (forget, fst, ($), (.))
import Prelude.Linear qualified as L
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

```

</details>

The main thing to remember is that we use `L` and `NL` to disambiguate linear and non-linear functions, respectively, where needed.
Functions from `linear-base` are usually not qualified.

Now we can define our vectors and `vecFromList`:


``` haskell
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
```

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


``` haskell
data Fresh0 a = Fresh0

unpack0 :: (forall a. Fresh0 a -> r) -> r
unpack0 f = f Fresh0
```


This proxy will serve as a proof-witness that the associated type variable was "existentially quantified" elsewhere in the program.
The type of `vecFromList` becomes `forall n a. [a] -> Fresh n -> Vec n a` and the burden of the existential quantification is pushed outward to the caller.
This effectively enlarges the scope of the existential type to wherever the caller (or even its caller) decides to introduce the existential type using `unpack0`.
By passing the existential quantification witness as an argument to where it is eventually used, we create the leash from which this technique and article get their name.

Now, we need a way for `vecFromList` to choose a type for `n`.
Since it is a concrete type (instantiated at the call site), our only option is `unsafeCoerce`.

Putting the dangers of this approach aside for a moment, given a value of type `Fresh n`, we should allow `n` to be coerced to some other type `b`.
This can be accomplished by providing a type equality witness (from `Data.Type.Equality`).

We arrive at:


``` haskell
newtype Fresh1 a = Fresh1 (forall b. a :~: b)

unpack1 :: (forall a. Fresh1 a -> r) -> r
unpack1 f = f (Fresh1 $ unsafeCoerce Refl)
```


Using `Data.Type.Equality.castWith`, we can now perform unsafe coercions for any instance of `a` for which we have a `Fresh a`!
Now, we only need to remove the word "unsafe" from that sentence.

In order to make this safe, I believe it's sufficient to ensure such a coercion always targets the same type for each `Fresh`-value.
Until we use the witness, no values of type `a` can exist because it was existentially quantified.
Values of a type `f` parameterized by `a` can exist, but such values must be independent of `a` for the same reason.
So as long as there only ever exists one `a ~ b`, it should then be safe to substitute `a` for the `b` which is chosen.

The first steps to this are (1) to hide the constructor `Fresh` and (2) to require that a `Fresh`-value is used linearly in the continuation passed to `unpack1`, like so:


``` haskell
newtype Fresh a = Fresh (forall b. a :~: b) -- consider the constructor hidden

type Exists a b = Fresh a %1 -> b -- conceptually this should be `forall a. Fresh a %1 -> b`, but that prevents `a` from being used in `b` and defeats the entire point.

unpack2 :: (forall a. Exists a r) %1 -> r
unpack2 f = f L.$ Fresh $ unsafeCoerce Refl

pack :: forall b r a. (a ~ b => r) %1 -> Exists a r
pack r (Fresh (Refl :: a :~: b)) = r
```

The `%1` in `type Exists a b = Fresh a %1 -> b` demands that the function is linear.
This means that the compiler will verify that such a function will consume the argument exactly once if the result of the function is consumed completely.
These annotations can also be used in the types for GADT constructors (like `VCons`).
In that case, the values in those fields must be used linearly when you pattern match on that constructor in a linear function.

The function `pack` is needed to replace `Data.Type.Equality.castWith` since the user can't get the `a :~: b` from pattern matching on a `Fresh`-value anymore.

However, this is not sufficient to ensure a `pack`-coercion always targets the same type for each `Fresh`-value.
The following example shows how this can be used to generate incorrect type equalities.


``` haskell
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

```


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


``` haskell
unpack :: Dupable r => (forall a. Exists a r) %1 -> r
unpack f = f L.$ Fresh $ unsafeCoerce Refl

```

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


``` haskell
lazyVecFromList0 :: Dupable a => [a] %m -> Exists n (Vec n a)
lazyVecFromList0 [] n = pack @Zero VNil n
lazyVecFromList0 (a : as) n =
  -- This `unpack` actually unpacks the `Vec` produced by the recursive call, not the one `pack`ed immediately below
  unpack
    -- TypeAbstractions syntax
    ( \ @predN predN ->
        pack @(Succ predN) (VCons a L.$ lazyVecFromList0 as predN) n
    )

```

The manual `pack`ing and `unpack`ing adds significant verbosity, but I believe each use is necessary.
The `pack`s are needed because neither `VNil` nor `VCons` produce vectors of arbitrary length, and we can't remove the `unpack` because we can't use the same `Fresh`-value for coercing the `VCons`.

However, as you'll see in the next code block, we can abstract some of the verbosity away:


``` haskell
repack :: forall f n a. Dupable a => (forall m. n ~ f m => Exists m a) %1 -> Exists n a
repack f n = unpack (\ @m m -> pack @(f m) (f m) n)

lazyVecFromList1 :: Dupable a => [a] %m -> Exists n (Vec n a)
lazyVecFromList1 [] = pack @Zero VNil
lazyVecFromList1 (a : as) = repack (VCons a . lazyVecFromList1 as)
```

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


``` haskell
lazyVecFromListIsLazy :: Maybe Int
lazyVecFromListIsLazy =
  unpack (SomeVec . lazyVecFromList1 (0 : error "second element evaluated")) & \case
    (SomeVec (VCons a _)) -> Just a
    _ -> Nothing

-- >>> lazyVecFromListIsLazy
-- Just 0
```


<details>
<summary>Required Consumable/Dupable instances</summary>

Nothing special going on here. They just have to be written out manually because `Vec` and `SomeVec` are GADTs.


``` haskell
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

```

</details>

And thus we prove the laziness of `lazyVecFromList1`!

We do need `SomeVec` as a GADT wrapper to use it though, because otherwise the type variable from `Fresh` would escape its scope.
We also can't pattern match inside `unpack` because we have to discard the tail of the vector.
Inside `unpack` we'd have to do that linearly, which is possible to do with `consume` (from a superclass of `Dupable`), but that would break the test by evaluating the tail to normal form.

### Constraints on existential type variables

Aside from the `exists` quantifier, the existential types proposal also proposes a type level operator `(/\) :: Constraint -> Type -> Type` that puts constraints on a given type.
This operator gets some special treatment during type checking, but when `pack`/`unpacking` is explicit like in our implementation, it seems the current type checking algorithm already does quite well!


``` haskell
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
```

This demo is a bit contrived because I wanted to use the `n ~ Succ m` explicitly and linear types force the explicit duplication and consumption of values, but I think the point should be clear: no explicit type annotations outside those of functions signatures were needed to make GHC resolve all constraints correctly!

While that "inconvenience" of duping/consuming is by design, there are also still many unintentional difficulties with working with linear types:
  * Multiplicity inference is not enabled by default. This means that most existing Haskell code is unusable, even if the implementation of a function is actually linear.
  * The error messages don't say where a value is used non-linearly, only which variable.
  * Even if a function only captures `Consumable` or `Dupable` values in it's closure, it's not `Consumable` or `Dupable`.
  * Linear pattern synonyms are not supported yet.
  * All the other limitations mentioned in the [docs](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/linear_types.html#limitations).

So while this linear-existentiality-witness-techinique allows some things that are not possible with the existing existential-type-workarounds, I can't recommend using it outside of cases that are very limited in scope like `lazyVecFromList`.

Luckily, we can define a `lazyVecFromList` that hides all the linear-types complexity and falls back to GADT-wrapper workaround, while still being lazy:


``` haskell
lazyVecFromList :: [a] -> SomeVec a
lazyVecFromList xs =
  unpack (SomeVec L.. lazyVecFromList1 (NL.fmap Ur xs))
    & \(SomeVec vec) -> SomeVec $ NL.fmap (forget unur) vec
```


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
* if `h` and `g` are chosen to be something like `[]` and `Const ()`, `hide` could duplicate `Some`-values.

We can solve both problems by requiring that `h` is a linear control functor, i.e. it admits a function `fmap :: (a %1 -> b) %1 -> h a %1 -> h b`.
If you don't know about linear control functors and the difference with linear data functors, I recommend reading [Arnaud's blogpost](https://www.tweag.io/blog/2020-01-16-data-vs-control/).
What's important here is that linear control functors always contain exactly one element `a` (because the linearity of the second arrow in `fmap`).
Because of this, we can be sure that a `h (g x)` produced by `expose` does not contain any `Some`-values (if Haskell were strict, but we'll get to that) and the `h (g x)` in `hide` contains just one `g x`.

But this is also very restrictive.
It forbids functors like `Either e`, because `Left` does not contain an `a`.

I think the solution that fits most use cases is to require that `h` is either a linear control functor or an instance of both a linear version of [`Alt`](https://hackage-content.haskell.org/package/semigroupoids-6.0.2/docs/Data-Functor-Alt.html) and an "affine" functor:


``` haskell
-- This "Functor" is the linear data Functor
class Functor f => Alt f where
  (<!>) :: Consumable a => f a %1 -> f a %1 -> f a

data Affine a where
  Affine :: a -> Affine a -- explicit non-linear constructor. Consider the constructor hidden

instance Consumable (Affine a) where
  consume (Affine _) = ()

affine :: a -> Affine a
affine = Affine

runAffine :: Affine a %1 -> a
runAffine (Affine a) = a

liftAffine :: (a -> b) -> Affine a %1 -> Affine b
liftAffine f (Affine a) = Affine L.$ f a

class Functor f => AffineFunctor f where
  afmap :: Affine (a %1 -> b) %1 -> f a %1 -> f b

```

`Alt` makes `expose` safe while `AffineFunctor` makes `hide` safe.
Let's focus on `Alt` and `expose` first.

Functors that store any non-`Consumable` data other than their element `a` cannot be an instance of `Alt` due to the "left catch" and "left distribution" laws (instances of `Alt` must satisfy at least one of the two):
* left catch: `pure a <!> b = pure a`
* left distribution regarding `<*>`: `(a <!> b) <*> c = (a <*> c) <!> (b <*> c)`

The reason that these laws exclude functors with non-`Consumable` data is simplest for the left catch law: `<!>` must be able to consume/discard any `b`.
Instances that satisfy the left distribution law must do the same because any data from `c` that is not consumed/discarded is duplicated on the right side of the `=`-sign.

Because of this, we can be sure that an `h` produced by `expose` does not contain any `Some`-values.
Thus, functors like `Const (Some f)` and `Either (Some f)` are forbidden while `Const e` and `Either e` with some `Consumable` `e` are still allowed.

Now let's look at `AffineFunctor`.
It's similar to a linear control functor in that the mapping function (wrapped in `Affine`) needs to be consumed linearly.
However, the `Affine` wrapper actually stores the function in a non-linear field, which allows `Affine a` to be `Consumable` without needing `Consumable a`.
Thus, instances of `AffineFunctor` must use the mapping function *at most* once, instead of *exactly once*.
This provides the same safety guarantee for `hide` that `Control.Functor` would have.
`Affine` is also equivalent to `Ur` except that `Dupable` should never be implemented for it.

There is just one small thing to get out of the way before we go to the implementation of `hide` and `expose`: we don't want `Some` to work only for types of kind `k -> Type`.
We will use the kind-heterogeneous type-level lists from `kind-apply`, named [`LoT`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t:LoT) (for List of Types) and the operator [`:@@:`](https://hackage-content.haskell.org/package/kind-apply-0.4.0.1/docs/Data-PolyKinded.html#t::-64--64-:) which applies a type constructor to a `LoT`.

We'll start with an `Alt`/`AffineFunctor`-based definitions of `hide` and `expose` and extend them to allow linear control functors as alternative later.


``` haskell
data Some f xs where
  Some :: forall x f xs. f x :@@: xs %1 -> Some f xs -- consider the constructor hidden

hideAffineFunctor
  :: AffineFunctor h
  => (forall x. f x :@@: xs %m -> h (g x :@@: ys)) %1 -> Some f xs %m -> h (Some g ys)
hideAffineFunctor f (Some @x x) = Some @x <$> f @x x

exposeAlt
  :: forall x h f g xs ys
   . Alt h
  => (Some f xs %1 -> h (Some g ys)) -> f x :@@: xs %1 -> h (g x :@@: ys)
exposeAlt f x = f (Some @x x) <&> \(Some y) -> Unsafe.coerce y
```


<details>
<summary>Some example instances of `Alt` and `AffineFunctor` to check the most common functors admit an instance.</summary>


``` haskell
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

instance AffineFunctor Identity where
  afmap f (Identity a) = Identity L.$ runAffine f a

instance AffineFunctor m => AffineFunctor (NL.StateT s m) where
  afmap f (NL.StateT t) = NL.StateT L.$ \s -> afmap (liftAffine first f) L.$ t s

instance AffineFunctor (Either e) where
  afmap f (Left e) = lseq f L.$ Left e
  afmap f (Right a) = Right L.$ runAffine f a

instance AffineFunctor m => AffineFunctor (ExceptT e m) where
  afmap f (ExceptT m) = ExceptT L.$ afmap (liftAffine fmap f) m
```


</details>

Now let's consider a version of `expose` that uses linear control functors instead of `Alt`.
Like I said before, these only guarantee that a `h (g x)` produced by `expose` does not contain any `Some`-values if Haskell were strict.
Let me show why.


``` haskell
exposeControlFunctor
  :: forall x h f g xs ys
   . Control.Functor h
  => (Some f xs %1 -> h (Some g ys)) %1 -> f x :@@: xs %1 -> h (g x :@@: ys)
exposeControlFunctor f x = f (Some @x x) <&> \(Some y) -> Unsafe.coerce y

-- very specific simple Show instance for the purpose of this example
instance Show a => Show (Some Vec (LoT1 a)) where
  show (Some x) = "Some (" <> show x <> ")"

problem =
  NL.fst $
    exposeControlFunctor @_ @((,) (Some Vec (LoT1 Int)))
      (\s -> (s, error "The consequences of my actions"))
      VNil

-- >>> problem
-- Some (VNil)
```

We have successfully ignored the consequences of our actions and obtained an unrestricted `Some`-value!
That could be abused to cause all sorts of mayhem in other uses of `preserving0`.

As mentioned before, the problem lies with strictness, or rather laziness.
The caller of `exposeControlFunctor` can always choose not to evaluate the `Some` in the right side of the tuple, and thus the `Some` in the left side can escape.
It's not enough to call `deepseq` on the produced `h (Some g ys)` because if we take `State s` as `h` for example, `deepseq` would not ensure `Some g ys` is evaluated to weak-head-normal-form before the tuple in the definition of `State` is created (and the `NFData` instance for `a -> b` has been deprecated for a while anyway).
Moreover, we don't want to force the entire `h (Some g ys)`-value.

We need an `fmap` that allows evaluating a part of the `a` in `f a` to weak-head-normal-form "as eagerly as possible".
It must be "a part of `a`", because if we implement this for `StateT s m`, we need to recursively apply the function to `m (a, s)`, and we want to evaluate a part of that `a`, not `m`'s "element" (the tuple `(a, s)`).

We'll accomplish this with a new class called `SeqElement` (name is subject to change):


``` haskell
class Control.Functor f => SeqElement f where
  mapAndSeq :: Consumable c => (a %1 -> (b, c)) %1 -> f a %1 -> f b
```

Let't check that we can define instances for `SeqElement` for some common functors.


``` haskell
instance SeqElement Identity where
  mapAndSeq extract (Identity a) = extract a & \(b, c) -> lseq c L.$ Identity b

instance SeqElement m => SeqElement (StateT s m) where
  mapAndSeq extract (StateT f) = StateT L.$ \s -> mapAndSeq extract' L.$ f s
   where
    extract' (a, s) = extract a & \(b, c) -> ((b, s), c)

instance SeqElement ((,) a) where
  mapAndSeq extract (a, b) = extract b & \(d, c) -> lseq c (a, d)
```

So far, so good!
Now let's check that this solves our `problem`.


``` haskell
hideSeqElement
  :: SeqElement h
  => (forall x. f x :@@: xs %m -> h (g x :@@: ys)) %1 -> Some f xs %m -> h (Some g ys)
hideSeqElement f (Some @x x) = Some @x <$> f @x x

seqAndMap :: (SeqElement f, Consumable c) => f a %1 -> (a %1 -> (b, c)) %1 -> f b
seqAndMap = flip mapAndSeq

exposeSeqElement
  :: forall x h f g xs ys
   . SeqElement h
  => (Some f xs %1 -> h (Some g ys)) %1 -> f x :@@: xs %1 -> h (g x :@@: ys)
exposeSeqElement f x = f (Some @x x) `seqAndMap` \(Some y) -> (Unsafe.coerce y, ())

problemSolved =
  NL.fst $
    exposeSeqElement @_ @((,) (Some Vec (LoT1 Int)))
      (\s -> (s, error "The consequences of my actions"))
      VNil

-- >>> problemSolved
-- The consequences of my actions
```

Calling a problem "solved" when your function returns an `error` instead of a proper value feels odd, but that's what you get when working with unsafe primitives.

Now we need to combine `exposeAlt` with `exposeSeqElement` and `hideAlt` with `hideSeqElement`.
We'll define a class `Capturing` that requires a functor to be either an instance of `SeqElement` or both `Alt` and `AffineFunctor`.


``` haskell
data Dict :: Constraint -> Type where
  Dict :: c => Dict c

class Functor f => Capturing f where
  seqElementOrAltAffine :: Either (Dict (SeqElement f)) (Dict (Alt f, AffineFunctor f))

instance Capturing Identity where
  seqElementOrAltAffine = Right Dict -- we pick the Alt option, because expose will use fmap instead of mapAndSeq and fmap is more efficient

instance SeqElement m => Capturing (Control.StateT s m) where
  seqElementOrAltAffine = Left Dict -- Control.StateT is also Alt, but that requires a Consumable s, so the SeqElement option is less stringent

instance Capturing ((,) a) where
  seqElementOrAltAffine = Left Dict

instance
  ( Monad m
  , Alt m
  , AffineFunctor m
  , Consumable e
  )
  => Capturing (ExceptT e m)
  where
  seqElementOrAltAffine = Right Dict

hide
  :: forall h f g xs ys m
   . Capturing h
  => (forall x. f x :@@: xs %m -> h (g x :@@: ys)) %1 -> Some f xs %m -> h (Some g ys)
hide f (Some @x x) = Some @x <$> f @x x

expose
  :: forall x h f g xs ys
   . Capturing h
  => (Some f xs %1 -> h (Some g ys)) -> f x :@@: xs %1 -> h (g x :@@: ys)
expose f x = case seqElementOrAltAffine @h of
  Left Dict -> f (Some @x x) `seqAndMap` \(Some y) -> (Unsafe.coerce y, Just ())
  Right Dict -> f (Some @x x) <&> \(Some y) -> Unsafe.coerce y
```


Now we can move on to the optics bit.
I found out way too late that linear lenses (or rather the linear `Strong` instance for the `Kleisli` profunctor) require that in `f` in `Kleisli f a b` is a linear *control* functor, so in the linear optics world, you can't use the `Alt` + `AffineFunctor` path anyway.
It's still useful for non-linear optics though, which we'll get back to later.

First, we'll finally have our type-changing safe `partsOf`:


``` haskell
partsOf
  :: SeqElement f
  => Traversal s t a b
  -> Optic_ (Kleisli f) s t (Some Vec (LoT1 a)) (Some Vec (LoT1 b))
partsOf (Optical o) = Optical $ \(Kleisli f) -> Kleisli L.$ \s ->
  runBatching (exposeSeqElement f) L.$ runKleisli (o (Kleisli request)) s

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
```

<details>
<summary>Required instances and helper functions</summary>



``` haskell
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
```


</details>

I'll admit, the demo is a bit contrived again, but the point is that `partsOf` allows you to work over each element of a traversal with the context of all visited elements.

I should also note that the implementation of `Batching` and it's instances is much less efficient than it could be.
See [the implementation in the `batching` package](https://hackage.haskell.org/package/batching-0.1.0.0/docs/src/Control.Batching.html#Batching) for a more optimised version.

And I lied.
The type-changing `partsOf` was not my actual goal.
I need it for something I plan to write an article about later™.
(Spoiler: it's more fancy optics).

Now let's see how we can use the version of `partsOf` with non-linear optics.


``` haskell
type instance Lens.Index (Vec n a) = Int
type instance Lens.IxValue (Vec n a) = a

instance Lens.Ixed (Vec n a) where
  ix 0 f (VCons a as) = flip VCons as NL.<$> f a
  ix i f (VCons a as) = VCons a NL.<$> Lens.ix (pred i) f as
  ix _ _ VNil = error "a proper `ix` for vectors would use some integral type with a type-level upper bound for the first argument"

-- Linear version of Lens.Context
data Context a b t = Context a (b %1 -> t)

instance Functor (Context a b) where
  fmap = forget Control.fmap

instance Control.Functor (Context a b) where
  fmap f (Context a bt) = Context a (f . bt)

instance SeqElement (Context a b) where
  mapAndSeq f (Context a bt) = Context a L.$ uncurry (flip lseq) . f . bt

-- Also from lens
sell :: a %1 -> Context a b b
sell a = Context a id

runContext :: NL.Functor f => (a -> f b) -> Context a b t -> f t
runContext f (Context a bt) = forget bt NL.<$> f a

seqElementLensForget :: (forall f. SeqElement f => Optic_ (Kleisli f) s t a b) -> Lens.Lens s t a b
seqElementLensForget (Optical o) f s = runContext f (runKleisli (o $ Kleisli sell) s)

hidden
  :: forall f s t xs ys a b
   . Capturing f
  => (forall x. (a -> f b) -> s x :@@: xs -> f (t x :@@: ys))
  -> Lens.LensLike f (Some s xs) (Some t ys) a b
hidden o f = hide (\ @n -> o @n f)

demo2 :: Consumable e => Except e [Either Bool Char]
demo2 =
    Lens.traverseOf
      (seqElementLensForget (partsOf (traversed .> _Right)) . hidden (Lens.ix 1))
      (NL.pure . toUpper)
      [Left True, Right 'h', Left False, Right 'i']

-- >>> demo2
-- ExceptT (Identity (Right [Left True,Right 'h',Left False,Right 'I']))
-- notice how the "i" at the end is now capitalized
```

As shown above we can run standard optics like `Lens.ix` on `Some` foci using the `hidden` combinator.
And while the example does not show it, you can see from the type of `hidden` that we could precompose it with standard optics (like `hidden (...) . standardOptic`) because it produces a normal `LensLike`.

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

\# Test

<details>
<summary>Pragma's and imports</summary>

\begin{code}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wall -Wno-missing-signatures #-}
-- These are only used for the examples, not required to use this trick in general
{-# OPTIONS_GHC -fplugin Data.Type.Natural.Presburger.MinMaxSolver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import Prelude hiding (filter)
import Unsafe.Coerce (unsafeCoerce)
import Control.Lens as Lens
import Data.Sized as Sized
import GHC.TypeNats
--import Data.Type.Natural
import Data.Kind
import Control.Subcategory
import Data.Type.Equality hiding (gcastWith)

\end{code}

</details>

\begin{code}

newtype Fresh a = Fresh (forall b. a :~: b)

withFresh :: (forall a. Fresh a %1 -> r) %1 -> r
withFresh f = f (Fresh $ unsafeCoerce Refl)

\end{code}

`Fresh` is a proxy for a fresh type variable `a`.
This is guaranteed by having `withFresh` be the only way to introduce this type (the constructor `Fresh` should not be exported), where `a` is existentially quantified.

Until `a` is bound to a type with `bindFresh`, no values of type `a` can exist because nothing is known about `a`.
Types `f` that are parameterized by `a` can have values, but such values must be independent of `a` because `a` is existentially quantified.
Therefore, it is safe to substitute an arbitrary type `b` for `a`, which `bindFresh` and `innerCoerce` allow you to do.

However, you can do this only once.
If `a` is bound multiple times, it may lead to type conflicts:

```haskell
conflict = withFresh $ \(fresh :: Fresh a) ->
  let
    intEqualsA = sym fresh :: Int :~: a
    aEqualsChar = fresh :: a :~: Char
    Refl = trans intEqualsA aEqualsChar :: Int :~: Char
  in error "Int /= Char"
```

To prevent this, we only allow using the `Fresh`-token once using a linear arrow in `withFresh`.

This delayed binding of a type variable allows us to have "naked" existentially quantified types within the context of a function passed to `withFresh`.

For example, we can write a lazy `filter` for length-indexed vectors:

\begin{code}

-- | Linear version of Type.Equality.gcastWith
gcastWith :: (a :~: b) %1 -> ((a ~ b) => r) %1 -> r
gcastWith Refl x = x

data Nat' = Zero | Succ Nat'

type Vec :: Nat' -> Type -> Type
data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

filter :: forall fresh a n. Fresh fresh %1 -> (a -> Bool) -> Vec n a -> Vec fresh a
filter (Fresh fresh) p vec =
  case vec of
    VNil -> gcastWith (fresh @Zero) VNil
    VCons x xs | p x ->
      withFresh
        (\(freshPredN :: Fresh predN) ->
          gcastWith
            (fresh @(Succ predN))
            (VCons x (filter freshPredN p xs)))
    VCons _ xs ->
      withFresh
        (\(freshNMinus1 :: Fresh n') ->
          gcastWith (fresh @n') (filter freshNMinus1 p xs))

unsafeTestVec :: Vec (Succ (Succ n)) Int
unsafeTestVec = VCons 0 $ VCons 1 undefined

tryHead :: Vec n a %1 -> Maybe a
tryHead VNil = Nothing
tryHead (VCons x _) = Just x 

filterIsLazy = withFresh (\fresh -> tryHead (filter fresh (> 0) unsafeTestVec))

\end{code}

> -- >>> filterIsLazy
> -- Just 1

% \begin{code}

% data Batching s a b r = forall n. KnownNat n => Batching (Sized s n a) (Sized s n b -> r)

% request :: (Dom s a, Dom s b, CPointed s, CFoldable s) => a -> Batching s a b b
% request a = Batching (singleton a) Sized.head

% instance Functor (Batching s a b) where
%   fmap f (Batching as bsr) = Batching as (f . bsr)

% instance (Dom s a, CFreeMonoid s, Dom s b) => Applicative (Batching s a b) where
%   pure x = Batching empty (const x)
%   Batching as1 bsf <*> Batching as2 bsr = Batching (Sized.append as1 as2) $ \bs ->
%     let
%       (bs1, bs2) = Sized.splitAt (Sized.sLength as1) bs
%     in
%     _

% newtype SizePreservingF g s a b n = SizePreservingF (Sized s n a -> g (Sized s n b))

% partsOf :: forall f s t a b n. Functor f
%         => Fresh n
%         -> Traversing (->) f s t a b
%         -> LensLike f s t (Sized [] n a) (Sized [] n b)
% partsOf fresh o f s =
%   let --(t, (aVec, bVec)) = flip runState abList2 $ traverseOf o step s
%     g :: forall z. Sized [] z a -> f (Sized [] z b)
%     g as = innerCoerce (bindFresh fresh) (SizePreservingF f) & \(SizePreservingF h) -> h as
%     x = g empty
%     y = g $ singleton undefined
%     t = undefined
%   in t

% \end{code}

% \begin{code}

% data TheseTag
%   = ThisTag
%   | ThatTag
%   | TheseTag
%   deriving ( Eq, Ord, Show )

% -- These with tagged constructors, so a function can only map to the same constructor as the argument it receives
% data TaggedThese tag a b where
%   This :: a -> TaggedThese 'ThisTag a b
%   That :: b -> TaggedThese 'ThatTag a b
%   These :: a -> b -> TaggedThese 'TheseTag a b

% \end{code}

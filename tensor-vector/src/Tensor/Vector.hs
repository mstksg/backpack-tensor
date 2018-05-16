{-# LANGUAGE AllowAmbiguousTypes                      #-}
{-# LANGUAGE ConstraintKinds                          #-}
{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TemplateHaskell                          #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeFamilyDependencies                   #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Tensor.Vector (
  -- * Types
    Tensor(..), Scalar, Dom(..), RSym0, CSym0, SDom
  -- * General manipulation
  , genA, gen, konst, sumElements
  , mapT, zipT
  , index, select
  , reshape
  , load, store
  -- * BLAS
  , transp
  -- ** Level 1
  , scal, axpy, dot, norm2, asum, iamax
  -- -- ** Level 2
  -- , gemv, ger, syr
  -- -- ** Level 3
  -- , gemm, syrk
  ) where

import           Data.Coerce
import           Data.Complex
import           Data.Finite
import           Data.Finite.Internal
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Singletons.TH
import           Data.Singletons.TypeLits
import           Data.Type.Product hiding           (select, index)
import           GHC.TypeNats
import           Type.Class.Witness
import           Type.Family.List
import qualified Data.Vector.Generic                as VG
import qualified Data.Vector.Generic.Sized          as SVG
import qualified Data.Vector.Generic.Sized.Internal as SVG
import qualified Data.Vector.Storable               as VS

$(singletons [d|
  data Dom = R | C
  |])

type family Scalar (d :: Dom) = (s :: Type) | s -> d where
    Scalar 'R = Double
    Scalar 'C = Complex Double

newtype Tensor d (ns :: [Nat]) = T_ { getT_ :: VS.Vector (Scalar d) }

deriving instance (VS.Storable (Scalar d), Show (Scalar d)) => Show (Tensor d ns)

genA
    :: forall d ns f. (SingI d, Applicative f)
    => Sing ns
    -> (Prod Finite ns -> f (Scalar d))
    -> f (Tensor d ns)
genA s0 = domWit @VS.Storable @d //
    fmap (T_ . VS.fromList) . go s0
  where
    go :: Sing ms -> (Prod Finite ms -> f (Scalar d)) -> f [Scalar d]
    go = \case
      SNil                  -> \f -> (:[]) <$> f Ø
      SNat `SCons` ss -> \f ->
        concat <$> traverse (\i -> go ss (f . (i :<))) finites

gen :: forall d ns. SingI d
    => Sing ns
    -> (Prod Finite ns -> Scalar d)
    -> Tensor d ns
gen s0 f = domWit @VS.Storable @d //
    T_ (VS.generate l (f . splitP s0 . fromIntegral))
  where
    l = fromIntegral . product . fromSing $ s0

splitP
    :: Sing ns
    -> Integer
    -> Prod Finite ns
splitP = \case
    SNil         -> const Ø
    _ `SCons` ss -> \n ->
      let (i, j) = n `divMod` fromIntegral (product (fromSing ss))
      in  Finite i :< splitP ss j

konst
    :: forall d ns. SingI d
    => Sing ns
    -> Scalar d
    -> Tensor d ns
konst ss c = T_ $ VS.replicate l c      \\ domWit @VS.Storable @d
  where
    l = fromIntegral . fromSing . sProduct $ ss

sumElements
    :: forall d ns. (SingI d, SingI ns)
    => Tensor d ns
    -> Scalar d
sumElements = coerce (VS.sum @(Scalar d))       \\ domWit @VS.Storable @d
                                                \\ domWit @Num         @d

mapT
    :: forall d e ns. (SingI d, SingI e, SingI ns)
    => (Scalar d -> Scalar e)
    -> Tensor d ns
    -> Tensor e ns
mapT f = coerce (VS.map @(Scalar d) @(Scalar e) f)  \\ domWit @VS.Storable @d
                                                    \\ domWit @VS.Storable @e

zipT
    :: forall d e f ns. (SingI d, SingI e, SingI f, SingI ns)
    => (Scalar d -> Scalar e -> Scalar f)
    -> Tensor d ns
    -> Tensor e ns
    -> Tensor f ns
zipT f = coerce (VS.zipWith @(Scalar d) @(Scalar e) @(Scalar f) f)
      \\ domWit @VS.Storable @d
      \\ domWit @VS.Storable @e
      \\ domWit @VS.Storable @f

index
    :: forall d ns. (SingI d, SingI ns)
    => Prod Finite ns
    -> Tensor d ns
    -> Scalar d
index i (T_ xs) = domWit @VS.Storable @d //
    xs VS.! fromIntegral (joinP sing i)

joinP
    :: Sing ns
    -> Prod Finite ns
    -> Integer
joinP = \case
    SNil -> \case
      Ø -> 0
    _ `SCons` ss -> \case
      i :< js ->
        let l = fromIntegral (product (fromSing ss))
        in  getFinite i * l + joinP ss js

select
    :: (SingI d, SingI ns, SingI ms)
    => Prod Finite ns
    -> Tensor d (ns ++ ms)
    -> Tensor d ms
select = undefined

reshape
    :: (SingI d, SingI ns, Product ns ~ Product ms)
    => Sing ms
    -> Tensor d ns
    -> Tensor d ms
reshape _ = coerce

load
    :: forall v d ns. (SingI d, VG.Vector v (Scalar d))
    => Sing ns
    -> SVG.Vector v (Product ns) (Scalar d)
    -> Tensor d ns
load _ = coerce (VG.convert @v @(Scalar d) @VS.Vector)
    \\ domWit @VS.Storable @d

store
    :: forall v d ns. (SingI d, SingI ns, VG.Vector v (Scalar d))
    => Tensor d ns
    -> SVG.Vector v (Product ns) (Scalar d)
store = coerce (VG.convert @VS.Vector @(Scalar d) @v)
    \\ domWit @VS.Storable @d

transp
    :: (SingI d, KnownNat m, KnownNat n)
    => Tensor d '[m, n]
    -> Tensor d '[n, m]
transp t = gen sing $ \(i :< j :< Ø) -> index (j :< i :< Ø) t

scal
    :: forall d n. (SingI d, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ α x
scal α = coerce (VS.map (α *))
    \\ domWit @Num @d
    \\ domWit @VS.Storable @d

axpy
    :: (SingI d, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ y
    -> Tensor d '[n]    -- ^ α x + y
axpy = undefined

dot :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ y
    -> Scalar d     -- ^ x' y
dot (T_ xs) (T_ ys) = VS.sum (VS.zipWith (+) xs ys)
    \\ domWit @VS.Storable @d
    \\ domWit @Num @d

norm2
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Scalar 'R     -- ^ ||x||
norm2 (T_ xs) = case sing @_ @d of
    SR -> VS.sum $ VS.map (**2) xs
    SC -> VS.sum $ VS.map (\(r :+ i) -> r**2 + i**2) xs

asum
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Scalar 'R     -- ^ sum_i |x_i|
asum (T_ xs) = case sing @_ @d of
    SR -> VS.sum $ VS.map abs xs
    SC -> VS.sum $ VS.map magnitude xs

iamax
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n + 1]    -- ^ x
    -> Finite (n + 1)     -- ^ argmax_i |x_i|
iamax (T_ xs) = Finite . fromIntegral @Int $ case sing @_ @d of
    SR -> VS.maxIndex (VS.map abs xs)
    SC -> VS.maxIndex (VS.map magnitude xs)

-- gemv
--     :: (SingI d, KnownNat m, KnownNat n)
--     => Scalar d     -- ^ α
--     -> Tensor d '[m, n]  -- ^ A
--     -> Tensor d '[n]    -- ^ x
--     -> Maybe (Scalar d, Tensor d '[m])    -- ^ β, y
--     -> Tensor d '[m]    -- ^ α A x + β y

-- ger :: (SingI d, KnownNat m, KnownNat n)
--     => Scalar d     -- ^ α
--     -> Tensor d '[m]    -- ^ x
--     -> Tensor d '[n]    -- ^ y
--     -> Maybe (Tensor d '[m, n])  -- ^ A
--     -> Tensor d '[m, n]  -- ^ α x y' + A

-- syr :: (SingI d, KnownNat n)
--     => Scalar d           -- ^ α
--     -> Tensor d '[n]             -- ^ x
--     -> Maybe (Tensor d '[n, n])  -- ^ A
--     -> Tensor d '[n, n]          -- ^ x x' + A

-- gemm
--     :: (SingI d, KnownNat m, KnownNat o, KnownNat n)
--     => Scalar d     -- ^ α
--     -> Tensor d '[m, o]  -- ^ A
--     -> Tensor d '[o, n]  -- ^ B
--     -> Maybe (Scalar d, Tensor d '[m, n])  -- ^ β, C
--     -> Tensor d '[m, n]  -- ^ α A B + β C

-- syrk
--     :: (SingI d, KnownNat m, KnownNat n)
--     => Scalar d     -- ^ α
--     -> Tensor d '[m, n]  -- ^ A
--     -> Maybe (Scalar d, Tensor d '[m, m])  -- ^ β, C
--     -> Tensor d '[m, m]  -- ^ α A A' + β C

domWit
    :: forall c d. (SingI d, c Double, c (Complex Double))
    => Wit1 c (Scalar d)
domWit = case sing @_ @d of
    SR -> Wit1
    SC -> Wit1


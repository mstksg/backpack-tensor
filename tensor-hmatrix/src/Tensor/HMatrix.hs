{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Tensor.HMatrix (
  -- * Types
    Tensor(..), Scalar
  -- * General manipulation
  , genA, gen, konst, sumElements
  , mapT, zipT, zipTN
  , index, select
  , reshape
  , load, store
  -- * BLAS
  , transp
  -- ** Level 1
  , scal, axpy, dot, norm2, asum, iamax
  -- ** Level 2
  , gemv, ger, syr
  -- ** Level 3
  , gemm, syrk
  ) where

import           Data.Coerce
import           Data.Finite
import           Data.Finite.Internal
import           Data.Kind
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.TypeLits
import           Data.Type.Combinator
import           Data.Type.Product hiding           (select, index)
import           Type.Family.List
import qualified Data.Type.Vector                   as V
import qualified Data.Vector.Generic                as VG
import qualified Data.Vector.Generic.Sized          as SVG
import qualified Data.Vector.Generic.Sized.Internal as SVG
import qualified Data.Vector.Storable               as VS
import qualified GHC.TypeLits                       as TL
import qualified Numeric.LinearAlgebra              as H

type Scalar = Double
type family Tensor' (ns :: [Nat]) :: Type where
    Tensor' '[]        = Double
    Tensor' '[n]       = H.Vector Double
    Tensor' '[n,m]     = H.Matrix Double
    Tensor' (n':m':ns) = TL.TypeError ('TL.Text "Unsupported dimension: " 'TL.:<>: 'TL.ShowType ns)

newtype Tensor ns = T_ { getT_ :: Tensor' ns }

deriving instance Show (Tensor' ns) => Show (Tensor ns)

genA
    :: forall ns f. Applicative f
    => Sing ns
    -> (Prod Finite ns -> f Scalar)
    -> f (Tensor ns)
genA = \case
    SNil -> \f ->
      T_ <$> f Ø
    sn@SNat `SCons` SNil -> \f ->
      T_ . VS.fromListN (fromIntegral (fromSing sn)) <$> traverse (f . (:< Ø)) finites
    sn@SNat `SCons` sm@SNat `SCons` SNil -> \f ->
      let n = fromIntegral $ fromSing sn
          m = fromIntegral $ fromSing sm
      in  T_ . H.reshape m . VS.fromListN (n * m) <$>
            traverse (\(separateProduct->(j,i)) -> f (i :< j :< Ø)) finites
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "genA"

gen :: Sing ns
    -> (Prod Finite ns -> Scalar)
    -> Tensor ns
gen = \case
    SNil -> \f ->
      T_ $ f Ø
    sn@SNat `SCons` SNil -> \f ->
      T_ $ H.build (fromIntegral (fromSing sn)) (f . (:< Ø) .  round)
    sn@SNat `SCons` sm@SNat `SCons` SNil -> \f ->
      T_ $ H.build (fromIntegral (fromSing sn), fromIntegral (fromSing sm))
        (\i j -> f (round i :< round j :< Ø))
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "genA"

konst
    :: Sing ns
    -> Scalar
    -> Tensor ns
konst = \case
    SNil ->
      T_
    sn@SNat `SCons` SNil ->
      T_ . flip H.konst (fromIntegral (fromSing sn))
    sn@SNat `SCons` sm@SNat `SCons` SNil ->
      T_ . flip H.konst (fromIntegral (fromSing sn), fromIntegral (fromSing sm))
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "konst"

sumElements
    :: forall ns. SingI ns
    => Tensor ns
    -> Scalar
sumElements = case sing @_ @ns of
    SNil -> coerce
    SNat `SCons` SNil -> coerce $
        H.sumElements @H.Vector @Double
    SNat `SCons` SNat `SCons` SNil -> coerce $
        H.sumElements @H.Matrix @Double
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "sumElements"

mapT
    :: forall ns. SingI ns
    => (Scalar -> Scalar)
    -> Tensor ns
    -> Tensor ns
mapT f = case sing @_ @ns of
    SNil -> coerce f
    SNat `SCons` SNil -> coerce $
        H.cmap @_ @H.Vector f
    SNat `SCons` SNat `SCons` SNil -> coerce $
        H.cmap @_ @H.Matrix f
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "mapT"

zipT
    :: forall ns. SingI ns
    => (Scalar -> Scalar -> Scalar)
    -> Tensor ns
    -> Tensor ns
    -> Tensor ns
zipT f = case sing @_ @ns of
    SNil -> coerce f
    SNat `SCons` SNil -> coerce $ VS.zipWith f
    SNat `SCons` sm@SNat `SCons` SNil -> \(T_ x) (T_ y) ->
      T_ . H.reshape (fromIntegral (fromSing sm)) $
        VS.zipWith f (H.flatten x) (H.flatten y)
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "zipT"

zipTN
    :: forall n ns. SingI ns
    => (V.Vec n Scalar -> Scalar)
    -> V.VecT n Tensor ns
    -> Tensor ns
zipTN f ts = gen (sing @_ @ns) $ \i -> f (V.vmap (I . index i) ts)

index
    :: SingI ns
    => Prod Finite ns
    -> Tensor ns
    -> Scalar
index = \case
    Ø -> coerce
    i :< Ø -> coerce $
      flip (H.atIndex @H.Vector @Double) (fromIntegral (getFinite i))
    i :< j :< Ø -> coerce $
      flip (H.atIndex @H.Matrix @Double)
        (fromIntegral (getFinite i), fromIntegral (getFinite j))
    _ -> dimErr "index"

select
    :: forall ns ms. (SingI ns, SingI ms)
    => Prod Finite ns
    -> Tensor (ns ++ ms)
    -> Tensor ms
select = \case
    Ø -> id
    is@(i :< Ø) -> case sing @_ @ms of
      SNil -> coerce (index is)
      SNat `SCons` SNil -> coerce $
          H.flatten @Double
        . (H.? [fromIntegral (getFinite i)])
      _ `SCons` _ `SCons` _ -> dimErr "select"
    is@(_ :< _ :< Ø) -> case sing @_ @ms of
      SNil -> coerce (index is)
      _ `SCons` _ -> dimErr "select"
    _ -> dimErr "select"


reshape
    :: forall ns ms. (SingI ns, Product ns ~ Product ms)
    => Sing ms
    -> Tensor ns
    -> Tensor ms
reshape = \case
    SNil -> coerce (sumElements @ns)
    sns@(SNat `SCons` SNil) -> case sing @_ @ns of
      SNil -> coerce (konst sns)
      SNat `SCons` SNil -> id
      SNat `SCons` SNat `SCons` SNil -> coerce (H.flatten @Double)
      _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"
    sns@(SNat `SCons` sm@SNat `SCons` SNil) -> case sing @_ @ns of
      SNil -> coerce (konst sns)
      SNat `SCons` SNil -> coerce $
          H.reshape @Double (fromIntegral (fromSing sm))
      SNat `SCons` SNat `SCons` SNil -> coerce $
          H.reshape @Double (fromIntegral (fromSing sm)) . H.flatten
      _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"

load
    :: forall v ns. VG.Vector v Scalar
    => Sing ns
    -> SVG.Vector v (Product ns) Scalar
    -> Tensor ns
load = \case
    SNil -> coerce $
        flip (SVG.index @v @1 @Double) 0
    SNat `SCons` SNil -> coerce $
        SVG.convert @v @Double @H.Vector
    SNat `SCons` sm@SNat `SCons` SNil -> coerce $
          H.reshape (fromIntegral (fromSing sm))
        . SVG.fromSized
        . SVG.convert @v @Double @H.Vector
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "load"

store
    :: forall v ns. (SingI ns, VG.Vector v Scalar)
    => Tensor ns
    -> SVG.Vector v (Product ns) Scalar
store = case sing @_ @ns of
    SNil -> coerce $
        SVG.singleton @v @Double
    SNat `SCons` SNil -> coerce $
        SVG.convert @H.Vector @Double @v
    SNat `SCons` SNat `SCons` SNil -> coerce $
          SVG.convert @H.Vector @Double @v
        . SVG.Vector
        . H.flatten
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "store"

transp
    :: (KnownNat m, KnownNat n)
    => Tensor '[m, n]
    -> Tensor '[n, m]
transp = coerce $ H.tr @(H.Matrix Double) @(H.Matrix Double)

scal
    :: KnownNat n
    => Scalar         -- ^ α
    -> Tensor '[n]    -- ^ x
    -> Tensor '[n]    -- ^ α x
scal = coerce $ H.scale @Double @H.Vector

axpy
    :: KnownNat n
    => Scalar     -- ^ α
    -> Tensor '[n]    -- ^ x
    -> Tensor '[n]    -- ^ y
    -> Tensor '[n]    -- ^ α x + y
axpy α (T_ x) (T_ y) = T_ $ H.scale α x + y

dot :: KnownNat n
    => Tensor '[n]    -- ^ x
    -> Tensor '[n]    -- ^ y
    -> Scalar     -- ^ x' y
dot = coerce $ H.dot @Double

norm2
    :: KnownNat n
    => Tensor '[n]    -- ^ x
    -> Scalar     -- ^ ||x||
norm2 = coerce $ H.norm_2 @(H.Vector Double)

asum
    :: KnownNat n
    => Tensor '[n]    -- ^ x
    -> Scalar     -- ^ sum_i |x_i|
asum = coerce $ H.norm_1 @(H.Vector Double)

iamax
    :: forall n. KnownNat n
    => Tensor '[n TL.+ 1]    -- ^ x
    -> Finite (n TL.+ 1)     -- ^ argmax_i |x_i|
iamax = coerce $ fromIntegral @_ @Integer
               . H.maxIndex @H.Vector @Double
               . abs

gemv
    :: (KnownNat m, KnownNat n)
    => Scalar     -- ^ α
    -> Tensor '[m, n]  -- ^ A
    -> Tensor '[n]    -- ^ x
    -> Maybe (Scalar, Tensor '[m])    -- ^ β, y
    -> Tensor '[m]    -- ^ α A x + β y
gemv α (T_ a) (T_ x) Nothing          = T_ $ H.scale α (a H.#> x)
gemv α (T_ a) (T_ x) (Just (β, T_ y)) = T_ $ H.scale α (a H.#> x)
                                           + H.scale β y

ger :: (KnownNat m, KnownNat n)
    => Scalar     -- ^ α
    -> Tensor '[m]    -- ^ x
    -> Tensor '[n]    -- ^ y
    -> Maybe (Tensor '[m, n])  -- ^ A
    -> Tensor '[m, n]  -- ^ α x y' + A
ger α (T_ x) (T_ y) Nothing       = T_ $ H.scale α (x `H.outer` y)
ger α (T_ x) (T_ y) (Just (T_ a)) = T_ $ H.scale α (x `H.outer` y) + a

syr :: KnownNat n
    => Scalar           -- ^ α
    -> Tensor '[n]             -- ^ x
    -> Maybe (Tensor '[n, n])  -- ^ A
    -> Tensor '[n, n]          -- ^ x x' + A
syr α x = ger α x x

gemm
    :: (KnownNat m, KnownNat o, KnownNat n)
    => Scalar     -- ^ α
    -> Tensor '[m, o]  -- ^ A
    -> Tensor '[o, n]  -- ^ B
    -> Maybe (Scalar, Tensor '[m, n])  -- ^ β, C
    -> Tensor '[m, n]  -- ^ α A B + β C
gemm α (T_ a) (T_ b) Nothing          = T_ $ H.scale α (a H.<> b)
gemm α (T_ a) (T_ b) (Just (β, T_ c)) = T_ $ H.scale α (a H.<> b)
                                           + H.scale β c

syrk
    :: (KnownNat m, KnownNat n)
    => Scalar     -- ^ α
    -> Tensor '[m, n]  -- ^ A
    -> Maybe (Scalar, Tensor '[m, m])  -- ^ β, C
    -> Tensor '[m, m]  -- ^ α A A' + β C
syrk α a βc = gemm α a (transp a) βc

dimErr :: String -> a
dimErr s = errorWithoutStackTrace $ "Tensor.HMatrix." ++ s ++ ": Unsupported dimensions"

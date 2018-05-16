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

module Tensor.HMatrix (
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
  -- ** Level 2
  , gemv, ger, syr
  -- ** Level 3
  , gemm, syrk
  ) where

import           Data.Coerce
import           Data.Complex
import           Data.Finite
import           Data.Finite.Internal
import           Data.Kind
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.TH
import           Data.Singletons.TypeLits
import           Data.Type.Product hiding           (select, index)
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Family.List
import qualified Data.Vector.Generic                as VG
import qualified Data.Vector.Generic.Sized          as SVG
import qualified Data.Vector.Generic.Sized.Internal as SVG
import qualified Data.Vector.Storable               as VS
import qualified GHC.TypeLits                       as TL
import qualified Numeric.LinearAlgebra              as H

$(singletons [d|
  data Dom = R | C
  |])

type family Scalar (d :: Dom) = (s :: Type) | s -> d where
    Scalar 'R = Double
    Scalar 'C = Complex Double

type family Tensor' (d :: Dom) (ns :: [Nat]) :: Type where
    Tensor' d '[]        = Scalar d
    Tensor' d '[n]       = H.Vector (Scalar d)
    Tensor' d '[n,m]     = H.Matrix (Scalar d)
    Tensor' d (n':m':ns) = TL.TypeError ('TL.Text "Unsupported dimension: " 'TL.:<>: 'TL.ShowType ns)

newtype Tensor d ns = T_ { getT_ :: Tensor' d ns }

deriving instance Show (Tensor' d ns) => Show (Tensor d ns)

genA
    :: forall d ns f. (SingI d, Applicative f)
    => Sing ns
    -> (Prod Finite ns -> f (Scalar d))
    -> f (Tensor d ns)
genA = domWit @VS.Storable @d // \case
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

gen :: forall d ns. SingI d
    => Sing ns
    -> (Prod Finite ns -> Scalar d)
    -> Tensor d ns
gen = \case
    SNil -> \f ->
      T_ $ f Ø
    sn@SNat `SCons` SNil -> \f -> case sing @_ @d of
      SR -> T_ $ H.build (fromIntegral (fromSing sn)) (f . (:< Ø) . round)
      SC -> T_ $ H.build (fromIntegral (fromSing sn)) (f . (:< Ø) . round . realPart)
    sn@SNat `SCons` sm@SNat `SCons` SNil -> \f -> case sing @_ @d of
      SR -> T_ $ H.build (fromIntegral (fromSing sn), fromIntegral (fromSing sm))
                   (\i j -> f (round i :< round j :< Ø))
      SC -> T_ $ H.build (fromIntegral (fromSing sn), fromIntegral (fromSing sm))
                   (\(realPart->i) (realPart->j) -> f (round i :< round j :< Ø))
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "genA"

konst
    :: forall d ns. (SingI d)
    => Sing ns
    -> Scalar d
    -> Tensor d ns
konst = domWit @(H.Container H.Vector) @d //
        domWit @Num @d                    // \case
    SNil ->
      T_
    sn@SNat `SCons` SNil ->
      T_ . flip H.konst (fromIntegral (fromSing sn))
    sn@SNat `SCons` sm@SNat `SCons` SNil ->
      T_ . flip H.konst (fromIntegral (fromSing sn), fromIntegral (fromSing sm))
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "konst"

sumElements
    :: forall d ns. (SingI d, SingI ns)
    => Tensor d ns
    -> Scalar d
sumElements = domWit @(H.Container H.Vector) @d //
              domWit @Num @d                    // case sing @_ @ns of
    SNil -> coerce
    SNat `SCons` SNil -> coerce $
        H.sumElements @H.Vector @(Scalar d)
    SNat `SCons` SNat `SCons` SNil -> coerce $
        H.sumElements @H.Matrix @(Scalar d)
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "sumElements"

mapT
    :: forall d e ns. (SingI d, SingI e, SingI ns)
    => (Scalar d -> Scalar e)
    -> Tensor d ns
    -> Tensor e ns
mapT f = domWit @(H.Container H.Vector) @d //
         domWit @H.Element              @e //
         domWit @Num                    @d // case sing @_ @ns of
    SNil -> coerce f
    SNat `SCons` SNil -> coerce $
        H.cmap @_ @H.Vector f
    SNat `SCons` SNat `SCons` SNil -> coerce $
        H.cmap @_ @H.Matrix f
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "mapT"

zipT
    :: forall d e f ns. (SingI d, SingI e, SingI f, SingI ns)
    => (Scalar d -> Scalar e -> Scalar f)
    -> Tensor d ns
    -> Tensor e ns
    -> Tensor f ns
zipT f = domWit @VS.Storable @d //
         domWit @VS.Storable @e //
         domWit @H.Element   @e //
         domWit @VS.Storable @f //
         domWit @H.Element   @d // case sing @_ @ns of
    SNil -> coerce f
    SNat `SCons` SNil -> coerce $ VS.zipWith f
    SNat `SCons` sm@SNat `SCons` SNil -> \(T_ x) (T_ y) ->
      T_ . H.reshape (fromIntegral (fromSing sm)) $
        VS.zipWith f (H.flatten x) (H.flatten y)
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "zipT"

index
    :: forall d ns. (SingI d, SingI ns)
    => Prod Finite ns
    -> Tensor d ns
    -> Scalar d
index = domWit @(H.Container H.Vector) @d //
        domWit @Num @d                    // \case
    Ø -> coerce
    i :< Ø -> coerce $
      flip (H.atIndex @H.Vector @(Scalar d)) (fromIntegral (getFinite i))
    i :< j :< Ø -> coerce $
      flip (H.atIndex @H.Matrix @(Scalar d))
        (fromIntegral (getFinite i), fromIntegral (getFinite j))
    _ -> dimErr "index"

select
    :: forall d ns ms. (SingI d, SingI ns, SingI ms)
    => Prod Finite ns
    -> Tensor d (ns ++ ms)
    -> Tensor d ms
select = domWit @H.Element @d // \case
    Ø -> id
    is@(i :< Ø) -> case sing @_ @ms of
      SNil -> coerce (index @d is)
      SNat `SCons` SNil -> coerce $
          H.flatten @(Scalar d)
        . (H.? [fromIntegral (getFinite i)])
      _ `SCons` _ `SCons` _ -> dimErr "select"
    is@(_ :< _ :< Ø) -> case sing @_ @ms of
      SNil -> coerce (index @d is)
      _ `SCons` _ -> dimErr "select"
    _ -> dimErr "select"


reshape
    :: forall d ns ms. (SingI d, SingI ns, Product ns ~ Product ms)
    => Sing ms
    -> Tensor d ns
    -> Tensor d ms
reshape = \case
    SNil -> coerce (sumElements @d @ns)
    sns@(SNat `SCons` SNil) -> case sing @_ @ns of
      SNil -> coerce (konst @d sns)
      SNat `SCons` SNil -> id
      SNat `SCons` SNat `SCons` SNil -> coerce (H.flatten @Double)
      _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"
    sns@(SNat `SCons` sm@SNat `SCons` SNil) -> case sing @_ @ns of
      SNil -> coerce (konst @d sns)
      SNat `SCons` SNil -> coerce $
          H.reshape @Double (fromIntegral (fromSing sm))
      SNat `SCons` SNat `SCons` SNil -> coerce $
          H.reshape @Double (fromIntegral (fromSing sm)) . H.flatten
      _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "reshape"

load
    :: forall v d ns. (VG.Vector v (Scalar d), SingI d)
    => Sing ns
    -> SVG.Vector v (Product ns) (Scalar d)
    -> Tensor d ns
load = domWit @VS.Storable @d // \case
    SNil -> coerce $
        flip (SVG.index @v @1 @(Scalar d)) 0
    SNat `SCons` SNil -> coerce $
        SVG.convert @v @(Scalar d) @H.Vector
    SNat `SCons` sm@SNat `SCons` SNil -> coerce $
          H.reshape (fromIntegral (fromSing sm))
        . SVG.fromSized
        . SVG.convert @v @(Scalar d) @H.Vector
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "load"

store
    :: forall v d ns. (SingI d, SingI ns, VG.Vector v (Scalar d))
    => Tensor d ns
    -> SVG.Vector v (Product ns) (Scalar d)
store = domWit @VS.Storable @d //
        domWit @H.Element   @d // case sing @_ @ns of
    SNil -> coerce $
        SVG.singleton @v @(Scalar d)
    SNat `SCons` SNil -> coerce $
        SVG.convert @H.Vector @(Scalar d) @v
    SNat `SCons` SNat `SCons` SNil -> coerce $
          SVG.convert @H.Vector @(Scalar d) @v
        . SVG.Vector
        . H.flatten
    _ `SCons` _ `SCons` _ `SCons` _ -> dimErr "store"

transp
    :: forall d m n. (SingI d, KnownNat m, KnownNat n)
    => Tensor d '[m, n]
    -> Tensor d '[n, m]
transp = case sing @_ @d of
    SR -> coerce $ H.tr @(H.Matrix Double) @(H.Matrix Double)
    SC -> coerce $ H.tr @(H.Matrix (Complex Double)) @(H.Matrix (Complex Double))

scal
    :: forall d n. (SingI d, KnownNat n)
    => Scalar d         -- ^ α
    -> Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ α x
scal = domWit @(H.Container H.Vector) @d //
        coerce (H.scale @(Scalar d) @H.Vector)

axpy
    :: forall d n. (SingI d, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ y
    -> Tensor d '[n]    -- ^ α x + y
axpy α (T_ x) (T_ y) = domWit @(H.Container H.Vector) @d //
    T_ (H.scale α x `H.add` y)

dot :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Tensor d '[n]    -- ^ y
    -> Scalar d     -- ^ x' y
dot = domWit @H.Numeric @d //
    coerce (H.dot @(Scalar d))

norm2
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Scalar 'R     -- ^ ||x||
norm2 = domWit @(Comp H.Normed H.Vector) @d //
    coerce (H.norm_2 @(H.Vector (Scalar d)))

asum
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n]    -- ^ x
    -> Scalar 'R     -- ^ sum_i |x_i|
asum = domWit @(Comp H.Normed H.Vector) @d //
    coerce (H.norm_1 @(H.Vector (Scalar d)))

iamax
    :: forall d n. (SingI d, KnownNat n)
    => Tensor d '[n TL.+ 1]    -- ^ x
    -> Finite (n TL.+ 1)       -- ^ argmax_i |x_i|
iamax = domWit @(H.Container H.Vector) @d //
        domWit @Num                    @d //
    coerce ( fromIntegral @_ @Integer
           . H.maxIndex @H.Vector @(Scalar d)
           . H.cmap abs
           )

gemv
    :: forall d m n. (SingI d, KnownNat m, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[m, n]  -- ^ A
    -> Tensor d '[n]    -- ^ x
    -> Maybe (Scalar d, Tensor d '[m])    -- ^ β, y
    -> Tensor d '[m]    -- ^ α A x + β y
gemv α (T_ a) (T_ x) βy = domWit @(H.Container H.Vector) @d //
                          domWit @H.Numeric              @d //
    case βy of
      Nothing        -> T_ $ H.scale α (a H.#> x)
      Just (β, T_ y) -> T_ $ H.scale α (a H.#> x) `H.add` H.scale β y

ger :: forall d m n. (SingI d, KnownNat m, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[m]    -- ^ x
    -> Tensor d '[n]    -- ^ y
    -> Maybe (Tensor d '[m, n])  -- ^ A
    -> Tensor d '[m, n]  -- ^ α x y' + A
ger α (T_ x) (T_ y) ma = domWit @(H.Container H.Vector) @d //
                         domWit @H.Product              @d //
    case ma of
      Nothing     -> T_ $ H.scale α (x `H.outer` y)
      Just (T_ a) -> T_ $ H.scale α (x `H.outer` y) `H.add` a

syr :: (SingI d, KnownNat n)
    => Scalar d           -- ^ α
    -> Tensor d '[n]             -- ^ x
    -> Maybe (Tensor d '[n, n])  -- ^ A
    -> Tensor d '[n, n]          -- ^ x x' + A
syr α x = ger α x x

gemm
    :: forall d m o n. (SingI d, KnownNat m, KnownNat o, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[m, o]  -- ^ A
    -> Tensor d '[o, n]  -- ^ B
    -> Maybe (Scalar d, Tensor d '[m, n])  -- ^ β, C
    -> Tensor d '[m, n]  -- ^ α A B + β C
gemm α (T_ a) (T_ b) βc = domWit @H.Numeric @d //
    case βc of
      Nothing        -> T_ $ H.scale α (a H.<> b)
      Just (β, T_ c) -> T_ $ H.scale α (a H.<> b) `H.add` H.scale β c

syrk
    :: (SingI d, KnownNat m, KnownNat n)
    => Scalar d     -- ^ α
    -> Tensor d '[m, n]  -- ^ A
    -> Maybe (Scalar d, Tensor d '[m, m])  -- ^ β, C
    -> Tensor d '[m, m]  -- ^ α A A' + β C
syrk α a βc = gemm α a (transp a) βc

domWit :: forall c d. (SingI d, c Double, c (Complex Double)) => Wit1 c (Scalar d)
domWit = case sing @_ @d of
    SR -> Wit1
    SC -> Wit1

dimErr :: String -> a
dimErr s = errorWithoutStackTrace $ "Tensor.HMatrix." ++ s ++ ": Unsupported dimensions"


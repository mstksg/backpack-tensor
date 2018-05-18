{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Tensor (
    module Tensor.Core
  , (#>)
  , (<#)
  , (<#>)
  ) where

import           Data.Singletons
import           Data.Singletons.TypeLits
import           Tensor.Core

(#>)
    :: (SingI d, Num (Scalar d), KnownNat m, KnownNat n)
    => Tensor d '[m, n] -> Tensor d '[n] -> Tensor d '[m]
a #> x = matVecScale 1 a x

(<#)
    :: (SingI d, Num (Scalar d), KnownNat m, KnownNat n)
    => Tensor d '[m] -> Tensor d '[m,n] -> Tensor d '[n]
x <# a = tr a #> x

(<#>)
    :: (SingI d, Num (Scalar d), KnownNat m, KnownNat o, KnownNat n)
    => Tensor d '[m,o] -> Tensor d '[o,n] -> Tensor d '[m,n]
x <#> y = matMatScale 1 x y

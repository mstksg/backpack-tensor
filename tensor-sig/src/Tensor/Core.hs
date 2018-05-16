{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Tensor.Core (
    Product
  , sProduct
  , product
  ) where

import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           Data.Singletons.TypeLits
import qualified Prelude                  as P

$(singletons [d|
  product :: [Nat] -> Nat
  product []       = 1
  product (n : ns) = n P.* product ns
  |])

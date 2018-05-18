{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

import           Tensor.Core
import           Data.Type.Product
import           Data.Singletons

main :: IO ()
main = do
    print test1
    print test2
    print $ matVecScale 0.5 test1 test2

test1 :: Tensor 'R '[5,3]
test1 = gen sing $ \(i :< j :< Ø) -> fromIntegral i + fromIntegral j

test2 :: Tensor 'R '[3]
test2 = gen sing $ \(i :< Ø) -> fromIntegral i

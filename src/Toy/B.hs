
module Toy.B where

import Toy.A (i2)


{-@ i3 :: Nat @-}
i3 :: Int
i3 = i2 - 50

module Foo.Bar.Example
    ( doubleIt
    , three
    ) where

{-@ doubleIt :: Nat -> Nat @-}
doubleIt :: Int -> Int
doubleIt x = x * 2

{-@ three :: Nat @-}
three :: Int
three = 1 + 2



{- | This module defines assumptions and other Liquid refinements that we use to test if the lifted
     spec retains such information.
-}

module Toy.A ( notThree, one, two, d1, d2, notEmpty, myTest, i2 ) where

-- | We define a simple type to be able to use it inside signatures and assumptions.
data D = MkD1 | MkD2

-- | Here we define a simple function 'd1' and we refine its type to be 'MkD1'. This will translate
-- into LH with 'd1' ending up into the \"sigs\" of the final spec.

{-@ d1 :: {v:D | v = MkD1} @-}
d1 :: D
d1 = MkD1

-- | Here we define a simple function 'd2' and we /assume/ its type to be 'MkD2'. This will translate
-- into LH with 'd2' ending up into the \"asmSigs\" of the final spec.

{-@ assume d2 :: {v:D | v = MkD2} @-}
d2 :: D
d2 = MkD2

-- | This tests that LH can infer that this is a basic type 'int'. If this fails to check probably means
-- that either the assumption for 'I#' was not exported, which is:
--
-- assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
--
--

--{-@ assume one :: {v: Int | v = 1 } @-}

{-@ one :: {v:Int | v = 1 } @-}
one :: Int
one = 1

foo :: Int
foo = 10

{-@ assume notThree :: {v : Nat | v != 3 } @-}
notThree :: Int
notThree = 4

{-@ two :: Nat @-}
two :: Int
two = one + one

{- @ invariant {v:Nat | 0 <= v } @-}

{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True


{-@
data MyStruct = MyStruct
    { size :: Nat
    }
@-}

data MyStruct = MyStruct
    { size :: {-# UNPACK #-} !Int
    } deriving Show

{-@ i0 :: Nat @-}
i0 :: Int
i0 = 0

{-@ i1 :: Nat @-}
i1 :: Int
i1 = 5

{-@ i2 :: Nat @-}
i2 :: Int
i2 = 10 + i1

{-@ enlargeMyStruct :: b:MyStruct -> i:Nat -> v:MyStruct @-}
enlargeMyStruct :: MyStruct -> Int -> MyStruct
enlargeMyStruct (MyStruct old) i = MyStruct (old + i)

myTest :: IO ()
myTest = do
  print i2
  print $ enlargeMyStruct (MyStruct 0) i0


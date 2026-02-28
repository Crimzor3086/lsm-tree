{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Database.LSMTree.Internal.BloomFilterDependencies (tests) where

import           Control.Exception (ErrorCall, evaluate, try)
import           Control.Monad (forM_)
import           Control.Monad.ST (ST, runST)
import qualified Data.Array.Byte as AB
import qualified Data.BloomFilter as Bloom
import qualified Data.BloomFilter.BitVec64 as BitVec64
import qualified Data.BloomFilter.Calc as Calc
import qualified Data.BloomFilter.Easy as Easy
import qualified Data.BloomFilter.Hash as Hash
import qualified Data.BloomFilter.Mutable as Mutable
import           Data.Char (ord)
import           Data.List (isInfixOf)
import qualified Data.Primitive.ByteArray as P
import qualified Data.Primitive.PrimArray as PrimArray
import           Data.Word (Word32, Word64, Word8)
import           Test.QuickCheck (Positive (..), Property, counterexample,
                     (===))
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit (Assertion, assertBool, assertFailure,
                     testCase, (@?=))
import           Test.Tasty.QuickCheck (Small (..), testProperty)


tests :: TestTree
tests = testGroup "Data.BloomFilter dependency coverage"
    [ testGroup "Data.BloomFilter"
        [ testCase "freeze/thaw/freeze roundtrip" case_freezeThawRoundtrip
        , testCase "empty filter has no members" case_emptyFilterHasNoMembers
        , testCase "singleton has inserted member" case_singletonHasMember
        , testCase "elemHashes can query precomputed hashes" case_elemHashes
        , testCase "elemHashes returns False when bits are unset"
            case_elemHashesMiss
        , testCase "length reports bit count" case_bloomLength
        , testCase "unfold populates values" case_unfold
        ]
    , testGroup "Data.BloomFilter.BitVec64"
        [ testCase "large vector branch and mutable operations"
            case_largeBitVecOps
        ]
    , testGroup "Data.BloomFilter.Calc"
        [ testProperty "falsePositiveProb formula"
            prop_falsePositiveProbFormula
        , testProperty "falsePositiveProb range"
            prop_falsePositiveProbRange
        ]
    , testGroup "Data.BloomFilter.Easy"
        [ testCase "easyList [] keeps empty-membership false" case_easyListEmpty
        , testCase "easyNew creates mutable bloom filter" case_easyNew
        , testCase "safeSuggestSizing handles invalid inputs"
            case_safeSuggestSizingInvalid
        , testCase "safeSuggestSizing traverses primes > 1021"
            case_safeSuggestSizingLargePrime
        , testCase "suggestSizing throws on invalid error-rate"
            case_suggestSizingInvalid
        ]
    , testGroup "Data.BloomFilter.Hash"
        [ testCase "hashSalt64 @ByteArray and hashByteArray" case_hashByteArray
        , testCase "incremental update @Word32 and @Char" case_incrementalUpdate
        , testCase "RealHashes make/eval" case_realHashes
        , testCase "Prim (CheapHashes a) instance via PrimArray"
            case_cheapHashesPrim
        , testProperty "hash64 is deterministic" prop_hash64Deterministic
        ]
    , testGroup "Data.BloomFilter.Internal"
        [ testCase "Eq works for sizes divisible by 64"
            case_bloomEqDivisibleBy64
        , testCase "Show for immutable bloom" case_showBloom
        ]
    , testGroup "Data.BloomFilter.Mutable"
        [ testCase "new 0 bits is clamped to 1" case_mutableNewZeroBits
        , testCase "new huge size guard is evaluated" case_mutableNewHugeGuard
        , testCase "elem/length work on mutable bloom" case_mutableElemLength
        , testCase "elemHashes works on mutable bloom" case_mutableElemHashes
        ]
    , testGroup "Data.BloomFilter.Mutable.Internal"
        [ testCase "Show for mutable bloom" case_showMutableBloom
        ]
    , testGroup "Additional properties"
        [ testProperty "insert is idempotent" prop_insertIdempotent
        , testProperty "freeze/thaw equivalence" prop_freezeThawEquivalence
        ]
    ]


case_freezeThawRoundtrip :: Assertion
case_freezeThawRoundtrip = do
    let ok = runST $ do
          mb <- Mutable.new 4 257 :: ST s (Mutable.MBloom s Word64)
          mapM_ (Mutable.insert mb) [1, 2, 3, 4]
          b0 <- Bloom.freeze mb
          mb' <- Bloom.thaw b0
          b1 <- Bloom.freeze mb'
          pure (b0 == b1)
    assertBool "expected equality after freeze/thaw/freeze" ok

case_emptyFilterHasNoMembers :: Assertion
case_emptyFilterHasNoMembers = do
    let bloom = Bloom.empty 4 257 :: Bloom.Bloom Word64
    Bloom.elem 999 bloom @?= False

case_singletonHasMember :: Assertion
case_singletonHasMember = do
    let bloom = Bloom.singleton 4 257 (42 :: Word64) :: Bloom.Bloom Word64
    Bloom.elem 42 bloom @?= True

case_elemHashes :: Assertion
case_elemHashes = do
    let bloom = Bloom.singleton 4 257 (88 :: Word64) :: Bloom.Bloom Word64
        hashes = Hash.makeCheapHashes (88 :: Word64)
    Bloom.elemHashes hashes bloom @?= True

case_elemHashesMiss :: Assertion
case_elemHashesMiss = do
    let bloom = Bloom.empty 4 257 :: Bloom.Bloom Word64
        hashes = Hash.makeCheapHashes (88 :: Word64)
    Bloom.elemHashes hashes bloom @?= False

case_bloomLength :: Assertion
case_bloomLength = do
    let bloom = Bloom.empty 3 333 :: Bloom.Bloom Word64
    Bloom.length bloom @?= 333

case_unfold :: Assertion
case_unfold = do
    let step i
          | i < 4     = Just (fromIntegral i :: Word64, i + 1)
          | otherwise = Nothing
        bloom = Bloom.unfold 3 257 step (0 :: Int) :: Bloom.Bloom Word64
    mapM_ (\w -> Bloom.elem w bloom @?= True) [0, 1, 2, 3]

case_largeBitVecOps :: Assertion
case_largeBitVecOps = do
    let result = runST $ do
          mv <- BitVec64.new (64 * 130)
          BitVec64.unsafeWrite mv 17 True
          BitVec64.unsafeWrite mv 17 False
          BitVec64.unsafeWrite mv 129 True
          bit17 <- BitVec64.unsafeRead mv 17
          bit129 <- BitVec64.unsafeRead mv 129
          v <- BitVec64.freeze mv
          BitVec64.prefetchIndex v 129
          mv' <- BitVec64.thaw v
          bit129' <- BitVec64.unsafeRead mv' 129
          pure (bit17, bit129, bit129', BitVec64.unsafeIndex v 129)
    result @?= (False, True, True, True)

prop_falsePositiveProbFormula
    :: Positive (Small Int)
    -> Positive (Small Int)
    -> Positive (Small Int)
    -> Property
prop_falsePositiveProbFormula (Positive (Small n0))
                             (Positive (Small m0))
                             (Positive (Small k0)) =
    let n = fromIntegral (max 1 n0) :: Double
        m = fromIntegral (max 1 m0) :: Double
        k = fromIntegral (max 1 k0) :: Double
        actual = Calc.falsePositiveProb n m k
        expected = (1 - exp (negate (k * n / m))) ** k
        delta = abs (actual - expected)
    in  counterexample
            ("actual=" <> show actual <> ", expected=" <> show expected)
        $ (delta <= 1e-10) === True

prop_falsePositiveProbRange
    :: Positive (Small Int)
    -> Positive (Small Int)
    -> Positive (Small Int)
    -> Property
prop_falsePositiveProbRange (Positive (Small n0))
                           (Positive (Small m0))
                           (Positive (Small k0)) =
    let n = fromIntegral (max 1 n0) :: Double
        m = fromIntegral (max 1 m0) :: Double
        k = fromIntegral (max 1 k0) :: Double
        p = Calc.falsePositiveProb n m k
    in  counterexample ("p=" <> show p) (0 <= p && p <= 1)

case_easyListEmpty :: Assertion
case_easyListEmpty = do
    let bloom = Easy.easyList 0.01 ([] :: [Word64])
    Bloom.length bloom @?= 1
    Bloom.elem 123 bloom @?= False

case_easyNew :: Assertion
case_easyNew = do
    let hasMember = runST $ do
          mb <- Easy.easyNew 0.01 100 :: ST s (Mutable.MBloom s Word64)
          Mutable.insert mb 7
          b <- Bloom.freeze mb
          pure (Bloom.elem 7 b)
    hasMember @?= True

case_safeSuggestSizingInvalid :: Assertion
case_safeSuggestSizingInvalid = do
    Easy.safeSuggestSizing 0 0.01 @?= Right (61, 1)
    Easy.safeSuggestSizing (-10) 0.01 @?= Right (61, 1)
    Easy.safeSuggestSizing 100 0 @?= Left "invalid error rate"
    Easy.safeSuggestSizing 100 1 @?= Left "invalid error rate"
    case Easy.safeSuggestSizing maxBound 0.01 of
      Left "capacity too large" -> pure ()
      other -> assertFailure $ "unexpected result: " <> show other

case_safeSuggestSizingLargePrime :: Assertion
case_safeSuggestSizingLargePrime = do
    let result = Easy.safeSuggestSizing 5000 0.01
    case result of
      Right (bits, hashes) -> do
        assertBool "expected a prime above 1021 to be selected" (bits > 1021)
        assertBool "expected at least one hash function" (hashes > 0)
      Left err ->
        assertFailure $ "unexpected failure: " <> err

case_suggestSizingInvalid :: Assertion
case_suggestSizingInvalid =
    assertErrorCall "suggestSizing should throw on invalid false positive rate" $
      Easy.suggestSizing 100 0

case_hashByteArray :: Assertion
case_hashByteArray = do
    let bytes = mkArrayByte [0 .. 31]
        salt = 17
    Hash.hashSalt64 salt bytes @?= Hash.hashByteArray bytes 0 32 salt

case_incrementalUpdate :: Assertion
case_incrementalUpdate = do
    let wordHash1 = Hash.incrementalHash 11 $ \s ->
                      Hash.update s (123456 :: Word32)
        wordHash2 = Hash.incrementalHash 11 $ \s ->
                      Hash.update s (123456 :: Word32)
        charHash = Hash.incrementalHash 23 $ \s ->
                     Hash.update s 'x'
        charViaWord32 = Hash.incrementalHash 23 $ \s ->
                          Hash.update s (fromIntegral (ord 'x') :: Word32)
    wordHash1 @?= wordHash2
    charHash @?= charViaWord32

case_realHashes :: Assertion
case_realHashes = do
    let x = 1234 :: Word64
        hs = Hash.makeHashes @Hash.RealHashes x
    Hash.evalHashes hs 0 @?= Hash.hashSalt64 0 x
    Hash.evalHashes hs 1 @?= Hash.hashSalt64 1 x

case_cheapHashesPrim :: Assertion
case_cheapHashesPrim = do
    let (a0, b0, b1) = runST $ do
          mba <- PrimArray.newPrimArray 2
               :: ST s (PrimArray.MutablePrimArray s (Hash.CheapHashes Word64))
          let a = Hash.makeCheapHashes (11 :: Word64)
              b = Hash.makeCheapHashes (22 :: Word64)
          PrimArray.writePrimArray mba 0 a
          PrimArray.writePrimArray mba 1 b
          a' <- PrimArray.readPrimArray mba 0
          b' <- PrimArray.readPrimArray mba 1
          ba <- PrimArray.unsafeFreezePrimArray mba
          let b'' = PrimArray.indexPrimArray ba 1
          pure (Hash.evalCheapHashes a' 0,
                Hash.evalCheapHashes b' 0,
                Hash.evalCheapHashes b'' 0)
        expectedA = Hash.evalCheapHashes (Hash.makeCheapHashes (11 :: Word64)) 0
        expectedB = Hash.evalCheapHashes (Hash.makeCheapHashes (22 :: Word64)) 0
    (a0, b0, b1) @?= (expectedA, expectedB, expectedB)

prop_hash64Deterministic :: Word64 -> Bool
prop_hash64Deterministic w =
    Hash.hash64 w == Hash.hash64 w

case_bloomEqDivisibleBy64 :: Assertion
case_bloomEqDivisibleBy64 = do
    let lhs = Bloom.singleton 4 128 (51 :: Word64) :: Bloom.Bloom Word64
        rhs = Bloom.singleton 4 128 (51 :: Word64) :: Bloom.Bloom Word64
    lhs @?= rhs

case_showBloom :: Assertion
case_showBloom = do
    let bloom = Bloom.empty 3 128 :: Bloom.Bloom Word64
    assertBool "expected Show output to mention Bloom"
      ("Bloom" `isInfixOf` show bloom)

case_mutableNewZeroBits :: Assertion
case_mutableNewZeroBits = do
    let bits = runST $ do
          mb <- Mutable.new 3 0 :: ST s (Mutable.MBloom s Word64)
          pure (Mutable.length mb)
    bits @?= 1

case_mutableNewHugeGuard :: Assertion
case_mutableNewHugeGuard =
    forceMutableNewGuard 0xffff_ffff_ffff @?= ()

case_mutableElemLength :: Assertion
case_mutableElemLength = do
    let result = runST $ do
          mb <- Mutable.new 4 257 :: ST s (Mutable.MBloom s Word64)
          Mutable.insert mb 10
          present <- Mutable.elem 10 mb
          absent <- Mutable.elem 11 mb
          pure (present, absent, Mutable.length mb)
    result @?= (True, False, 257)

case_mutableElemHashes :: Assertion
case_mutableElemHashes = do
    let result = runST $ do
          mbPresent <- Mutable.new 4 257 :: ST s (Mutable.MBloom s Word64)
          Mutable.insert mbPresent 10
          let presentHashes = Hash.makeCheapHashes (10 :: Word64)
          present <- Mutable.elemHashes presentHashes mbPresent

          mbEmpty <- Mutable.new 4 257 :: ST s (Mutable.MBloom s Word64)
          let absentHashes = Hash.makeCheapHashes (11 :: Word64)
          absent <- Mutable.elemHashes absentHashes mbEmpty

          pure (present, absent)
    result @?= (True, False)

case_showMutableBloom :: Assertion
case_showMutableBloom = do
    let shown = runST $ do
          mb <- Mutable.new 2 128 :: ST s (Mutable.MBloom s Word64)
          pure (show mb)
    assertBool "expected Show output to mention MBloom"
      ("MBloom" `isInfixOf` shown)

prop_insertIdempotent :: Word64 -> Bool
prop_insertIdempotent x =
    runST $ do
      mb <- Mutable.new 4 257 :: ST s (Mutable.MBloom s Word64)
      Mutable.insert mb x
      b0 <- Bloom.freeze mb
      Mutable.insert mb x
      b1 <- Bloom.freeze mb
      pure (b0 == b1 && Bloom.elem x b1)

prop_freezeThawEquivalence :: [Word64] -> Bool
prop_freezeThawEquivalence xs =
    runST $ do
      mb <- Mutable.new 4 1021 :: ST s (Mutable.MBloom s Word64)
      forM_ xs (Mutable.insert mb)
      b0 <- Bloom.freeze mb
      mb' <- Bloom.thaw b0
      b1 <- Bloom.freeze mb'
      pure (b0 == b1)

assertErrorCall :: String -> a -> Assertion
assertErrorCall message thunk = do
    result <- try @ErrorCall (evaluate thunk)
    case result of
      Left _  -> pure ()
      Right _ -> assertFailure message

mkArrayByte :: [Word8] -> AB.ByteArray
mkArrayByte ws = AB.ByteArray $ runST $ do
    mba <- P.newByteArray (length ws)
    forM_ (zip [0 ..] ws) $ \(i, w) ->
      P.writeByteArray mba i w
    P.unsafeFreezeByteArray mba

forceMutableNewGuard :: Word64 -> ()
forceMutableNewGuard bits = runST $ do
    let action = Mutable.new 1 bits
    action `seq` pure ()

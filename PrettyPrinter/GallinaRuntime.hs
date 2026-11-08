{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

{-# LANGUAGE ForeignFunctionInterface #-}

-- Runtime for simulating CallGallina through DPI-C. It is linked (as a GHC static
-- library, together with Verilog/GallinaShim.cpp) into Verilator simulators whose
-- SimRtl.sv contains Gallina calls. It runs the same extracted compiledMod as the
-- printer, so call sites and Gallina register leaves are numbered identically.

module GallinaRuntime where

import Data.Bits
import Data.IORef
import Data.Word
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Map.Strict as M
import Compile
import CodePrinter
import ModPrinter

type GallinaFun = (Prelude.Integer -> Prelude.Integer) -> Prelude.Integer -> Any -> (Prelude.Integer, Any)

data Runtime = Runtime
  { rtWidth :: Int                                  -- GuruGallinaWidth
  , rtSites :: M.Map Integer GallinaFun             -- call site -> wrapped Gallina function
  , rtInit  :: M.Map Integer Any                    -- Gallina register leaf -> initial value
  }

{-# NOINLINE runtime #-}
runtime :: Runtime
runtime =
  let (((_, tree), _), code) = compiledMod
      calls = gallinaCalls code
  in Runtime
       { rtWidth = fromInteger (gallinaWidth calls)
       , rtSites = M.fromList [(site, g) | GallinaCall site _ _ _ g <- calls]
       , rtInit  = M.fromList [(i, v) | (i, (_, EGallinaReg v)) <- tag (dfsElems tree)]
       }

{-# NOINLINE stateRef #-}
stateRef :: IORef (M.Map Integer Any)
stateRef = unsafePerformIO (newIORef (rtInit runtime))

-- Oracle configuration, set once by the shim from the plusargs.
{-# NOINLINE seedRef #-}
seedRef :: IORef (Word64, Bool)
seedRef = unsafePerformIO (newIORef (0, False))

-- splitmix64 finalizer
mix64 :: Word64 -> Word64
mix64 z0 =
  let z1 = (z0 `xor` (z0 `shiftR` 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
  in z2 `xor` (z2 `shiftR` 31)

-- The oracle of the execution of call site `site` in cycle `cycle`: it depends only on
-- (seed, site, cycle, n), not on any other call.
mkOracle :: (Word64, Bool) -> Integer -> Word64 -> (Prelude.Integer -> Prelude.Integer)
mkOracle (_, True) _ _ = \_ -> 0
mkOracle (seed, False) site cycle =
  let base = mix64 (mix64 (mix64 seed + fromInteger site) + cycle)
  in \n -> toInteger (mix64 (base + fromInteger n))

peekBits :: Int -> Ptr Word32 -> IO Integer
peekBits w p = do
  ws <- mapM (peekElemOff p) [0 .. (w + 31) `Prelude.div` 32 - 1]
  return (foldr (\x acc -> (acc `shiftL` 32) .|. toInteger x) 0 ws .&. (bit w - 1))

pokeBits :: Int -> Ptr Word32 -> Integer -> IO ()
pokeBits w p v =
  mapM_ (\i -> pokeElemOff p i (fromInteger ((v `shiftR` (32 * i)) .&. 0xffffffff)))
        [0 .. (w + 31) `Prelude.div` 32 - 1]

hsGuruGallinaCall :: CInt -> CInt -> CLLong -> Ptr Word32 -> Ptr Word32 -> IO ()
hsGuruGallinaCall cSite cLeaf cCycle pIn pOut = do
  let site = toInteger cSite
      leaf = toInteger cLeaf
      w = rtWidth runtime
      g = M.findWithDefault (error ("GallinaRuntime: unknown call site " ++ show site)) site (rtSites runtime)
  cfg <- readIORef seedRef
  inBits <- peekBits w pIn
  st <- readIORef stateRef
  let old = M.findWithDefault (error ("GallinaRuntime: unknown Gallina register " ++ show leaf)) leaf st
      (outBits, new) = g (mkOracle cfg site (fromIntegral cCycle)) inBits old
  new `seq` outBits `seq` writeIORef stateRef (M.insert leaf new st)
  pokeBits w pOut outBits

hsGuruGallinaReset :: IO ()
hsGuruGallinaReset = writeIORef stateRef (rtInit runtime)

hsGuruGallinaConfig :: CULLong -> CInt -> IO ()
hsGuruGallinaConfig seed zero = writeIORef seedRef (fromIntegral seed, zero /= 0)

foreign export ccall "hs_guru_gallina_call" hsGuruGallinaCall :: CInt -> CInt -> CLLong -> Ptr Word32 -> Ptr Word32 -> IO ()
foreign export ccall "hs_guru_gallina_reset" hsGuruGallinaReset :: IO ()
foreign export ccall "hs_guru_gallina_config" hsGuruGallinaConfig :: CULLong -> CInt -> IO ()

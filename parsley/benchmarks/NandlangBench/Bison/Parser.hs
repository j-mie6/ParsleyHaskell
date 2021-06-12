{-# LANGUAGE ForeignFunctionInterface #-}
module NandlangBench.Bison.Parser where

import Foreign.C
import Foreign.Ptr
import Data.ByteString
import System.IO.Unsafe

foreign import ccall "parse" c_parse :: Ptr CChar -> CBool

marshall :: ByteString -> CBool
marshall = unsafePerformIO . flip useAsCString (return . c_parse)

nand :: ByteString -> Maybe ()
nand str = if marshall str == 1 then Just () else Nothing
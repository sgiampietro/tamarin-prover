{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_tamarin_prover_utils (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [1,9,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/bin"
libdir     = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/lib/x86_64-osx-ghc-9.2.8/tamarin-prover-utils-1.9.0-GF6vzZf7ldAASd9GaqAcZl"
dynlibdir  = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/lib/x86_64-osx-ghc-9.2.8"
datadir    = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/share/x86_64-osx-ghc-9.2.8/tamarin-prover-utils-1.9.0"
libexecdir = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/libexec/x86_64-osx-ghc-9.2.8/tamarin-prover-utils-1.9.0"
sysconfdir = "/Users/sofiagiampietro/Documents/tamarin-bilinear-pairings/bp-tamarin-source/tamarin-prover/.stack-work/install/x86_64-osx/b6257c784c2bc0020026b0a5507581a4d35623dc1dbd6dc7437d2f158fb4918a/9.2.8/etc"

getBinDir     = catchIO (getEnv "tamarin_prover_utils_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "tamarin_prover_utils_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "tamarin_prover_utils_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "tamarin_prover_utils_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "tamarin_prover_utils_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "tamarin_prover_utils_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'

module Rules.ToolArgs(toolArgsTarget) where

import qualified Rules.Generate
import Development.Shake
import Target
import Context
import Stage
import Expression

import Packages
import Settings
import Hadrian.Oracles.Cabal
import Hadrian.Haskell.Cabal.Type
import System.Directory (canonicalizePath)

-- | @tool-args@ is used by tooling in order to get the arguments necessary
-- to set up a GHC API session which can compile modules from GHC. When
-- run, the target prints out the arguments that would be passed to @ghc@
-- during normal compilation to @stdout@.
--
-- This target is called by the `ghci.sh` script in order to load all of GHC's
-- modules into GHCi.
allDeps :: Action ()
allDeps = do
   do
    -- We can't build DLLs on Windows (yet). Actually we should only
    -- include the dynamic way when we have a dynamic host GHC, but just
    -- checking for Windows seems simpler for now.
    let fake_target = target (Context Stage0 compiler (if windowsHost then vanilla else dynamic))
                             (Ghc ToolArgs Stage0) [] ["ignored"]

    -- need the autogenerated files so that they are precompiled
    includesDependencies Stage0 >>= need
    interpret fake_target Rules.Generate.compilerDependencies >>= need

    root <- buildRoot
    let dir = buildDir (vanillaContext Stage0 compiler)
    need [ root -/- dir -/- "Config.hs" ]
    need [ root -/- dir -/- "Parser.hs" ]
    need [ root -/- dir -/- "Lexer.hs" ]
    need [ root -/- dir -/- "GHC" -/- "Cmm" -/- "Parser.hs" ]
    need [ root -/- dir -/- "GHC" -/- "Cmm" -/- "Lexer.hs"  ]

    -- Find out the arguments that are needed to load a module into the
    -- session


toolTargets :: [Package]
toolTargets = [ array
             , bytestring
             , templateHaskell
             , containers
             , deepseq
             , directory
             , exceptions
             , filepath
             , compiler
             , ghcCompact
             , ghcPrim
             --, haskeline
             , hp2ps
             , hsc2hs
             , pretty
             , process
             , rts
             , stm
             , time
             , unlit
             , xhtml ]

dirMap :: Action [(FilePath, (Package, [String]))]
dirMap =do
  auto <- concatMapM go toolTargets
  -- Mush the ghc executable into the compiler component so the whole of ghc is not built when
  -- configuring
  manual <- mkGhc
  return (auto ++ [manual])

  where
    mkGhc = do
      let c = (Context Stage0 compiler (if windowsHost then vanilla else dynamic))
      cd <- readContextData c
      fp <- liftIO $ canonicalizePath "ghc/"
      return (fp, (compiler, "-ighc" : modules cd ++ otherModules cd ++ ["ghc/Main.hs"]))
    go p = do
      let c = (Context Stage0 p (if windowsHost then vanilla else dynamic))
      cd <- readContextData c
      ids <- liftIO $ mapM canonicalizePath [pkgPath p </> i | i <- srcDirs cd]
      return $ map (,(p, modules cd ++ otherModules cd)) ids

toolArgsTarget :: Rules ()
toolArgsTarget = do
  phonys (\s -> if "tool:" `isPrefixOf` s then Just (toolRuleBody (drop 5 s)) else Nothing)

toolRuleBody :: FilePath -> Action ()
toolRuleBody fp = do
  mm <- dirMap
  cfp <- liftIO $ canonicalizePath fp
  case find (flip isPrefixOf cfp . fst) mm  of
    Just (_, (p, extra)) -> mkToolTarget extra p
    Nothing -> fail $ "No prefixes matched " ++ show fp ++ " IN\n " ++ show mm

mkToolTarget :: [String] -> Package -> Action ()
mkToolTarget es p = do
    allDeps
    let fake_target = target (Context Stage0 p (if windowsHost then vanilla else dynamic))
                        (Ghc ToolArgs Stage0) [] ["ignored"]
    arg_list <- interpret fake_target getArgs
    liftIO $ putStrLn (intercalate "\n" (arg_list ++ es))



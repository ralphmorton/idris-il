
module IRTS.IL where

import IRTS.IL.Gen (generateIL)

import Idris.AbsSyntax
import IRTS.Compiler
import Idris.Core.TT
import Idris.ElabDecls
import Idris.Options
import Idris.Main
import Idris.ModeCommon
import Idris.REPL

import System.Environment
import System.Exit

il :: IO ()
il = do
    opts <- getOpts
    case null (inputs opts) of
        True -> error "Invalid usage"
        False -> runMain (gen opts)

--
--
--

data Opts = Opts {
    inputs :: [FilePath],
    output :: FilePath
}

getOpts :: IO Opts
getOpts = do
    xs <- getArgs
    return $ process (Opts [] "a.il") xs
    where
    process opts ("-o":o:xs) = process (opts { output = o }) xs
    process opts (x:xs) = process (opts { inputs = x:inputs opts }) xs
    process opts [] = opts

--
--
--

gen :: Opts -> Idris ()
gen (Opts ins out) = do
    elabPrims
    loadInputs ins Nothing
    mainP <- elabMain
    ir <- compile (Via IBCFormat "il") out (Just mainP)
    runIO (generateIL ir)

-- 
-- Main module for lazy amortized analysis
-- pbv, 2012--2015
--
module Main where

import Term
import Parser
import Pretty
import DamasMilner
import Analysis
import Options
import Cost
import Text.Parsec
import System.Exit
import System.Environment
import Control.Monad
import Data.LinearProgram
import qualified Data.Map as Map
 
      
main = do arg0 <- getProgName 
          argv <- getArgs
          (opts, argv') <- parseOpts arg0 argv
          case argv' of
            [] ->  do txt<-getContents
                      analyse opts (runParser toplevel 0 "stdin" txt)
            (f:_) -> do txt<-readFile f 
                        analyse opts (runParser toplevel 0 f txt)
               

analyse opts (Left err) = print err >> exitFailure
analyse opts (Right e') 
  = case hm_inference e' of
  Right (e :@ t) -> do 
          putStrLn ""
          putStrLn "-- Amortised type analysis " 
          putStrLn ("-- Cost model: " ++ show (costName $ optCostModel opts))
          let (typ, lp) = aa_inference opts e t
          putStrLn "-- LP metrics follow"
          putStrLn ("--  # constraints: " ++ show (length $ constraints lp))
          putStrLn ("--  # variables  : " ++ show (Map.size $ allVars lp))
          putStrLn ""
          putStrLn "-- Invoking LP solver"
          typ' <- aa_solve (typ,lp)
          putStrLn "\n-- Annotated typing"
          print typ'
  Left err -> putStrLn err >> exitFailure


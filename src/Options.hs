module Options where

import Cost 
import System.Console.GetOpt

-- command-line options
data Options = Options { optVerbose :: Bool
                       , optRecRule :: Int
                       , optCostModel :: CostModel
                       } deriving Show

defaultOptions = Options { optVerbose=False, 
                           optRecRule = 2,
                           optCostModel = zero
                         }
      
options = 
  [ Option ['r'] ["rec"]
    (ReqArg (\a opts -> opts { optRecRule = read a }) "[0|1|2]") 
    "specify recursion type rule"
  , Option ['v'] ["verbose"]
    (NoArg (\opts -> opts { optVerbose = True }))
    "turn on verbose output"
  , Option ['c'] ["cost"]
    (ReqArg
     (\a opts -> opts { optCostModel = lookupCost a }) names)
    "specify cost model"
  ]
  where names = show (map costName models)



lookupCost :: String -> CostModel
lookupCost arg
  = head ([cm | cm <- models, costName cm == arg ] ++
          error ("invalid cost model: " ++ show arg))


parseOpts arg0 argv = 
  case getOpt Permute options argv of
    (o,n,[]) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError $ userError (concat errs ++ usageInfo header options)
      where header = "usage: " ++ arg0 ++ " [OPTIONS] [file]"



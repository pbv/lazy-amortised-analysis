--
--  Parametric cost constants
--
module Cost where

data CostModel
  = CostModel
    { costName :: String
    , costVar :: !Int
    , costLet :: !Int
    , costLetcons :: !Int
    , costApp :: !Int
    , costMatch :: !Int
    , costPrim :: !Int
    } deriving Show


-- | various cost models
models :: [CostModel]
models = [zero, steps, allocs, apps, prims]

-- count nothing; zero element
zero = CostModel "zero" 0 0 0 0 0 0

-- count evaluation steps: a unit cost for everything
steps = CostModel "steps" 1 1 1 1 1 1

-- count allocations
allocs = zero { costName = "allocs", costLet=1, costLetcons=1 }

-- count forced thunks
-- thunks = zero { costName = "thunks", costVar=1 }

-- count forced thunks
apps = zero { costName = "apps", costApp=1 }

prims = zero { costName = "prims", costPrim = 1}

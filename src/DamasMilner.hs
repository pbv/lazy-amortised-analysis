{- 
 - Damas-Milner type inference for amortised lazy analysis
 -
 - Pedro Vasconcelos, 2012
-}
module DamasMilner where

import Term
import Types
import Pretty
import Text.PrettyPrint.HughesPJ (render)
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Error

-- type schemes
newtype HMscheme = Gen ([TVar], HMtype) deriving (Eq,Show)

-- inject a type into a scheme 
nogen :: HMtype -> HMscheme
nogen t = Gen ([], t)

gen :: [TVar] -> HMtype -> HMscheme
gen vs t = Gen (vs, t)

-- Hindley-Milner context assigning types schemes to variables
type HMcontext = [(Ident, HMscheme)]

-- a monad for Hindler-Milner type inference/checking 
-- combination of state and failure 
type Tc = StateT TcState (Either String)

-- type checking state: fresh var generation and current unifier 
data TcState = TcState { counter :: Int,  unifier :: HMsubst }
             deriving (Eq, Show)


-- generate fresh variables
freshvars :: Int -> Tc [TVar]
freshvars n = do i <- gets counter
                 modify $ \s -> s {counter=counter s+n} 
                 return ['t':show n | n<-[i..i+n-1]]

freshvar :: Tc TVar
freshvar = liftM head (freshvars 1)

-- lookup in context and instantiate type scheme 
lookupTc :: Ident -> HMcontext -> Tc HMtype
lookupTc x ctx 
  = case lookup x ctx of
    Nothing -> throwError ("unbound variable: " ++ show x)
    Just (Gen (vs,t)) -> do vs' <- freshvars (length vs)
                            let s = Map.fromList $ zip vs (map TyVar vs')
                            return (appsubst s t)


-- assert a unification constraint
unify :: HMtype -> HMtype -> Tc ()
unify t1 t2 = do u <- gets unifier
                 case unifyEqs u [(t1, t2)] of
                   Left err -> throwError err
                   Right u' -> modify $ \s -> s {unifier=u'}

-- unification algorithm
-- takes the current unifier and a list of term equations 
-- result is extended unifier or failure
unifyEqs :: HMsubst -> [(HMtype, HMtype)] -> Either String HMsubst
unifyEqs s [] = return s 
unifyEqs s ((t,t'):eqs) = unifyEqs' s (appsubst s t) (appsubst s t') eqs

-- worker function to unify two types and more equations
-- pre-condition: substitution has been applyed to the types
unifyEqs' s TySelf TySelf eqs 
  = unifyEqs s eqs

unifyEqs' s t@(TyCon c) t'@(TyCon c') eqs
  | c==c'     = unifyEqs s eqs
  | otherwise = throwError $
                unlines ["type mismatch:", 
                         render (pretty t), 
                         render (pretty t')]
       
unifyEqs' s (TyVar x) (TyVar y) eqs 
  = case compare x y of   -- fix bindings from higher to lower variables
    EQ -> unifyEqs s eqs
    LT -> unifyEqs (extend y (TyVar x) s) eqs
    GT -> unifyEqs (extend x (TyVar y) s) eqs

unifyEqs' s v@(TyVar x) t eqs 
  | x `notElem` typevars t = unifyEqs (extend x t s) eqs
  | otherwise = throwError $ unlines ["occur check failed:",
                                      render (pretty v),
                                      render (pretty t)]


unifyEqs' s t (TyVar x) eqs = unifyEqs' s (TyVar x) t eqs

unifyEqs' s (TyFun _ t1 t2) (TyFun _ t1' t2') eqs
  = unifyEqs s ((t1,t1'):(t2,t2'):eqs)

unifyEqs' s (TyThunk _ t) (TyThunk _ t') eqs
  = unifyEqs s ((t,t'):eqs)

unifyEqs' s t@(TyRec alts) t'@(TyRec alts') eqs 
  | length alts==length alts' =  unifyAlts s alts alts' eqs
  | otherwise = throwError $ unlines ["rec type mismatch (different number of alternatives):", 
                                      render (pretty t),
                                      render (pretty t')]


unifyEqs' s t@(TyTup ts) t'@(TyTup ts') eqs
  | length ts == length ts' = unifyEqs s (zip ts ts' ++ eqs)
  | otherwise = throwError $ unlines ["tuple mismatch (different number of alternatives):",
                                      render (pretty t), render (pretty t')]
  
-- distinct type structures
unifyEqs' s t t' eqs  = throwError $ unlines ["type mismatch:", 
                                              render (pretty t), 
                                              render (pretty t')]

-- unify branches of two recursive types
-- precondition: the number of alternatives is equal
unifyAlts s [] [] eqs = unifyEqs s eqs
unifyAlts s ((c,_,t):alts) ((c',_,t'):alts') eqs
  | c==c' = unifyAlts s alts alts' ((t,t'):eqs)
  | otherwise = throwError $
                "type alternatives mismatch: " ++ c ++ ", " ++ c'
       
unifyAlts s _ _ _ = error "unifyAlts: diff number of alternatives"
                
                      
-- extend a type substitution maintaining idempotency
extend :: TVar -> HMtype -> HMsubst -> HMsubst 
extend v t s = Map.insert v t $ Map.map (appsubst s') s
  where s' = Map.singleton v t

--
-- Damas-Milner type inference
-- takes a context and term; 
-- computes the Hindley-Milner annotated term
-- discards annotations in the original term                   
--                   
hm_infer :: HMcontext -> Term () -> Tc (Term HMtype)

hm_infer ctx (Var x) 
  = do t <- lookupTc x ctx
       a <- freshvar
       unify t (hmthunk (tyvar a))
       return (Var x :@ tyvar a)

hm_infer ctx (Lambda x e)
  = do a <- freshvar
       let ctx' = (x, nogen (hmthunk (tyvar a))):ctx
       (e' :@ t) <- hm_infer ctx' e
       return (Lambda x e' :@ (hmthunk (tyvar a) ~> t))
           
hm_infer ctx (App e y) 
  = do t1 <- lookupTc y ctx
       (e' :@ te) <- hm_infer ctx e
       b <- freshvar
       unify te (t1 ~> tyvar b)
       return (App (e':@te) y :@ tyvar b)
       
hm_infer ctx (ConsApp c ys)
  = do (TyFun _ t' t) <- lookupTc c ctx
       targs <- sequence [lookupTc y ctx | y<-ys]
       unify t' (tuple targs)
       return (ConsApp c ys :@ t)

hm_infer ctx (Let x e1 e2)
  = do a <- freshvar
       let ctx' = (x, nogen (hmthunk (tyvar a))):ctx
       (e1' :@ t1) <- hm_infer ctx' e1
       unify (tyvar a) t1
       (e2' :@ t2) <- hm_infer ctx' e2
       return (Let x (e1':@t1) e2' :@ t2)

hm_infer ctx (Match e0 alts Nothing)
  = do (e0' :@ t0) <- hm_infer ctx e0
       a <- freshvar
       alts' <- hm_infer_alts ctx alts t0 (tyvar a)
       return (Match (e0':@t0) alts' Nothing :@ tyvar a)
           
hm_infer ctx (Match e0 alts (Just e1))
  = do (e0' :@ t0) <- hm_infer ctx e0
       (e1' :@ t1) <- hm_infer ctx e1
       alts' <- hm_infer_alts ctx alts t0 t1       
       return (Match (e0':@t0) alts' (Just e1') :@ t1)
       
-- constants       
hm_infer ctx (Const n)
  = return (Const n :@ hmint)

-- primitive operations
-- looks type in the context as if it were a curried function
hm_infer ctx (PrimOp op x y)
  = do TyThunk _ (TyFun _ tx (TyFun _ ty t)) <- lookupTc op ctx
       tx' <- lookupTc x ctx
       ty' <- lookupTc y ctx
       unify tx tx'
       unify ty ty'
       return (PrimOp op x y :@ t)

hm_infer ctx (Coerce a@(t',_) e) 
  = do (e' :@ t) <- hm_infer ctx e        
       -- ensure the annotated type has the same HM structure       
       let t'' = fmap (\_ -> ()) t'
       unify t t''
       return (Coerce a e' :@ t)
       

hm_infer ctx _ = error "hm_infer: invalid argument"


hm_infer_alts ctx alts t0 t1
  = sequence [ do { TyFun _  (TyTup ts) t <- lookupTc c ctx
                  ; guard (length xs == length ts)
                  ; unify t0 t
                  ; let ctx' = zip xs (map nogen ts) ++ ctx
                  ; (e' :@ t') <- hm_infer ctx' e 
                  ; unify t1 t'
                  ; return (c, xs, e') 
                  }  | (c,xs,e) <- alts]


-- perform HM type inference and annotate the term with types
hm_inference :: Term () -> Either String (Term HMtype) 
hm_inference e 
  = do (e',tc) <- runStateT (hm_infer prelude e) tc0        
       return (let s = unifier tc 
               in fmap (appsubst s) e')
  where  -- initial state for the type checker 
    tc0 = TcState { counter=0, unifier = Map.empty }


-- types for primitive integers, Peano naturals and lists

-- initial typing context 
prelude :: HMcontext
prelude = [ 
  ("True", nogen (unit ~> hmbool)),
  ("False", nogen (unit ~> hmbool)),
  ("Succ", nogen (tuple [hmthunk hmnat] ~> hmnat)),
  ("Zero", nogen (unit ~> hmnat)),
  ("Cons", gen [a] (tuple [hmthunk (tyvar a), 
                           hmthunk (hmlist (tyvar a))] ~> hmlist (tyvar a))),
  ("Nil", gen [a] (unit ~> hmlist (tyvar a))) ,
  ("Pair", gen [a,b] (tuple [hmthunk (tyvar a), hmthunk (tyvar b)] ~>
                      hmpair (tyvar a) (tyvar b))),
  ("Just", gen [a] (tuple [hmthunk (tyvar a)] ~> hmmaybe (tyvar a))),
  ("Nothing", gen [a] (unit ~> hmmaybe (tyvar a))),
  ("Branch", gen [a] (tuple [hmthunk (hmtree (tyvar a)),
                             hmthunk (hmtree (tyvar a))] ~> hmtree (tyvar a))),
  ("Leaf", gen [a] (tuple [hmthunk (tyvar a)] ~> hmtree (tyvar a)))
  ] 
  ++ -- arithmetic 
  [ (op, nogen (hmthunk (hmthunk hmint ~> hmthunk hmint ~> hmint))) 
     | op <- ["+", "-", "*", "//", "%"]]
  ++ -- comparisons
  [ (op, nogen (hmthunk (hmthunk hmint ~> hmthunk hmint ~> hmbool)))
     | op <- ["<", "<=", ">", ">=", "==", "/="]]
  where a = "a"
        b = "b"
        

{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
--
-- Lazy Amortized Analysis
--
module Analysis where

import           Prelude hiding (Num(..))
import           Algebra.Classes hiding (zero)

import           Term
import           Types
import           DamasMilner
import           Control.Monad.State
import           Control.Monad.Reader
import           Data.LinearProgram hiding (Var,zero)
import           Data.LinearProgram.GLPK.Solver
import           Control.Monad.LPMonad hiding (Var)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (transpose, partition, nubBy)
import           Data.Char (isSymbol)
import           Options
import           Cost (CostModel(..))
import           Debug.Trace  


-- | typing contexts for annotated types
type Context a = [(Ident,TyExp a)]

-- | context for the lazy amortized analysis
type Acontext = Context Ann

-- | a monad for constructing linear programs
type CLP = LPT Ann Int (StateT Ann (Reader Options))

-- | fixed zero annotation variable
zero_ann :: Ann
zero_ann = Ann 0

zero :: LinFunc Ann Int
zero = linCombination []

-- | singleton annotation variables
var :: Ann -> LinFunc Ann Int
var x = linCombination [(1,x)]

-- | sum a list of annotations
vars :: [Ann] -> LinFunc Ann Int
vars xs = linCombination $ zip (repeat 1) xs

-- | generate a fresh annotation variable
fresh_ann :: CLP Ann
fresh_ann = do a <- lift (do {modify succ; get})
               varGeq a 0  -- impose non-negativity
               return a
           

-- | decorate a type with fresh anotation variables
decorate_type :: TyExp a -> CLP Atype
decorate_type (TyVar x) = return (TyVar x)
decorate_type (TyThunk _ t) 
  = do q <- fresh_ann
       t'<- decorate_type t
       return (TyThunk q t')
                              
decorate_type (TyFun _  t1 t2) 
  = do p <- fresh_ann
       t1' <- decorate_type t1
       t2' <- decorate_type t2
       return (TyFun p t1' t2')
       
decorate_type (TyTup ts) = liftM TyTup (mapM decorate_type ts)

decorate_type (TyRec talts) 
  = do talts' <- sequence [ do { t'<-decorate_type t 
                               ; q <- fresh_ann
                               ; return (c, q, t') } 
                          | (c,_,t)<-talts]
       return (TyRec talts')
       
decorate_type TySelf = return TySelf       
decorate_type (TyCon b) = return (TyCon b)


-- | decorate a term with annotation variables
decorate_term :: Term HMtype -> CLP (Term Atype)
decorate_term (Var x) = return (Var x)

decorate_term (Lambda x e) 
  = do e' <- decorate_term e
       return (Lambda x e')
       
decorate_term (App e y) 
  = do e' <- decorate_term e
       return (App e' y)
       
decorate_term (ConsApp c ys) 
  = return (ConsApp c ys)

decorate_term (Let x e1 e2)    
  = do e1'<- decorate_term e1
       e2'<- decorate_term e2
       return (Let x e1' e2')
       
decorate_term (Match e0 alts (Just e1))
  = do e0' <- decorate_term e0
       alts' <- sequence [do {e'<-decorate_term e; return (c,xs,e')} 
                         | (c,xs,e)<-alts]
       e1' <- decorate_term e1
       return (Match e0' alts' (Just e1'))

decorate_term (Match e0 alts Nothing)
  = do e0' <- decorate_term e0
       alts' <- sequence [do {e'<-decorate_term e; return (c,xs,e')} 
                         | (c,xs,e)<-alts]
       return (Match e0' alts' Nothing)
       
-- | primitive operations       
decorate_term (Const n)       = return (Const n)
decorate_term (PrimOp op x y) = return (PrimOp op x y)

decorate_term (Coerce a e) 
  = do e' <- decorate_term e
       return (Coerce a e')

-- | annotations  
decorate_term (e :@ t) 
  = do e' <- decorate_term e
       t' <- decorate_type t 
       return (e' :@ t')


-- | sharing relation between types
-- pre-condition: types have the same Hindley-Milner structure       
share :: Atype -> [Atype] -> CLP ()
share _ [] = return ()

-- thunks
share (TyThunk q t0) ts 
  = do sequence_ [ do { var qi `geq` var q  
                      -- ; (var qi - var q) `geq` (var qi' - var q')
                      }
                 | TyThunk qi ti <- ts]
       share t0 [ ti | TyThunk qi ti <- ts]
       
-- function types
share (TyFun q a b) ts
  =  sequence_ [ do { var qi `geq` var q
                    --; (var qi ^-^ var q) `geq` (var qi' ^-^ var q')
                    ; share ai [a]
                    ; share b [bi]
                    }
               | TyFun qi ai bi <- ts]
       

-- tuples (ShareVec)
-- TODO: verify this!
share (TyTup as) ts
  = sequence_ [ share a bs | (a,bs) <- zip as (transpose bss) ]
    where bss = [bs | TyTup bs <- ts]
          

-- recursive types (ShareDat)
-- TODO: verify this!
share (TyRec alts) ts   
  = do sequence_ [ share a bs | (a,bs)<-zip as (transpose bss)]
       sequence_ [ var p `geq` vars qs  
                 | (p,qs) <- zip ps (transpose qss)]
    where bss = [[b | (c,q,b)<-alts'] | TyRec alts'<-ts]
          qss = [[q | (c,q,b)<-alts'] | TyRec alts'<-ts]
          as = [ a | (c,p,a) <- alts]
          ps = [ p | (c,p,a) <- alts]
          
share TySelf ts    = return ()

share (TyCon b) ts = return ()

share (TyVar x) ts = return ()


-- | subtyping is a special case of sharing
subtype, equaltype :: Atype -> Atype -> CLP ()
t1 `subtype` t2 = share t1 [t2]

-- NB: the following is not needed 
t1 `equaltype` t2 = do t1 `subtype` t2; t2 `subtype` t1

-- | sharing a context against itself
share_self :: Acontext -> CLP ()
share_self ctx = sequence_ [share t [t,t] | (x,t)<-ctx]


-- | split a context for typing a subexpression
split_context :: Acontext -> CLP (Acontext, Acontext)
split_context ctx 
  = let newctx = sequence [do {t'<-decorate_type t; return (x,t')}
                          | (x,t)<-ctx]
    in do ctx1 <- newctx
          ctx2 <- newctx
          sequence_ [ share t [t1,t2] | 
                      (t,t1,t2)<-zip3 (map snd ctx) (map snd ctx1) (map snd ctx2)]
          return (ctx1, ctx2)


-- | trim context to vars with free occurences in a term
trim_context :: Term b -> Context a -> Context a
trim_context e  
  = filter (\(x,_) -> x`Set.member`vars) . nubBy (\(x,_) (y,_) -> x==y)
  where vars = freevars e
    

-- relax cost annotations
-- if \Gamma |-p0/p0'- e : C then  \Gamma |-p/p'- e : C
relaxcost :: (LinFunc Ann Int, LinFunc Ann Int) ->
             (LinFunc Ann Int, LinFunc Ann Int) -> CLP ()
(p,p') `relaxcost` (p0,p0') = do {p `geq` p0;  (p - p0) `geq` (p' - p0')}



-- | lower recursive thunk costs on a \mu-type
-- identity for other types
-- assumes types have the same structure
lower_thunks :: Atype -> Atype -> CLP ()
lower_thunks (TyRec alts) (TyRec alts') 
    = sequence_ [ do { var q `equal` var q'  -- equal potential
                   ; zipWithM_ lower ts ts'
                   }
              | ((c, q, TyTup ts), 
                 (c', q', TyTup ts')) <-zip alts alts', 
                c ==c'  -- must have same constructors
              ]
  where
    lower (TyThunk p  TySelf) (TyThunk q TySelf) -- lower recursive thunks only
      = do { var p `leq` var q 
           -- ; (var p ^-^ var p') `leq` (var q ^-^ var q')
           }
    lower t t' = t `equaltype` t'   -- other cases 
---
lower_thunks t t' = t`equaltype`t'

-- lookup a name in a context
lookupId :: Ident -> Context a -> TyExp a                         
lookupId x ctx  
  = case lookup x ctx of
    Nothing -> error ("unbound identifier: "++show x)
    Just t -> t
                         
-- as above but enforces sharing and returns remaining context
lookupShare :: Ident -> Acontext -> CLP (Atype,Acontext)
lookupShare x ctx
  = case span (\(x',_) -> x'/=x) ctx of
    (_, []) -> error ("unbound identifier: "++show x)
    (ctx', (_,t):ctx'') -> do t1 <-decorate_type t
                              t2 <- decorate_type t
                              share t [t1,t2]
                              return (t1, ctx' ++ (x,t2):ctx'')


-- get a cost model constant
askC :: (CostModel -> Int) -> CLP Int
askC k = fmap k $ asks optCostModel


  
--  Amortised Analysis 
-- collects linear constraints over annotations

aa_infer :: Acontext -> Term Atype -> Atype -> Ann -> Ann -> CLP ()
-- Var rule
aa_infer ctx (Var x) t p p' 
  = let TyThunk q t' = lookupId x ctx 
    in do -- pe <- fresh_ann
          k <- askC costVar
          ((var p - var p') - var q) `equalTo` k
          -- (var pe, var p') `relaxcost` (var q, zero)  -- allow relaxing 
          t' `subtype` t                          -- allow subtyping

-- Abs rule
-- allow prepaying for the argument
aa_infer ctx (Lambda x e) (TyFun q t t') p p'
  = do share_self (trim_context e ctx)
       var p `geq` var p' -- allow relaxing
       aa_infer_prepay [(x,t)] ctx e t' q zero_ann

-- App rule
aa_infer ctx (App (e :@ te) y) t0 p p'
  | TyFun q t' t <- te
  =  do (ty, ctx') <- lookupShare y ctx 
        pe <- fresh_ann
        -- pe' <- fresh_ann
        aa_infer ctx' e te pe p'
        -- allow subtyping the argument and result
        ty `subtype` t'
        t `subtype` t0
        k <- askC costApp
        ((var p - var pe) - var q) `equalTo` k
        -- allow relaxing
        -- (var p, var p') `relaxcost` (var pe ^+^ var q, var pe')

-- Letcons rule (SJ's proposal with PBV fix)
aa_infer ctx (Let x (e1 :@ tA) e2) tC p p'
  | ConsApp c ys <- e1
      = let TyRec talts = tA
            qc = head ([qc | (c', qc, tc)<-talts, c'==c] ++
                       error ("tag missing in rec-type: " ++ show c))
        in do r <- asks optRecRule
              pe <- fresh_ann
              tA'<- decorate_type tA
              share tA [tA, tA']
              (tA0, _) <- aa_rectype tA' zero_ann
              (ctx1,ctx2) <- split_context ctx
              aa_infer_cons ((x,TyThunk zero_ann tA0):ctx1) e1 tA 
              aa_infer ((x,TyThunk zero_ann tA):ctx2) e2 tC pe p'
              k <- askC costLetcons
              ((var p - var pe) - var qc) `equalTo` k
          

-- Let rule 
aa_infer ctx (Let x (e1 :@ tA) e2) tC p p'
  = do r <- asks optRecRule
       tA' <- decorate_type tA
       share tA [tA, tA']
       q <- fresh_ann
       pe <- fresh_ann
       (tA0,q0) <- aa_rectype tA' q
       k <- askC costLet
       (var p - var pe) `equalTo` k
       (ctx1, ctx2) <- split_context ctx
       aa_infer ((x,TyThunk q0 tA0):ctx1) e1 tA q zero_ann
       aa_infer_prepay [(x,TyThunk q tA)] ctx2 e2 tC pe p'


-- Match rule
aa_infer ctx (Match (e0 :@ t0) alts other) t p p''
  = do pe <- fresh_ann
       p' <- fresh_ann
       k <- askC costMatch
       (var p - var pe) `equalTo` k
       (ctx1,ctx2) <- split_context ctx
       aa_infer ctx1 e0 t0 pe p'
       aa_infer_alts ctx2 alts t0 t p' p''
       case other of
         Nothing -> return ()
         Just e -> aa_infer ctx2 e t p' p''

-- Constants           
aa_infer ctx (Const n) t p p'   -- t must be hmint
  = var p `geq` var p' -- allow relaxing

-- Primitive operations
-- TODO: can we allow potential in the result type? I think not!
aa_infer ctx (PrimOp op x y) t p p'
  = let TyThunk q0 tx = lookupId x ctx  -- no need for sharing here!
        TyThunk q1 ty = lookupId y ctx
    in do k <- askC costPrim
          q <- fresh_ann
          var q `equalTo` k
          share t [t,t]  -- no potential
          (var p, var p') `relaxcost` (var q + var q0 + var q1, zero)
       

-- user annotations and constraints
-- checking that t and t' match is done during Damas-Milner inference
aa_infer ctx (Coerce (t,cs) e) t' p p'
  = let s = Map.fromList $ zip (annotations t) (annotations t')
        ren x = Map.findWithDefault undefined x s
    in do sequence_ [ constrain lf' bds 
                    | Constr _ lf bds <- cs, 
                      let lf' = Map.mapKeys ren lf
                    ]
          aa_infer ctx e t' p p'


aa_infer ctx e t p p' = error ("aa_infer: undefined for " ++ show e)

-- auxiliary function to choose the recursive type for let/letcons
aa_rectype tA q = do
  r <- asks optRecRule  -- which recursive typeing rule are we using?
  case r of
    0 -> return (tA, zero_ann) -- ICFP'2012 paper
    1 -> return (tA, q)        -- Hugo's thesis
    2 -> do t <- decorate_type tA
            lower_thunks t tA
            return (t, zero_ann)  -- ESOP'2015 paper
    _ -> error "aa_rectype: invalid optRecRule"

------------------------------------------------------------------

-- auxiliary function for match alternatives
-- allow prepaying for pattern variables
-- should improve quality over the original ICFP submission 
aa_infer_alts ctx alts t@(TyRec talts) t' p' p'' = mapM_ infer alts
  where infer (c, xs, e) = do
          pe' <- fresh_ann
          pe'' <- fresh_ann
          aa_infer_prepay (zip xs ts) ctx e t' pe' pe''
          -- var pe' `equal` (var p' ^+^ var q)
          -- (var p', var p'') `relaxcost` (var pe' ^+^ var q, var pe'')
          var pe' `leq` (var p' + var q)
          var pe'' `geq` var p''
          where (q,TyTup ts) = head ([ (q, recsubst t t') 
                                     | (c',q,t')<-talts, c'==c] ++
                                     error ("wrong match alternative: "++show c))
aa_infer_alts ctx alts t t' p' p'' 
  = error "aa_infer_alts: invalid type"




--
-- allow the prepay for all variables in the first context
-- followed by type inference
aa_infer_prepay :: Acontext -> Acontext -> 
                   Term Atype -> Atype -> Ann -> Ann -> CLP ()
aa_infer_prepay [] ctx e t' p p' = aa_infer ctx e t' p p'
aa_infer_prepay ((x,TyThunk q t) : ctx1) ctx2 e t' p p'
  = do q0 <- fresh_ann
       q1 <- fresh_ann
       p0 <- fresh_ann
       var q `equal` (var q0 + var q1)
       var p `equal` (var p0 + var q1)
       aa_infer_prepay ctx1 ((x,TyThunk q0 t):ctx2) e t' p0 p'
aa_infer_prepay ctx _ e t' p p'
  = error ("aa_infer_prepay: invalid context\n " ++ show ctx)

               
-- auxiliary Cons-rule used at the Letcons 
-- given both context *and* the result type 
-- turnstile annotations are ommitted (always 0)
aa_infer_cons ctx (ConsApp c ys) tB
  | length ys == length ts'    -- should always hold
  = do (ts, _) <- lookupMany ys ctx
       sequence_ [t `subtype` t' | (t,t')<-zip ts ts']
    where TyRec talts = tB    -- pattern-match result type
          TyTup ts' = head [recsubst tB t' | (c',_,t')<-talts, c'==c]
aa_infer_cons ctx _ tB = error "aa_infer_cons: invalid argument"          
        
-- lookup and share many identifiers in sequence
lookupMany :: [Ident] -> Acontext -> CLP ([Atype], Acontext)
lookupMany [] ctx = return ([],ctx)
lookupMany (x:xs) ctx 
  = do (t, ctx') <- lookupShare x ctx
       (ts, ctx'')<- lookupMany xs ctx'
       return (t:ts, ctx'')


-- leave only type annotations for let-bindings
let_annotations :: Term a -> Term a
let_annotations (Let x (e1 :@ t1) e2)
  = Let x (let_annotations e1 :@ t1) (let_annotations e2)
let_annotations (Let x e1 e2) 
  = Let x (let_annotations e1) (let_annotations e2)
let_annotations (Lambda x e)     
  = Lambda x (let_annotations e)
let_annotations (Match e0 alts other)
  = Match (let_annotations e0) alts' other'
  where alts' = [ (c,xs, let_annotations e) | (c,xs,e)<-alts ]
        other' = fmap let_annotations other
let_annotations (App e y) 
  = App (let_annotations e) y
let_annotations (Var x)          = Var x    
let_annotations (ConsApp c ys)   = ConsApp c ys    
let_annotations (PrimOp op x y)  = PrimOp op x y
let_annotations (Const n)        = Const n
let_annotations (Coerce a e)     = Coerce a (let_annotations e) 
let_annotations (e :@ a)         = let_annotations e



-- | toplevel inference 
-- generates a typing \Gamma |-p/p'- e : C 
-- and a linear program for constraints over annotations
-- set p'=0 and solves to minimize p (i.e. the whnf cost of the expression)
aa_inference :: Options -> Term HMtype -> HMtype -> (Typing Ann, LP Ann Int)
aa_inference opts e t
  = flip runReader opts $
    flip evalStateT (Ann 1) $
    runLPT $ 
     do { varEq zero_ann 0
        ; p <- fresh_ann
        ; e'<- decorate_term e
        ; t'<- decorate_type t
        ; setDirection Min
        ; setObjective  (vars (p:annotations t'))
        ; aa_infer [] e' t' p zero_ann
        ; return Typing {aterm = let_annotations e', 
                         atype = t', 
                         ann_in  = p, 
                         ann_out = zero_ann}
        }





-- | solve linear constraints and instantiate annotations
aa_solve :: (Typing Ann, LP Ann Int) -> IO (Typing Double)
aa_solve (typing, lp) 
  = do answer <- glpSolveVars simplexDefaults{msgLev=MsgOff} lp 
       case answer of
         (Success, Just (obj, vars)) -> 
           let subst a = Map.findWithDefault 0 a vars
           in return (fmap subst typing)
         (other, _) -> error ("LP solver failed: " ++ show other)



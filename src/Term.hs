--
-- Abstract syntax for minimal lazy language
-- Pedro Vasconcelos, 2012
--
module Term where

import Types
import Data.LinearProgram hiding (Var)
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

-- identifiers 
type Ident = String

-- terms with sub-terms with annotations `a' 
-- used to keep the type information and 
-- avoid the need for "guessing" during constraint collection
data Term a = Var Ident
            | Lambda Ident (Term a) 
            | App (Term a) Ident
            | Let Ident (Term a) (Term a)
                            -- letcons is a special use case of let
            | Match (Term a) [Alt a] (Maybe (Term a))
                            -- maybe is the "otherwise" alternative
            | ConsApp Cons [Ident]       -- constructor application
            | PrimOp String Ident Ident  -- primitive operations
            | Const !Integer             -- primitive integers
            | Coerce SrcAnn (Term a)   -- source level annotation
            | (Term a) :@ a              -- type checker annotation
            | Ind Ident          -- indirections
            deriving (Show)

-- | match alternatives
type Alt a = (Cons, [Ident], Term a) 

-- | source annotations
type SrcAnn  = (SrcType, [SrcConstr])
type SrcType = TyExp String
type SrcConstr = Constraint String Int


-- instance of Functor for mapping over annotations
instance Functor Term where
  fmap f (Var x)        = Var x
  fmap f (Lambda x e)   = Lambda x (fmap f e)
  fmap f (App e y)      = App (fmap f e) y
  fmap f (ConsApp c ys) = ConsApp c ys
  fmap f (Let x e1 e2)  = Let x (fmap f e1) (fmap f e2)
  fmap f (Match e alts other) = Match (fmap f e) alts' other'
    where alts' = [(c, xs, fmap f e) | (c, xs, e)<-alts]
          other'= fmap (fmap f) other
  -- primitive ops
  fmap f (Const n)       = Const n
  fmap f (PrimOp op x y) = PrimOp op x y
  -- annotations
  fmap f (Coerce a e)    = Coerce a (fmap f e) 
  fmap f (e :@ a)        = fmap f e :@ f a
  fmap f (Ind x)         = Ind x



freevars :: Term a -> Set Ident
freevars (Var x)        = Set.singleton x
freevars (Lambda x e)   = Set.delete x (freevars e)
freevars (App e y)      = Set.insert y (freevars e)
freevars (ConsApp c ys) = Set.fromList ys 
freevars (Let x e1 e2)  = Set.delete x (freevars e1 `Set.union` freevars e2)
freevars (Match e1 alts other) = freevars e1 `Set.union` 
                                 freevars_alts `Set.union` 
                                 maybe Set.empty freevars other
  where freevars_alts = Set.unions [freevars e `Set.difference` 
                                    Set.fromList xs | (c,xs,e)<-alts ]
freevars (Const n)         = Set.empty
freevars (PrimOp op x y)   = Set.fromList [x,y]
freevars (Coerce a e)      = freevars e
freevars (e :@ a)          = freevars e
freevars (Ind x)           = Set.singleton x


-- substitute identifers
rename :: Ident -> Ident -> Term a -> Term a
rename x y e@(Var v) | v==x      = Var y
                     | otherwise = e                                 
rename x y e@(Lambda x' e') 
  | x==x'     = e
  | otherwise = Lambda x' (rename x y e')
rename x y (App e' v) = App (rename x y e') v'
  where v' | v==x      = y
           | otherwise = v
rename x y (ConsApp c xs') 
  = ConsApp c [if x==x' then y else x' | x'<-xs']

rename x y e@(Let x' e1 e2) 
  | x'==x     = e
  | otherwise = Let x' (rename x y e1) (rename x y e2)
  
rename x y (Match e alts other) 
  = Match (rename x y e) (map rename_alt alts) (fmap (rename x y) other)
  where rename_alt alt@(c, xs, e) 
          | x`elem`xs = alt
          | otherwise = (c, xs, rename x y e)
    
rename x y e@(Const n) = e                                   
rename x y e@(PrimOp op x' y') = PrimOp op x'' y''
  where x'' = if x==x' then y else x'
        y'' = if x==y' then y else y'
-- annotations
rename x y (Coerce a e) = Coerce a (rename x y e)  
rename x y (e :@ a) = rename x y e :@ a
rename x y (Ind v) | v==x      = Ind y
                   | otherwise = Ind v



-- | shorthand constructors for non-annotated terms 
lvar x = Var x
lapp e y = App e y
lmatch e0 alts other = Match e0 alts other
lconsapp c ys = ConsApp c ys
llambda x e = Lambda x e
llet x e1 e2 = Let x e1 e2
lconsalt cons xs e = (cons, xs, e) 
lconst n = Const n
lprimop op x y = PrimOp op x y

-- collect all annotations
instance Annotations Term where
  annotations (Var x) = []
  annotations (Lambda x e) = annotations e
  annotations (App e y) = annotations e
  annotations (ConsApp c ys) = []
  annotations (Let x e1 e2) = annotations e1 ++ annotations e2
  annotations (Match e alts other) = annotations e ++
                                     concat [annotations e | (c,xs,e)<-alts] ++
                                     maybe [] annotations other
  annotations (PrimOp op x y) = []                                   
  annotations (Const n) = []
  annotations (Coerce a e) = annotations e
  annotations (e :@ a) = a : annotations e
  annotations (Ind x)  = []


instance Typevars a => Typevars (Term a) where
  typevars = concat . annotations . fmap typevars
    

-- substitute many variables in sequence
renames :: [Ident] -> [Ident] -> Term a -> Term a 
renames (x:xs) (y:ys) e = renames xs ys (rename x y e)
renames [] [] e = e
renames _  _  _ = error "renames: variable lists must have equal length"

-- a global typing with annotations 'a'
data Typing a = Typing { aterm :: Term (TyExp a), 
                         atype :: TyExp a, 
                         ann_in :: a, 
                         ann_out :: a 
                       }
                
instance Functor Typing where
  fmap f (Typing e t p p') = Typing (fmap (fmap f) e) (fmap f t) (f p) (f p')


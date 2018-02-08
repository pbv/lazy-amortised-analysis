{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Types where

import Data.List (union, delete)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (guard)

infixr 4 ~>     -- function type constructor

-- type expressions with annotations 'a' 
data TyExp a = TyVar TVar                    -- variables
             | TyThunk a (TyExp a)           -- thunks
             | TyFun a (TyExp a) (TyExp a)   -- functions
             | TyTup [TyExp a]      -- tuple 
             | TyRec [TyAlt a]      -- recursive type
             | TySelf               -- self-reference in recursive type
             | TyCon TConst         -- atomic types (e.g. Int)
             deriving (Eq,Show)
                          

type TVar = String      -- type variables
type TConst = String    -- atomic types
type Cons = String      -- constructor tags

-- alternatives of recursive types                          
type TyAlt a = (Cons, a, TyExp a)

-- Hindley-Milner types (no annotations)
type HMtype = TyExp ()

-- annotation variables
newtype Ann = Ann Int deriving (Eq,Ord,Enum)

instance Show Ann where
  showsPrec _ (Ann n) = ('a':) . shows n

-- annotated types
type Atype = TyExp Ann




-- auxiliary functions to make simple types
tycon = TyCon
tyvar  = TyVar
tyfun = TyFun
hmfun = TyFun () 
(~>) = hmfun
thunk   = TyThunk
hmthunk = TyThunk ()
hmalt c t = (c, (), t)
rec = TyRec
self = TySelf
tuple = TyTup
unit = TyTup []
pair t1 t2 = TyTup [t1,t2]

hmint = TyCon "Int"

hmbool = rec [hmalt "True" unit, hmalt "False" unit]

hmnat  = rec [hmalt "Succ" (tuple [hmthunk self]), 
              hmalt "Zero" unit]
         
hmlist a = rec [hmalt "Cons" (tuple [hmthunk a, hmthunk self]), 
                hmalt "Nil"  unit]

hmmaybe a = rec [hmalt "Just" (tuple [hmthunk a]),
                 hmalt "Nothing" unit]

hmpair a b = rec [hmalt "Pair" (tuple [hmthunk a, hmthunk b])]


-- overload listing type variables and annotations
class Typevars t where
  typevars :: t -> [TVar]

class Annotations t where
  annotations :: t a -> [a]


instance Typevars (TyExp a) where
  typevars TySelf    = []
  typevars (TyCon _) = []
  typevars (TyVar x) = [x]
  typevars (TyThunk _ t) = typevars t
  typevars (TyFun _ t1 t2) = typevars t1 ++ typevars t2
  typevars (TyRec alts) = concat [typevars t | (c,_,t)<-alts]
  typevars (TyTup ts)   = concatMap typevars ts

instance Annotations TyExp where
  annotations TySelf = []
  annotations (TyCon _) = []
  annotations (TyVar x) =  []
  annotations (TyThunk q t) = q:annotations t
  annotations (TyFun q t1 t2) = q:annotations t1 ++ annotations t2
  annotations (TyRec alts) = concat [q:annotations t | (c,q,t)<-alts]
  annotations (TyTup ts)  = concatMap annotations ts



-- Functor instance to map over annotations
instance Functor TyExp where
  fmap f (TyVar v) = TyVar v
  fmap f (TyThunk q t)= TyThunk (f q) (fmap f t)
  fmap f (TyFun q  t t') = TyFun (f q) (fmap f t) (fmap f t')
  fmap f (TyTup ts) = TyTup (map (fmap f) ts)
  fmap f (TyRec alts) = TyRec [(c,f a, fmap f t) | (c,a,t)<-alts]
  fmap f TySelf = TySelf
  fmap f (TyCon c) = TyCon c
  

-- substitute the recursive self-reference in a type
recsubst :: TyExp a -> TyExp a -> TyExp a
recsubst t TySelf = t
recsubst t (TyVar x) = TyVar x
recsubst t (TyCon b) = TyCon b
recsubst t (TyThunk q t') = TyThunk q (recsubst t t')
recsubst t (TyFun q t1 t2) = TyFun q (recsubst t t1) (recsubst t t2)
recsubst t (TyTup ts) = TyTup (map (recsubst t) ts)
recsubst t (TyRec alts) = TyRec alts



-- type substitutions 
type Tysubst a = Map TVar (TyExp a)
type HMsubst = Tysubst ()


-- apply a substitution to a type
appsubst :: Tysubst a -> TyExp a -> TyExp a 
appsubst s TySelf = TySelf
appsubst s t@(TyCon _) = t
appsubst s t@(TyVar v) = Map.findWithDefault t v s
appsubst s (TyThunk q t') = TyThunk q (appsubst s t')
appsubst s (TyFun q t1 t2) = TyFun q (appsubst s t1) (appsubst s t2)
appsubst s (TyRec alts) = TyRec alts'
  where alts' = [(c,a,appsubst s t) | (c,a,t)<-alts]
appsubst s (TyTup ts) = TyTup (map (appsubst s) ts)
          



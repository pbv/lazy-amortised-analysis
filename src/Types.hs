{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, DeriveFunctor #-}
--
-- Type expressions and annotations
--
module Types where

import Data.List (union, delete)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (guard)

infixr 4 ~>     -- function type constructor

-- | type expressions with annotations 'a' 
data TyExp a
  = TyVar TVar                    -- ^ variables
  | TyThunk a (TyExp a)           -- ^ thunks
  | TyFun a (TyExp a) (TyExp a)   -- ^ functions
  | TyTup [TyExp a]               -- ^ tuple 
  | TyRec [TyAlt a]               -- ^ recursive type
  | TySelf                        -- ^ self-reference in recursive type
  | TyCon TConst                  -- ^ base types (e.g. Int)
  deriving (Eq, Show, Functor)
                          

type TVar = String      -- ^ type variables
type TConst = String    -- ^ basic types
type Cons = String      -- ^ constructor tags

-- | alternatives of recursive types                          
type TyAlt a = (Cons, a, TyExp a)

-- | Hindley-Milner types (without annotations)
type HMtype = TyExp ()

-- | annotated types 
type Atype = TyExp Ann

-- | annotation variables
newtype Ann = Ann Int deriving (Eq,Ord,Enum)

instance Show Ann where
  showsPrec _ (Ann n) = ('a':) . shows n



-- | auxiliary functions to make simple types
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


hmtree a = rec [hmalt "Leaf" (tuple [hmthunk a]),
                hmalt "Branch" (tuple [hmthunk self,
                                       hmthunk self])]

-- | classes for overloading the collection of
-- type variables and annotations
--
class Typevars t where
  typevars :: t -> [TVar]  -- ^ collect all type variables

class Annotations t where
  annotations :: t a -> [a]  -- ^ collect all annotations


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



-- | substitute the recursive self-reference in a type
recsubst :: TyExp a -> TyExp a -> TyExp a
recsubst t TySelf = t
recsubst t (TyVar x) = TyVar x
recsubst t (TyCon b) = TyCon b
recsubst t (TyThunk q t') = TyThunk q (recsubst t t')
recsubst t (TyFun q t1 t2) = TyFun q (recsubst t t1) (recsubst t t2)
recsubst t (TyTup ts) = TyTup (map (recsubst t) ts)
recsubst t (TyRec alts) = TyRec alts


-- | type substitutions 
type Tysubst a = Map TVar (TyExp a)
type HMsubst = Tysubst ()


-- | apply a substitution to a type
appsubst :: Tysubst a -> TyExp a -> TyExp a 
appsubst s TySelf = TySelf
appsubst s t@(TyCon _) = t
appsubst s t@(TyVar v) = Map.findWithDefault t v s
appsubst s (TyThunk q t') = TyThunk q (appsubst s t')
appsubst s (TyFun q t1 t2) = TyFun q (appsubst s t1) (appsubst s t2)
appsubst s (TyRec alts) = TyRec alts'
  where alts' = [(c,a,appsubst s t) | (c,a,t)<-alts]
appsubst s (TyTup ts) = TyTup (map (appsubst s) ts)
          



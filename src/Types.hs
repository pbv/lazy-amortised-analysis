{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable
#-}
--
-- Type expressions and annotations
--
module Types where

import           Data.Foldable (toList)
import           Data.Map (Map)
import qualified Data.Map as Map

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
  deriving (Eq, Show, Functor, Foldable, Traversable)
                          

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


annotations :: Foldable t => t a -> [a]
annotations = toList

-- | collect all type variables
-- generic foldable and for plain type expressions
typevars :: Foldable f => f (TyExp a) -> [TVar]
typevars = foldMap tyvars 

tyvars :: TyExp a -> [TVar]
tyvars TySelf    = []
tyvars (TyCon _) = []
tyvars (TyVar x) = [x]
tyvars (TyThunk _ t) = tyvars t
tyvars (TyFun _ t1 t2) = tyvars t1 ++ tyvars t2
tyvars (TyRec alts) = concat [tyvars t | (c,_,t)<-alts]
tyvars (TyTup ts)   = concatMap tyvars ts


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
          



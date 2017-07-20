-- Pretty printers for terms and types
-- pbv, 2012
module Pretty where

import Term
import Types
import Text.PrettyPrint.HughesPJ
import Data.List(nub,intersperse)
import qualified Data.Map as Map

-- | typeclass to overload showing of annotations
class ShowA a where
  showA :: a -> String        -- a single annotation 
  showAs :: a -> a -> String  -- a pair (thunks and arrows)

instance ShowA () where
  showA _ = ""
  showAs _ _ = ""  

instance ShowA Ann where
  showA a     = "@" ++ show a
  showAs a a' = "@" ++ show a ++ "/" ++ show a'

instance ShowA Double where
  showA q = if iszero q then "" else "@" ++ showRound q
  showAs q q'
      | iszero q && iszero q' = ""
      | otherwise =  "@" ++ showRound q ++ "/" ++ showRound q'


showRound :: Double -> String
showRound x = let r = round x :: Int
              in if iszero (x - fromIntegral r) then
                   show r else show x

iszero :: Double -> Bool
iszero x = abs x < 1e-6


-- | typeclass to overload pretty-printing
class Pretty a where
  prettyPrec :: Int -> a -> Doc
  pretty :: a -> Doc
  pretty = prettyPrec 0
  

instance Pretty a => Pretty (Term a) where
  prettyPrec = prettyTerm
  
instance ShowA a => Pretty (TyExp a) where  
  prettyPrec = prettyType

instance Pretty () where
  prettyPrec n _ = empty

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- | pretty-printing terms
prettyTerm :: Pretty a => Int -> Term a -> Doc
prettyTerm _ (Ind x) = text ('^':x)
prettyTerm _ (Var x) = text x
prettyTerm p (Lambda x e)
  = parensIf (p>3) $ 
    fsep [char '\\' <> hsep (map text (x:args e)), text "->", 
          nest 2 (prettyTerm 2 (body e))]
      where args (Lambda y e) = y : args e
            args e            = []
            body (Lambda y e) = body e
            body e            = e


prettyTerm p (App e y) = prettyTerm 4 e <+> text y
prettyTerm p (ConsApp c ys) 
  = ppConsApp c ys 
prettyTerm p (Let x (e1 :@ a) e2)
  = parensIf (p>3) $
    fsep [ text "let", text x, colon, pretty a,
          nest 2 (sep [equals, prettyTerm 0 e1]),
          text "in", prettyTerm 2 e2
        ]
prettyTerm p (Let x e1 e2)
  = parensIf (p>3) $ 
    fsep [ text "let", text x,
          nest 2 (fsep [equals, prettyTerm 0 e1]), 
          text "in", prettyTerm 2 e2
         ]
prettyTerm p (Match e (alt0:alts) other)    
  = parensIf (p>3) $
    fsep ([text "match", prettyTerm 0 e, text "with"] 
          ++
          ppalt0 : map ppalt alts 
          ++
          --sep (punctuate (char '|') $ map (nest 2 . ppalt) alts),
         maybe [] (\e' -> [text "otherwise", prettyTerm 0 e']) other
         )
      where ppalt (c,xs,e) 
              = fsep [char '|' <+> ppConsApp c xs <+> text "->",
                      nest 2 (prettyTerm 2 e)]
            ppalt0 = 
              let (c,xs,e) = alt0 in
              fsep [ppConsApp c xs <+> text "->", 
                    nest 2 (prettyTerm 2 e)]
                             
prettyTerm p (Const n) = text (show n)                             
prettyTerm p (PrimOp op x y) = hsep [text x, text op, text y]

prettyTerm p (Coerce (t,cs) e) -- TODO: fix this!
  = prettyTerm p e
prettyTerm p (e :@ a) 
  = fsep [prettyTerm p e, colon, pretty a]


prettyTerm p (Ind x) = ppConsApp "ind" [x]


ppConsApp c xs = text c <> parens (hcat $ punctuate comma (map text xs))



-- | pretty-printing annotated types
prettyType :: ShowA a => Int -> TyExp a -> Doc
prettyType _ (TyVar v) = text v
prettyType _ (TyCon c) = text c
prettyType _ TySelf    = char '#'
prettyType _ (TyThunk q t) 
  = text ("T" ++ showA q) <> parens (prettyType 0 t)
    
prettyType p (TyFun q t1 t2)
  = parensIf (p>3) $
    fsep [prettyType 4 t1, 
          nest 2 (ppArrow q), 
          nest 2 (prettyType 3 t2)]
prettyType _ (TyTup ts) 
  = parens (fcat $ punctuate comma $ map (prettyType 0) ts)
prettyType _ (TyRec alts)
  = text "Rec" <> braces (fsep $ intersperse (char '|') $ map p alts)
  where p (c, q, t) = hcat [text (c ++ showA q), colon,
                            prettyType 0 t]

ppArrow q =  text ("->" ++ showA q)




-- | pretty-print typings
instance ShowA a => Pretty (Typing a) where
  prettyPrec _ (Typing e t p p') 
    -- rename all typevars to A, B, C, ...
    = let tvs = nub (typevars e ++ typevars t)
          s = Map.fromList $ zip tvs (map TyVar varnames)
          e' = fmap (appsubst s) e
          t' = appsubst s t
      in fsep [text ("|-"  ++ showAs p p'),
               nest 2 (pretty e'), 
               colon, 
               nest 2 (pretty t')]


-- pretty variables names
varnames :: [String]
varnames = let singles = "abc"
           in [[v] | v<-singles] ++ [v:show n | n<-[1..], v<-singles]
                            
instance ShowA a => Show (Typing a) where
  show t = render (pretty t)




{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE PatternGuards #-}

module Pretty where

import           Data.Bool            (bool  )
import           Data.Functor.Classes (liftEq)
import qualified Data.Text        as   T

import           Syntax
import           Utils  

--------------------------------------------------------------------------------

-- This whole module is utter mess

type Prec = Int

data Assoc
  = LeftAssoc
  | RightAssoc
  | NoneAssoc

precApp, precArr, precTApp, precAppExp, precBind :: Prec

precTApp   = 11
precApp    = 10
precAppExp = 10
precArr    = 4
precBind   = 1

parensIf :: Bool -> String -> String
parensIf cond s = bool s ("(" ++ s ++ ")") cond

cDepth :: Int -> String -> String
cDepth d s = "\ESC[" ++ show (31 + (d `mod` 5)) ++ "m" ++ s ++ "\ESC[0m"

binOpAssoc :: Prec -> Assoc -> (Prec, Prec)
binOpAssoc opP = \case
  LeftAssoc  -> (opP    , opP + 1)
  RightAssoc -> (opP + 1, opP    )
  NoneAssoc  -> (opP + 1, opP + 1)

nameSuffixes :: [String]
nameSuffixes = "" : "′" : "″" : "‴" : map show [(1 :: Int)..]

freshName :: String -> Names -> String 
freshName base nms = findFresh nameSuffixes
  where findFresh = \case
          s : ss -> let lnm = base ++ s in bool (findFresh ss) lnm (LName lnm `notElem` nms)
          []     -> base

idxNameErr :: String -> Names -> Ix -> String

idxNameErr err nms ix = let i = unIx ix in checkBounds err nms "index" i i

checkBounds :: String -> Names -> String -> Int -> Int -> String
checkBounds err nms kind orig i =
  bool (internalErr $ "Out of bounds " ++ err ++ " " ++ kind ++ ": " ++ show orig)
       (unLName (nms !! i))
       (i >= 0 && i < length nms)

idxNmT :: Names -> Ix -> String
idxNmE :: Names -> Ix -> String

idxNmT = idxNameErr "type"
idxNmE = idxNameErr "term"

fmtKindAnn :: Names -> Kind -> String
fmtKindAnn kNms k = " ∷ " ++ ppKind kNms 0 k

fmtTypeAnn :: Names -> Names -> Type -> String
fmtTypeAnn tNms kNms t = " : " ++ ppType tNms kNms 0 t

fmtBinOp :: Prec -> Prec -> String -> String -> String -> String
fmtBinOp p opP sym e e' = parensIf (p > opP) $ e ++ " " ++ sym ++ " " ++ e'

--------------------------------------------------------------------------------

type TyBinds      = [(String,  Maybe Kind)]
type QuantGroups  = [([String], Maybe Kind)]

type Collected  a = (TyBinds, Names, Names, a)
type Quantifier a = Maybe (Quant, Maybe Kind, LName, a)

data Quant
  = QForall
  | QForallK
  deriving Eq

isQuant   :: Type -> Quantifier Type
isQuantNf :: NfT  -> Quantifier NfT

isQuant t = case t of
  TApp op arg -> case (op, arg) of
    (TConst (TForall k), TLam  lnm _ body) -> Just (QForall,  Just k,  lnm, body)
    (TConst  TForallK  , TKLam lnm   body) -> Just (QForallK, Nothing, lnm, body)
    _                                      -> Nothing
  _                                        -> Nothing

isQuantNf = \case
  NfNeu (NfNeuApp op arg) -> case (op, arg) of
    (NfNeuConst (TForall k), NfLam  lnm _ body) -> Just (QForall,  Just k,  lnm, body)
    (NfNeuConst  TForallK  , NfLamK lnm   body) -> Just (QForallK, Nothing, lnm, body)
    _                                           -> Nothing
  _                                             -> Nothing

collectQGen :: (a -> Quantifier a) -> Quant -> Names -> Names -> a -> Collected a
collectQGen isQ q tNms kNms t = case isQ t of
  Just (q', mk, lnm, body) | q == q' ->
    let (lnm', tNms', kNms') = case q of
                                 QForallK -> let l = freshName (unLName lnm) kNms in (l, tNms, LName l : kNms)
                                 _        -> let l = freshName (unLName lnm) tNms in (l, LName l : tNms, kNms)
        (binds, tNms'', kNms'', inner) = collectQGen isQ q tNms' kNms' body
    in  ((lnm', mk) : binds, tNms'', kNms'', inner)
  _                                 -> ([], tNms, kNms, t)

collectQ   :: Quant -> Names -> Names -> Type -> Collected Type
collectQNf :: Quant -> Names -> Names -> NfT  -> Collected NfT

collectQ   = collectQGen isQuant
collectQNf = collectQGen isQuantNf

groupBinds :: TyBinds -> QuantGroups
groupBinds = foldr groupStep []
  where groupStep (n, mk) = \case
          [              ]         -> [([n], mk)]
          (ns, mk') : rest 
            | liftEq eqK mk mk' -> (n : ns, mk) : rest
            | otherwise         -> ([n],    mk) : (ns, mk') : rest
        eqK     k  k'  = case (k, k') of -- We use equality on kinds ONLY HERE, so, I don't think it's reasonable to define Eq instance for Kinds (and we can't derive it because of lnms)
          (KStar        , KStar          ) -> True
          (KArr      a b, KArr      a' b') -> eqK a  a' && eqK b b'
          (KForall _ bk , KForall _ bk'  ) -> eqK bk bk'
          (KVar      i  , KVar      i'   ) -> i == i'
          (KGlobal   g  , KGlobal   g'   ) -> g == g'
          _                                -> False

fmtQuantGroups :: Quant -> Names -> QuantGroups -> String
fmtQuantGroups q kNms = \case
  [g] -> fmtGroup g
  gs  -> unwords [ "(" ++ fmtGroup g ++ ")" | g <- gs ]
  where fmtGroup (ns, mk) = unwords ns ++ case q of
                                            QForallK -> " ∷ ◻"
                                            _        -> maybe " ∷ ◻" (\k -> " ∷ " ++ ppKind kNms 0 k) mk

fmtQuant :: Names -> Prec -> Quant -> TyBinds -> String -> String
fmtQuant kNms p q binds inner = parensIf (p > 0) $ "∀ " ++ fmtQuantGroups q kNms (groupBinds binds) ++ ". " ++ inner

--------------------------------------------------------------------------------

ppKind :: Names -> Prec -> Kind -> String
ppKind kNms p = \case
  KStar         -> "*"
  KArr dom cod  -> parensIf (p > precArr) $ ppKind kNms (precArr + 1) dom ++ " → " ++ ppKind kNms precArr cod
  KVar ix       -> idxNameErr "kind" kNms ix
  KForall lnm k -> let lnm' = freshName (unLName lnm) kNms
                   in parensIf (p > 0) $ "∀ " ++ lnm' ++ " ∷ ◻. " ++ ppKind (LName lnm' : kNms) 0 k
  KGlobal gnm   -> unGName gnm

--------------------------------------------------------------------------------

ppConstT :: Names -> ConstT Kind -> String
ppConstT kNms = \case
  TBase Int    -> "Int"
  TBase Double -> "Double"
  TBase String -> "String"
  TBase Unit   -> "()"
  TBase Arr    -> "(→)"
  TBase IO     -> "IO"
  TForall   k  -> "∀ ["  ++ ppKind kNms 0 k ++ "]"
  TForallK     -> "∀ ∷ ◻"

binOpInfoT :: ConstT Kind -> Names -> Maybe (String, Prec, Assoc)
binOpInfoT c _ = case c of
  TBase Arr -> Just ("→", precArr, RightAssoc)
  _         -> Nothing

isBinOp      :: Type   -> Names -> Maybe (String, Prec, Assoc)
isBinOpNeuNf :: NeuNfT -> Names -> Maybe (String, Prec, Assoc)

isBinOp      t  kNms = case t  of { TConst     c -> binOpInfoT c kNms; _ -> Nothing }
isBinOpNeuNf nf kNms = case nf of { NfNeuConst c -> binOpInfoT c kNms; _ -> Nothing }

ppType :: Names -> Names -> Prec -> Type -> String
ppType tNms kNms p t = case t of
  _ | Just (q, mk, lnm, body) <- isQuant t ->
      let (lnm', tNms', kNms') = case q of
                                   QForallK -> let l = freshKNm lnm in (l, tNms, LName l : kNms)
                                   _        -> let l = freshTNm lnm in (l, LName l : tNms, kNms)
          (binds, tNms'', kNms'', inner) = collectQ q tNms' kNms' body
      in  fmtQuant kNms'' p q ((lnm', mk) : binds) (ppType tNms'' kNms'' 0 inner)

  TVar    i                 -> idxNmT tNms i
  TGlobal gnm               -> unGName gnm
  TConst  c                 -> ppConstT kNms c
  
  TLam    lnm  k       tBdy -> let lnm' = freshTNm lnm in parens 0 $ "λ "   ++ lnm' ++ fmtKindAnn kNms k ++ ". "   ++ ppBodyT lnm' tBdy
  TKLam   lnm          tBdy -> let lnm' = freshKNm lnm in parens 0 $ "λ "   ++ lnm' ++                      ". "   ++ ppBodyK lnm' tBdy
  TLet    lnm  ty      tBdy -> let lnm' = freshTNm lnm in parens 0 $ "let " ++ lnm' ++ " = "  ++ pp 0 ty ++ " in " ++ ppBodyT lnm' tBdy
  
  TApp    (TApp op t') t''  | Just (sym, opP, assoc) <- isBinOp op kNms ->
      let (p', p'') = binOpAssoc opP assoc
      in  fmtBinOp p opP sym (pp p' t') (pp p'' t'')
      
  TApp    t'            t'' -> parens precApp  $ pp precApp t' ++ " " ++ pp (precApp + 1) t''
  TKApp   t'            k   -> parens precTApp $ pp precTApp t' ++ " {" ++ ppKind kNms 0 k ++ "}"
  where pp         = ppType tNms kNms
        ppBodyT lT = ppType (LName lT : tNms) kNms 0
        ppBodyK lK = ppType tNms (LName lK : kNms) 0
        freshTNm lnm = freshName (unLName lnm) tNms
        freshKNm lnm = freshName (unLName lnm) kNms
        parens pr  = parensIf (p > pr)

--------------------------------------------------------------------------------

ppNfT :: Names -> Names -> Prec -> NfT -> String
ppNfT tNms kNms p nf = maybe ppBase ppQ (isQuantNf nf)
  where ppBase = case nf of
          NfNeu         ne   -> ppNeuNfT tNms kNms p ne
          NfLam  lnm k  body -> let lnm' = freshTNm lnm in parens 0 $ "λ " ++ lnm' ++ fmtKindAnn kNms k ++ ". " ++ ppBodyT lnm' body
          NfLamK lnm    body -> let lnm' = freshKNm lnm in parens 0 $ "λ " ++ lnm' ++ ". " ++ ppBodyK lnm' body
        ppQ (q, mk, lnm, body) =
          let (lnm', tNms', kNms') = case q of
                                       QForallK -> let l = freshKNm lnm in (l, tNms, LName l : kNms)
                                       _        -> let l = freshTNm lnm in (l, LName l : tNms, kNms)
              (binds, tNms'', kNms'', inner) = collectQNf q tNms' kNms' body
          in  fmtQuant kNms'' p q ((lnm', mk) : binds) (ppNfT tNms'' kNms'' 0 inner)
        freshTNm lnm = freshName (unLName lnm) tNms
        freshKNm lnm = freshName (unLName lnm) kNms
        ppBodyT  lT  = ppNfT (LName lT : tNms) kNms 0
        ppBodyK  lK  = ppNfT tNms (LName lK : kNms) 0
        parens   pr  = parensIf (p > pr)

ppNeuNfT :: Names -> Names -> Prec -> NeuNfT -> String
ppNeuNfT tNms kNms p nf = case nf of
  NfNeuBVar   i      -> idxNmT tNms i
  NfNeuGlobal gnm    -> unGName gnm
  NfNeuConst  c      -> ppConstT kNms c
  
  NfNeuApp    (NfNeuApp op nf') nf'' | Just (sym, opP, assoc) <- isBinOpNeuNf op kNms ->
      let (p', p'') = binOpAssoc opP assoc
      in  fmtBinOp p opP sym (pp p' nf') (pp p'' nf'')
      
  NfNeuApp    nf' nf'' -> parens precApp  $ ppNeuNfT tNms kNms precApp  nf' ++ " " ++ pp (precApp + 1) nf''
  NfNeuKApp   nf' k    -> parens precTApp $ ppNeuNfT tNms kNms precTApp nf' ++ " {" ++ ppKind kNms 0 k ++ "}"
  where pp        = ppNfT tNms kNms
        parens pr = parensIf (p > pr)

--------------------------------------------------------------------------------

ppConstE :: Names -> ConstE -> String
ppConstE _ = \case
  EPutStr     -> "putStr"
  EGetLine    -> "getLine"
  EReadFile   -> "readFile"
  EWriteFile  -> "writeFile"
  
  EArgCount   -> "argCount"
  EArgAt      -> "argAt"
  
  EAdd        -> "(+)"
  ESub        -> "(-)"
  EMul        -> "(*)"
  EAddD       -> "(+.)"
  ESubD       -> "(-.)"
  EMulD       -> "(*.)"
  EDivD       -> "(/.)"
  ETrunc      -> "trunc"
  
  EIntEq      -> "=="
  EStringEq   -> "=^"
  EDoubleEq   -> "=."
  EConcat     -> "(^)"
  ESubstring  -> "substring"
  ELength     -> "length"
  EShowInt    -> "showInt"
  EShowDouble -> "showDouble"

binOpInfo :: ConstE -> Maybe (Prec, Prec, Prec, String)
binOpInfo = \case
  EConcat   -> Just (5, 6, 5, "^" )
  EIntEq    -> Just (5, 6, 6, "==")
  EStringEq -> Just (5, 6, 6, "=^")
  EDoubleEq -> Just (5, 6, 6, "=.")
  EMul      -> Just (7, 7, 8, "*" )
  EMulD     -> Just (7, 7, 8, "*.")
  EDivD     -> Just (7, 7, 8, "/.")
  EAdd      -> Just (6, 6, 7, "+" )
  ESub      -> Just (6, 6, 7, "-" )
  EAddD     -> Just (6, 6, 7, "+.")
  ESubD     -> Just (6, 6, 7, "-.")
  _         -> Nothing

ppLit :: Lit -> String
ppLit = \case
  LInt    n -> show n
  LDouble x -> show x
  LString s -> show (T.unpack s)
  LUnit     -> "()"

ppExp :: Names -> Names -> Names -> Prec -> Exp -> String
ppExp tNms kNms eNms p = \case
  EVar    i                      -> idxNmE   eNms i
  EGlobal gnm                    -> unGName  gnm
  EConst  c                      -> ppConstE kNms c
  ELit    l                      -> ppLit         l
  
  ELam    lnm ty   eBdy          -> let lnm' = freshENm lnm in parens 0 $ "λ "   ++ lnm' ++ fmtTypeAnn tNms kNms ty ++ ". " ++ ppBodyE lnm' eBdy
  ETLam   lnm k    eBdy          -> let lnm' = freshTNm lnm in parens 0 $ "Λ "   ++ lnm' ++ fmtKindAnn kNms k       ++ ". " ++ ppBodyT lnm' eBdy
  EKLam   lnm      eBdy          -> let lnm' = freshKNm lnm in parens 0 $ "Λ "   ++ lnm' ++                            ". " ++ ppBodyK lnm' eBdy
  
  ELet    lnm ty   e    e'       -> let lnm' = freshENm lnm in parens 0 $ "let " ++ lnm' ++ fmtTypeAnn tNms kNms ty ++ " = " ++ pp 0 e ++ " in " ++ ppBodyE lnm' e'
  
  EApp    (EApp (EConst c) e) e' | Just (opP, p', p'', sym) <- binOpInfo c -> fmtBinOp p opP sym (pp p' e) (pp p'' e')
  
  EApp    e   e'                 -> parens precAppExp $ pp precAppExp e ++ " "  ++ pp (precAppExp + 1) e'
  ETApp   e   t                  -> parens precTApp   $ pp precTApp   e ++ " [" ++ ppT         0 t ++ "]"
  EKApp   e   k                  -> parens precTApp   $ pp precTApp   e ++ " {" ++ ppKind kNms 0 k ++ "}"
  
  EReturn e                      -> parens precAppExp $ "return "                ++ pp (precAppExp + 1) e
  EBind   e   e'                 -> parens precBind   $ pp precBind e ++ " >>= " ++ pp (precBind   + 1) e'
                              
  EHole   hnm me                 -> "?" ++ unHName hnm ++ maybe "" (("{" ++) . (++ "}") . pp 0) me
  where pp           = ppExp                   tNms              kNms             eNms 
        ppT          = ppType                  tNms              kNms
        ppBodyE  lE  = ppExp                   tNms              kNms (LName lE : eNms) 0
        ppBodyT  lT  = ppExp       (LName lT : tNms)             kNms             eNms  0
        ppBodyK  lK  = ppExp                   tNms  (LName lK : kNms)            eNms  0
        freshENm lnm = freshName (unLName lnm)                                    eNms
        freshTNm lnm = freshName (unLName lnm) tNms
        freshKNm lnm = freshName (unLName lnm)                   kNms
        parens   pr  = parensIf (p > pr)

--------------------------------------------------------------------------------

ppErased :: Names -> Prec -> Int -> Erased -> String
ppErased kNms p d = \case
  XVar     ix                     -> let i = unIx ix in bool ("\ESC[36m#" ++ show i ++ "\ESC[0m") (cDepth (d - 1 - i) ("#" ++ show i)) (i < d)
  XGlobal  gnm                    -> unGName gnm
  XConst   c                      -> ppConstE kNms c
  XLit     l                      -> ppLit l
  
  XLam     e                      -> parens 0          $ cDepth d "λ. " ++ ppErased kNms 0 (d + 1) e

  XApp     (XApp (XConst c) e) e' | Just (opP, p', p'', sym) <- binOpInfo c -> fmtBinOp p opP sym (pp p' e) (pp p'' e')
  
  XApp     e   e'                 -> parens precAppExp $ pp precAppExp e ++ " " ++ pp (precAppExp + 1) e'
  
  XLet     e   e'                 -> parens 0          $ cDepth d "let " ++ pp 0 e ++ cDepth d " in " ++ ppErased kNms 0 (d + 1) e'
  
  XReturn  e                      -> parens precAppExp $ "return " ++ pp (precAppExp + 1) e
  XBind    e   e'                 -> parens precBind   $ pp precBind e ++ " >>= " ++ pp (precBind + 1) e'
  where pp     pr = ppErased kNms pr d
        parens pr = parensIf (p > pr)

--------------------------------------------------------------------------------

ppView :: View -> String
ppView = \case
  VwOmitted             -> "…"
  VwEvaluating          -> "~…"
  VwUneval      e       -> "~" ++ ppErased [] 0 0 e
  
  VwLit         l       -> ppLit l
  
  VwClosure     e env   -> "⟨" ++ cDepth 0 "λ. " ++ ppErased [] 0 1 e ++ bool (" | [" ++ unwords (map ppView env) ++ "]") "" (null env) ++ "⟩"
  VwPartial     c as    -> "⟨" ++ unwords (ppConstE [] c : map ppView as) ++ "⟩"
  
  VwIOReturn    sn      -> "return "             ++ ppView sn
  VwIOBind      snL snK -> ppView snL ++ " >>= " ++ ppView snK
  
  VwIPutStr     sn      -> "putStr "    ++ ppView sn
  VwIGetLine            -> "getLine"
  VwIReadFile   sn      -> "readFile "  ++ ppView sn
  VwIWriteFile  sn snK  -> "writeFile " ++ ppView sn ++ " " ++ ppView snK
  VwIArgCount           -> "argCount"
  VwIArgAt      sn      -> "argAt "     ++ ppView sn

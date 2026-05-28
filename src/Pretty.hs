{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE RecordWildCards #-}

module Pretty where

import           Control.Monad.Reader
import           Data.Bool            (bool  )
import           Data.Functor.Classes (liftEq)
import qualified Data.Text        as   T

import           Syntax
import           Utils  

--------------------------------------------------------------------------------

type Prec = Int

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

nameSuffixes :: [String]
nameSuffixes = "" : "′" : "″" : "‴" : map show [(1 :: Int)..]

freshNm :: String -> LNames -> String 
freshNm base nms = findFresh nameSuffixes
  where findFresh = \case
          s : ss -> let lnm = base ++ s in bool (findFresh ss) lnm (LName lnm `notElem` nms)
          []     -> base

checkBounds :: String -> LNames -> String -> Int -> String
checkBounds err nms kind i =
  bool (internalErr $ "Out of bounds " ++ err ++ " " ++ kind ++ ": " ++ show i)
       (unLName (nms !! i))
       (i >= 0 && i < length nms)

idxNameErr :: String -> LNames -> Int -> String
idxNameErr err nms = checkBounds err nms "index"

idxNmT :: LNames -> Int -> String
idxNmT = idxNameErr "type"

--------------------------------------------------------------------------------

data PPEnv = PPEnv
  { envTNms  :: LNames , 
    envKNms  :: LNames , 
    envPrec  :: Prec   , 
    envDepth :: Int    }

type PP = Reader PPEnv

runPP :: PPEnv -> PP a -> a
runPP = flip runReader

withPrec :: Prec -> PP a -> PP a
withPrec p = local (\e -> e { envPrec = p })

withDepthUp :: PP a -> PP a
withDepthUp = local (\e -> e { envDepth = envDepth e + 1 })

withNm :: (PPEnv -> LNames) -> (LNames -> PPEnv -> PPEnv) -> String -> (String -> PP a) -> PP a
withNm getN setN base f = asks getN >>= \nms -> let l = freshNm base nms in local (setN (LName l : nms)) (f l)

withTNm, withKNm :: String -> (String -> PP a) -> PP a

withTNm = withNm envTNms (\ns e -> e { envTNms = ns })
withKNm = withNm envKNms (\ns e -> e { envKNms = ns })

withBinder :: (String -> (String -> PP String) -> PP String) -> String -> (String -> PP String) -> PP String -> PP String
withBinder withNmF base mkPrefixM bodyM = 
  ask >>= \PPEnv{..} -> withNmF base $ \nm' -> 
    (\pref body -> parensIf (envPrec > 0) (pref ++ body)) <$> mkPrefixM nm' <*> withPrec 0 bodyM

--------------------------------------------------------------------------------

type TyBinds      = [(String,  Maybe Kind)]
type QuantGroups  = [([String], Maybe Kind)]

type Collected  a = (TyBinds, LNames, LNames, a)
type Quantifier a = Maybe (Quant, Maybe Kind, LName, a)

data Quant
  = QForall
  | QForallK
  deriving Eq

isQuant   :: Type -> Quantifier Type
isQuantNf :: NfT  -> Quantifier NfT

isQuant = \case
  TApp (TConst (TForall k)) (TLam  lnm _ body) -> Just (QForall,  Just k,  lnm, body)
  TApp (TConst  TForallK  ) (TKLam lnm   body) -> Just (QForallK, Nothing, lnm, body)
  _                                            -> Nothing

isQuantNf = \case
  NfNeu (NfNeuApp (NfNeuConst (TForall k)) (NfLam  lnm _ body)) -> Just (QForall,  Just k,  lnm, body)
  NfNeu (NfNeuApp (NfNeuConst  TForallK  ) (NfLamK lnm   body)) -> Just (QForallK, Nothing, lnm, body)
  _                                                             -> Nothing

collectQGen :: (a -> Quantifier a) -> Quant -> LNames -> LNames -> a -> Collected a
collectQGen isQ q tNms kNms t = case isQ t of
  Just (q', mk, LName l, body) | q == q' ->
    let isK                            = q == QForallK
        lnm'                           = freshNm l (if isK then kNms else tNms)
        (tNms', kNms'                ) = if isK then (tNms, LName lnm' : kNms) else (LName lnm' : tNms, kNms)
        (binds, tNms'', kNms'', inner) = collectQGen isQ q tNms' kNms' body
    in  ((lnm', mk) : binds, tNms'', kNms'', inner)
  _                                      -> ([], tNms, kNms, t)

collectQ   :: Quant -> LNames -> LNames -> Type -> Collected Type
collectQNf :: Quant -> LNames -> LNames -> NfT  -> Collected NfT

collectQ   = collectQGen isQuant
collectQNf = collectQGen isQuantNf

groupBinds :: TyBinds -> QuantGroups
groupBinds = foldr groupStep []
  where groupStep (n, mk) = \case
          [              ]      -> [([n], mk)]
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

--------------------------------------------------------------------------------

fmtPrefixM, fmtPostfixM, fmtAppM :: Prec -> PP String -> PP String -> PP String
fmtBinOpM                        :: Prec -> String    -> PP String -> PP String -> PP String

fmtPrefixM  appP mPre m    = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((++)                                     <$> mPre <*> m   )
fmtPostfixM appP mSuf m    = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((++)                                     <$> m    <*> mSuf)
fmtAppM     appP      m m' = ask >>= \PPEnv{..} -> parensIf (envPrec > appP) <$> ((\s s' -> s ++ " "  ++ s') <$> m <*> m')
fmtBinOpM   opP  sym  m m' = ask >>= \PPEnv{..} -> parensIf (envPrec > opP ) <$> ((\s s' -> s ++ " "  ++ sym ++ " " ++ s') <$> m    <*> m'  )

fmtBindM :: String -> PP String -> String -> PP String
fmtBindM pre mSuf n = (\suf -> pre ++ n ++ suf) <$> mSuf

fmtLetBindM :: PP String -> PP String -> String -> PP String
fmtLetBindM mTyAnn mBnd n = (\tyA bnd -> "let " ++ n ++ tyA ++ " = " ++ bnd ++ " in ") <$> mTyAnn <*> mBnd

fmtXLetM :: PP String -> PP String -> PP String
fmtXLetM mBnd mBdy = ask >>= \PPEnv{..} -> (\bnd bdy -> parensIf (envPrec > 0) $ cDepth envDepth "let " ++ bnd ++ cDepth envDepth " in " ++ bdy) <$> mBnd <*> mBdy

fmtKindAnnM :: Kind -> PP String
fmtTypeAnnM :: Type -> PP String

fmtKindAnnM k = (" ∷ " ++) <$> withPrec 0 (ppKindM k)
fmtTypeAnnM t = (" : " ++) <$> withPrec 0 (ppTypeM t)

fmtQuantGroupsM :: Quant -> QuantGroups -> PP String
fmtQuantGroupsM q = \case
  [g] -> fmtGroupM g
  gs  -> unwords . map (\x -> "(" ++ x ++ ")") <$> traverse fmtGroupM gs
  where fmtGroupM (ns, mk) = (unwords ns ++)   <$> fmtAnnM mk
        fmtAnnM        mk  = case q of { QForallK -> pure " ∷ ◻"; _ -> maybe (pure " ∷ ◻") (\k -> (" ∷ " ++) <$> withPrec 0 (ppKindM k)) mk }

fmtQuantM :: Quant -> TyBinds -> PP String -> PP String
fmtQuantM q binds innerM = do
  p         <- asks envPrec
  groupsStr <- fmtQuantGroupsM q (groupBinds binds)
  parensIf (p > 0) . (\inr -> "∀ " ++ groupsStr ++ ". " ++ inr) <$> innerM

--------------------------------------------------------------------------------

ppKind :: LNames -> Prec -> Kind -> String
ppKind kNms p k = runPP (PPEnv [] kNms p 0) (ppKindM k)

ppKindM :: Kind -> PP String
ppKindM k = ask >>= \PPEnv{..} -> case k of
  KStar               -> pure "*"
  KArr     dom cod    -> fmtBinOpM precArr "→" (withPrec (precArr + 1) (ppKindM dom)) (withPrec precArr (ppKindM cod))
  KVar    (Ix    i)   -> pure (idxNameErr "kind" envKNms i)
  KForall (LName l) b -> withBinder withKNm l (fmtBindM "∀ " (pure " ∷ ◻. ")) (ppKindM b)
  KGlobal (GName g)   -> pure g

--------------------------------------------------------------------------------

ppConstTM :: ConstT Kind -> PP String
ppConstTM = \case
  TBase     Int    -> pure "Int"
  TBase     Double -> pure "Double"
  TBase     String -> pure "String"
  TBase     Unit   -> pure "()"
  TBase     Arr    -> pure "(→)"
  TBase     IO     -> pure "IO"
  TForall   k      -> ("∀ [" ++) . (++ "]") <$> withPrec 0 (ppKindM k)
  TForallK         -> pure "∀ ∷ ◻"

binOpInfoT :: ConstT Kind -> Maybe (Prec, Prec, Prec, String)
binOpInfoT = \case { TBase Arr -> Just (precArr, precArr + 1, precArr, "→"); _ -> Nothing }

isBinOp      :: Type   -> Maybe (Prec, Prec, Prec, String)
isBinOpNeuNf :: NeuNfT -> Maybe (Prec, Prec, Prec, String)

isBinOp      = \case { TConst     c -> binOpInfoT c; _ -> Nothing }
isBinOpNeuNf = \case { NfNeuConst c -> binOpInfoT c; _ -> Nothing }

ppType :: LNames -> LNames -> Prec -> Type -> String
ppType tNms kNms p t = runPP (PPEnv tNms kNms p 0) (ppTypeM t)

ppTypeM :: Type -> PP String
ppTypeM t = ask >>= \PPEnv{..} -> case t of
  _ | Just (q, _, _, _) <- isQuant t
                             -> do
      let (binds, tNms', kNms', inner) = collectQ q envTNms envKNms t
      fmtQuantM q binds (local (\e -> e { envTNms = tNms', envKNms = kNms', envPrec = 0 }) (ppTypeM inner))

  TVar    (Ix i)             -> pure     (idxNmT envTNms i)
  TGlobal (GName g)          -> pure      g
  TConst  c                  -> ppConstTM c
  
  TLam    (LName l)  k tBdy  -> withBinder withTNm l (fmtBindM "λ " ((++  ". ") <$>     fmtKindAnnM k))  (ppTypeM tBdy)
  TKLam   (LName l)    tBdy  -> withBinder withKNm l (fmtBindM "λ " (pure ". "                       ))  (ppTypeM tBdy)
  TLet    (LName l) ty tBdy  -> withBinder withTNm l (fmtLetBindM   (pure "") (withPrec 0 (ppTypeM ty))) (ppTypeM tBdy)
  
  TApp    (TApp op ty) ty' 
    | Just (opP, p', p'', sym) <- isBinOp op
                             -> fmtBinOpM opP sym (withPrec p' (ppTypeM ty)) (withPrec p'' (ppTypeM ty'))
        
  TApp    ty          ty'    -> fmtAppM     precApp  (withPrec precApp (ppTypeM ty))    (withPrec   (precApp + 1)                    (ppTypeM ty'))
  TKApp   ty          k      -> fmtPostfixM precTApp ((" {" ++)      .      (++ "}") <$> withPrec 0 (ppKindM  k)) (withPrec precTApp (ppTypeM ty ))

--------------------------------------------------------------------------------

ppNfT :: LNames -> LNames -> Prec -> NfT -> String
ppNfT tNms kNms p nf = runPP (PPEnv tNms kNms p 0) (ppNfTM nf)

ppNfTM :: NfT -> PP String
ppNfTM nf = ask >>= \PPEnv{..} -> case nf of
  _ | Just (q, _, _, _) <- isQuantNf nf
                              -> do
        let (binds, tNms', kNms', inner) = collectQNf q envTNms envKNms nf
        fmtQuantM q binds (local (\e -> e { envTNms = tNms', envKNms = kNms', envPrec = 0 }) (ppNfTM inner))
  
  NfNeu        ne             -> ppNeuNfTM ne
  NfLam  (LName l) k  body    -> withBinder withTNm l (fmtBindM "λ " ((++  ". ") <$> fmtKindAnnM k)) (ppNfTM body)
  NfLamK (LName l)    body    -> withBinder withKNm l (fmtBindM "λ " (pure ". "                   )) (ppNfTM body)

ppNeuNfT :: LNames -> LNames -> Prec -> NeuNfT -> String
ppNeuNfT tNms kNms p nf = runPP (PPEnv tNms kNms p 0) (ppNeuNfTM nf)

ppNeuNfTM :: NeuNfT -> PP String
ppNeuNfTM ne = ask >>= \PPEnv{..} -> case ne of
  NfNeuBVar   (Ix i)     -> pure (idxNmT envTNms i)
  NfNeuGlobal (GName g)  -> pure g
  NfNeuConst  c          -> ppConstTM c
  
  NfNeuApp    (NfNeuApp op nf) nf' 
    | Just (opP, p', p'', sym) <- isBinOpNeuNf op
                         -> fmtBinOpM opP sym (withPrec p' (ppNfTM nf)) (withPrec p'' (ppNfTM nf'))
        
  NfNeuApp    nf nf'     -> fmtAppM     precApp  (withPrec precApp (ppNeuNfTM nf))    (withPrec   (precApp + 1) (ppNfTM nf'))
  NfNeuKApp   nf k       -> fmtPostfixM precTApp ((" {" ++)       .       (++ "}") <$> withPrec 0 (ppKindM  k)) (withPrec precTApp (ppNeuNfTM nf))

--------------------------------------------------------------------------------

ppConstE :: LNames -> ConstE -> String
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

--------------------------------------------------------------------------------

ppErased :: LNames -> Prec -> Int -> Erased -> String
ppErased kNms p d e = runPP (PPEnv [] kNms p d) (ppErasedM e)

ppErasedM :: Erased -> PP String
ppErasedM er = ask >>= \PPEnv{..} -> case er of
  XVar     (Ix i)                 -> pure $ bool ("\ESC[36m#" ++ show i ++ "\ESC[0m") (cDepth (envDepth - 1 - i) ("#" ++ show i)) (i < envDepth)
  XGlobal  (GName g)              -> pure g
  XConst   c                      -> pure (ppConstE envKNms c)
  XLit     l                      -> pure (ppLit l)
  
  XLam     e                      -> fmtPrefixM  0 (pure (cDepth envDepth "λ. ")) (withPrec 0 (withDepthUp (ppErasedM e)))

  XApp     (XApp (XConst c) e) e' 
    | Just (opP, p', p'', sym) <- binOpInfo c
                                  -> fmtBinOpM   opP        sym (withPrec p' (ppErasedM e)) (withPrec p'' (ppErasedM e'))
  
  XApp     e   e'                 -> fmtAppM     precAppExp     (withPrec precAppExp (ppErasedM e)) (withPrec  (precAppExp + 1) (ppErasedM e'))
  XLet     eBnd eBdy              -> fmtXLetM                   (withPrec 0 (ppErasedM eBnd))       (withPrec 0 (withDepthUp  (ppErasedM eBdy)))
  
  XReturn  e                      -> fmtPrefixM  precAppExp     (pure "return ") (withPrec (precAppExp + 1)                (ppErasedM e ))
  XBind    e   e'                 -> fmtBinOpM   precBind ">>=" (withPrec precBind (ppErasedM e)) (withPrec (precBind + 1) (ppErasedM e'))
  XFix     e                      -> fmtPrefixM  precAppExp     (pure (cDepth envDepth "fix ")) (withPrec (precAppExp + 1) (ppErasedM e ))

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

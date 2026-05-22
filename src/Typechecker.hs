{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE FlexibleContexts           #-}

module Typechecker where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad        ( when      , unless, forM, forM_)
                                                 
import           Data.Functor         ((<&>      ),($>    )            )
import           Data.Bifunctor       ( bimap                          )
import           Data.Bool            ( bool                           )
import qualified Data.Map          as   Map                            
import           Data.List            ( elemIndex                      )

import           Syntax
import           Eval
import           Equiv
import           Pretty
import           Utils

--------------------------------------------------------------------------------

data Ctx
  = Ctx { ctxGlbT    :: GTypes    ,     
          ctxGlbK    :: GKinds    ,     
          ctxGlbKDef :: GKinds    ,     
          ctxGlbET   :: GTypes    ,     
          ctxKEnv    :: EnvK      , -- bound kind vars (introduced by Λ k ∷ ◻.)     
          ctxTKs     :: TKinds    , -- bound type vars (introduced by Λ a ∷ κ.)
          ctxTEnv    :: EnvT      ,      
          ctxETs     :: EnvT      , 
          ctxENms    :: Names     , 
          ctxTNms    :: Names     ,      
          ctxKNms    :: Names     ,      
          ctxTLv     :: Lv        ,         
          ctxKLv     :: Lv        ,         
          ctxPos     :: Maybe Pos } 

type Report     = [String]
type TCResult a = (Either String a, Report)

newtype TC a = TC { unTC :: ReaderT Ctx (ExceptT String (Writer Report)) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadReader Ctx, MonadWriter Report)

instance MonadFail TC where
  fail msg = throwError $ "[Internal Error] Pattern match failure in TC do-block: " ++ msg

runTC :: Ctx -> TC a -> TCResult a
runTC ctx m = runWriter (runExceptT (runReaderT (unTC m) ctx))

emptyCtx :: Ctx
emptyCtx = Ctx Map.empty Map.empty Map.empty Map.empty [] [] [] [] [] [] [] 0 0 Nothing

--------------------------------------------------------------------------------

throwErr :: String -> TC a
throwErr msg = asks ctxPos >>= maybe (throwError msg) (\(Pos f l c) -> throwError $ "\"" ++ f ++ "\" (line " ++ show l ++ ", column " ++ show c ++ "):\n" ++ msg)

requireAnn :: Maybe a -> String -> TC a
requireAnn ann errMsg = maybe (throwErr errMsg) return ann

withBind  :: LName -> ValT -> TC a -> TC a
withBindT :: LName -> ValK -> TC a -> TC a
withBindK :: LName         -> TC a -> TC a

withBind lnm v = local $ \Ctx{..} ->
  Ctx { ctxETs  = v   : ctxETs ,
        ctxENms = lnm : ctxENms, 
        .. }

withBindT lnm vK = local $ \Ctx{..} ->
  Ctx { ctxTEnv = freshT ctxTLv : ctxTEnv,
        ctxTKs  = vK            : ctxTKs ,
        ctxTNms = lnm           : ctxTNms,
        ctxTLv  = ctxTLv + 1             ,
        .. }

withBindK lnm = local $ \Ctx{..} ->
  Ctx { ctxKEnv = freshK ctxKLv : ctxKEnv ,
        ctxKNms = lnm           : ctxKNms ,
        ctxKLv  = ctxKLv + 1              ,
        .. }

assertEquiv :: ValT -> ValT -> (Ctx -> String) -> TC ()
assertEquiv v v' mkErr = ask >>= \ctx@Ctx{..} ->
  unless (equivT ctxGlbT ctxGlbKDef ctxTLv ctxKLv v v') $ throwErr (mkErr ctx)

mismatch  :: ValT -> String -> String -> TC a
mismatchK :: ValK -> String -> String -> TC a

mismatch  v sh msg = ask >>= \ctx -> throwErr $ "Expected " ++ sh ++ " type " ++ msg ++ ", got: " ++ ppValT ctx v
mismatchK v sh msg = ask >>= \ctx -> throwErr $ "Expected " ++ sh ++ " kind " ++ msg ++ ", got: " ++ ppValK ctx v

expectArr     :: ValT -> String -> TC (ValT, ValT)
expectForallK :: ValT -> String -> TC  ValT
expectForall  :: ValT -> String -> TC (ValK, ValT)
expectIO      :: ValT -> String -> TC  ValT

expectArr     v msg = case decomposeT v of { Just (TBase    Arr, [dom, cod]) -> return (dom, cod); _ -> mismatch v "arrow"  msg }
expectForall  v msg = case decomposeT v of { Just (TForall  k  , [f       ]) -> return (k  , f  ); _ -> mismatch v "forall" msg }
expectForallK v msg = case decomposeT v of { Just (TForallK    , [f       ]) -> return  f        ; _ -> mismatch v "forall" msg }
expectIO      v msg = case decomposeT v of { Just (TBase IO    , [a       ]) -> return  a        ; _ -> mismatch v "IO"     msg }

expectKArr    :: ValK -> String -> TC (ValK, ValK)
expectKForall :: ValK -> String -> TC (Kind, EnvK)

expectKArr    v msg = case unaliasK v of { VKArr      dom   cod  -> return (dom  , cod ); _ -> mismatchK v "arrow"  msg }
expectKForall v msg = case unaliasK v of { VKForall _ kBody envK -> return (kBody, envK); _ -> mismatchK v "forall" msg }

ppValK :: Ctx -> ValK -> String
ppValT :: Ctx -> ValT -> String

ppValK Ctx{..} v = ppKind         ctxKNms 0 (rbK         ctxGlbKDef        ctxKLv v)
ppValT Ctx{..} v = ppNfT  ctxTNms ctxKNms 0 (rbT ctxGlbT ctxGlbKDef ctxTLv ctxKLv v)

reportHole :: HName -> Maybe Raw -> Maybe ValT -> TC (Maybe ValT, Maybe Exp)
reportHole hnm mR mVTy = ask >>= \ctx@Ctx{..} ->
  maybe (pure (Nothing, Nothing, False, Nothing)) evalR mR >>= \(mV, mErr, isOk, me) ->
        
  let ctxList = reverse (map     (\ n        -> (unLName n, "∷", "◻")) ctxKNms                      )  ++
                reverse (zipWith (\ n k      -> (unLName n, "∷",       ppValK ctx k)) ctxTNms ctxTKs)  ++
                reverse (zipWith (\ n e      -> (unLName n, ":",       ppValT ctx e)) ctxENms ctxETs)
      maxLen  = maximum (0 : map (\(n, _, _) -> length   n)            ctxList                      )
      ctxLns  =              map (\(n, s, t) -> n ++ replicate (maxLen - length n + 1) ' ' ++ s ++ " " ++ t) ctxList
      
      gStr    = maybe "Given: _" (\v -> "Given: " ++ ppValT ctx v) mV
      gLen    = length gStr
      mGiven  = mR $> (gStr ++ bool "" " ✓" isOk)
      
      goalStr = maybe     "Goal: " (const "Goal:  ") mGiven ++ maybe "_" (ppValT ctx) mVTy
      sepLine = replicate (maximum (length goalStr : maybe 0 (const gLen) mGiven : map length ctxLns)) '─' ++ "\n"
      
      ctxBlk  = bool ("\nContext:\n\n" ++ unlines ctxLns ++ sepLine) ("\n" ++ sepLine) (null ctxList)
      givStr  = maybe "" (++           "\n") mGiven
      errStr  = maybe "" ("\n\nError:\n" ++) mErr
      
  in tell ["\nHole: ?" ++ unHName hnm ++ "\n" ++ ctxBlk ++ givStr ++ goalStr ++ errStr ++ "\n"] $> (mV, me)
  where evalR  r       = maybe (inferR r) (checkR r) mVTy
        inferR r       = catchError (infer r          <&> \(vTy, e) ->            (Just vTy  , Nothing  , False, Just  e))
                                    (\err                           -> pure       (Nothing   , Just err , False, Nothing))
        checkR r vTyGl = catchError (check r vTyGl    <&> \e        ->            (Just vTyGl, Nothing  , True , Just  e))
                                    (\errC                          -> catchError
                                    (infer r          <&> \(vTy, e) ->            (Just vTy  , Nothing  , False, Just  e))
                                    (\_                             -> pure       (Nothing   , Just errC, False, Nothing)))

resolve :: UName -> Names -> Map.Map GName a -> String -> (Ix -> TC b) -> (GName -> a -> TC b) -> TC b
resolve (UName unm) nms glbs err onBnd onGlb =
  maybe (maybe (throwErr err)
               (onGlb      (GName unm      ))
               (Map.lookup (GName unm) glbs))
    (onBnd              .   Ix)
    (elemIndex (LName unm) nms)

evalK' :: Kind -> TC ValK
evalT' :: Type -> TC ValT

evalK' k  = asks $ \Ctx{..} -> evalK         ctxGlbKDef         ctxKEnv k
evalT' ty = asks $ \Ctx{..} -> evalT ctxGlbT ctxGlbKDef ctxTEnv ctxKEnv ty

rbK' :: ValK -> TC Kind
rbT' :: ValT -> TC NfT

rbK' v = asks $ \Ctx{..} -> rbK         ctxGlbKDef        ctxKLv v
rbT' v = asks $ \Ctx{..} -> rbT ctxGlbT ctxGlbKDef ctxTLv ctxKLv v

equivK' :: ValK -> ValK -> TC Bool
equivK' v v' = asks $ \Ctx{..} -> equivK ctxGlbKDef ctxKLv v v'

let' :: Raw -> Maybe RawT -> TC (ValT, Exp, Type)
let' r = maybe
  (do (vTy, e) <- infer r
      ty       <- nfToT <$> rbT' vTy
      pure (vTy, e, ty))
  (\rTy -> do
      ty  <- checkT  rTy VKStar
      vTy <- evalT'  ty
      e   <- check r vTy
      pure (vTy, e, ty))

--------------------------------------------------------------------------------

elabK :: RawK -> TC Kind
elabK rK = ask >>= \Ctx{..} -> case rK of
  RKStar                -> pure KStar                                -- *
  RKArr        rK' rK'' -> KArr        <$> elabK  rK' <*> elabK rK'' -- κ′ → κ″
  RKForall lnm rK'      -> KForall lnm <$> withBindK lnm (elabK rK') -- ∀ κ ∷ ◻. κ′
  RKVar        unm      -> resolve unm ctxKNms ctxGlbKDef           
    ("Unbound kind variable: " ++ unUName unm)
    (                     pure . KVar        )
    (\gnm _ ->            pure  (KGlobal  gnm))

--------------------------------------------------------------------------------

inferT :: RawT -> TC (ValK, Type)
inferT rTy = ask >>= \Ctx{..} -> case rTy of
  RTVar unm -> resolve unm ctxTNms ctxGlbK
    ("Unbound type variable: "  ++ unUName         unm )
    (\i      -> pure (ctxTKs    !! unIx i, TVar    i  ))
    (\gnm vK -> pure (vK                 , TGlobal gnm))
  
  RTConst c -> do
    vK <- evalK' (constKind c)
    return (vK, TConst (TBase c))
  
  RTTLam lnm mK rBody -> do         -- λ τ [∷ κ]. τBody
    rK <- requireAnn mK errUnannLam -- because of inference
    k  <- elabK      rK
    vK <- evalK'     k
    
    (vKbody, ty) <- withBindT lnm vK $ inferT rBody -- τBody ∷ κBody
    
    return (VKArr vK vKbody, TLam lnm k ty) -- κ → κBody, λ τ ∷ κ. τBody
    
  RTTKLam lnm rBody -> do                        -- Λ κ ∷ ◻. τBody
    (vKbody, ty) <- withBindK lnm $ inferT rBody -- τBody ∷ κBody

    -- There is no separate type of normal forms for kinds, so
    let kBody = rbK ctxGlbKDef (ctxKLv + 1) vKbody
    
    return (VKForall lnm kBody ctxKEnv, TKLam lnm ty) -- ∀ κ ∷ ◻. κBody, Λ κ. τBody
    
  RTTApp rTy' rTy'' -> do   -- τ′ τ″
    (vK, ty) <- inferT rTy' -- τ′ ∷ κ
    
    -- It is possible to get aliased kind values when the kind of the type is a user-defined kind alias (e. g., T ∷ KindName)
    case unaliasK vK of 
      VKForall {} -> throwErr errExpKApp
      _           -> do
        (vKDom, vKCod) <- expectKArr vK errInTApp
        ty'            <- checkT rTy'' vKDom
        return (vKCod, TApp ty ty') -- τ′ ∷ κ = κDom → κCod, τ″ ∷ κDom

  RTKApp rTy' rK -> do       -- τ′ {κ}
    (vK', ty) <- inferT rTy' -- τ′ ∷ κ′
    
    (kBody, envK) <- expectKForall vK' errInKApp
    k  <- elabK rK
    vK <- evalK' k
        
    let vKbody = evalK ctxGlbKDef (vK : envK) kBody -- κBody[κᵥ ≔ κ]
        
    return (vKbody, TKApp ty k) -- κBody[κᵥ ≔ κ], τ′ {κ}
      
  RTForall lnm mK rBody -> do          -- ∀ τ [∷ κ]. τBody 
    rK <- requireAnn mK errUnannForall 
    k  <- elabK rK
    vK <- evalK' k
    
    tyBody <- withBindT lnm vK (checkT rBody VKStar) -- Γ, τ ∷ κ ⊢ τBody ∷ *
    
    return (VKStar, TApp (TConst (TForall k)) (TLam lnm k tyBody)) -- *, ∀ τ ∷ κ. τBody (= ∀_κ (λ τ ∷ κ. τBody))

  RTForallK lnm rBody -> do                       -- ∀ κ ∷ ◻. τBody (type of kind-polymorphic functions)
    tyBody <- withBindK lnm (checkT rBody VKStar) -- Γ, κ ∷ ◻ ⊢ τBody ∷ *
    
    return (VKStar, TApp (TConst TForallK) (TKLam lnm tyBody)) -- *, ∀ κ ∷ ◻. τBody
        
  RTLoc p rTy' -> local (\c -> c { ctxPos = Just p }) (inferT rTy')
  
  where constKind = \case
          Arr -> KArr KStar (KArr KStar KStar)
          IO  -> KArr KStar  KStar
          _   -> KStar
        
        errUnannLam    = "Cannot infer kind for unannotated type lambda."
        errExpKApp     = "Type applied to a kind-expecting constructor must use explicit kind application syntax."
        errInTApp      = "in type application"
        errInKApp      = "in kind application"
        errUnannForall = "Cannot infer kind for unannotated forall."

checkT :: RawT -> ValK -> TC Type
checkT rTy vKExp = ask >>= \ctx@Ctx{..} -> case rTy of
    RTTKLam lnm rBody -> do                             -- (Λ κ ∷ ◻. τBody) ∷ (∀ κ ∷ ◻. κBody)
      (kBody, envK) <- expectKForall vKExp errForTKLam
      
      let vKbody = evalK ctxGlbKDef (freshK ctxKLv : envK) kBody
      
      TKLam lnm <$> withBindK lnm (checkT rBody vKbody) -- τBody ∷ κBody[κᵥ ≔ fresh]

    RTTLam lnm mK rBody -> do                       -- λ τ [∷ κ]. τBody ∷ κDom → κCod
      (vKDom, vKCod) <- expectKArr vKExp errForTLam
      
      let kDom = rbK ctxGlbKDef ctxKLv vKDom
      
      maybe
        (TLam lnm kDom <$> withBindT lnm vKDom (checkT rBody vKCod)) -- τBody ∷ κCod
        (\rK -> do                                                   
          k  <- elabK rK
          vK <- evalK' k
          
          b <- equivK' vK vKDom
          
          unless b $ throwErr errKMismAnn -- if κ /= κDom
          
          TLam lnm k <$> withBindT lnm vK (checkT rBody vKCod)) -- τBody ∷ κCod
        mK

    RTLoc p rTy' -> 
      local (\c -> c { ctxPos = Just p }) (checkT rTy' vKExp)

    _ -> do
      (vK, ty) <- inferT rTy

      b <- equivK' vK vKExp
      unless b $ throwErr $ errKMism (ppValK ctx vKExp) (ppValK ctx vK)
        
      return ty
      
  where errKMismAnn        = "Kind mismatch in type lambda annotation."
        errForTLam         = "for type lambda"
        errForTKLam        = "for kind lambda"
        errKMism     pE pG = "Kind mismatch. Expected " ++ pE ++ " but got " ++ pG

--------------------------------------------------------------------------------

infer :: Raw -> TC (ValT, Exp)
infer r = ask >>= \Ctx{..} -> case r of
  RVar unm -> resolve unm ctxENms ctxGlbET
    ("Unbound term variable: " ++ unUName unm         )
    (\i       -> pure (ctxETs  !! unIx i, EVar    i  ))
    (\gnm vTy -> pure (vTy              , EGlobal gnm))
      
  RConst c -> do
    vTy <- evalT' (constT c)
    pure (vTy, EConst c)
  
  RLit l -> pure (litTy l, ELit l)

  RAnn r' rTy -> do          -- (e′ : τ)
    ty  <- checkT rTy VKStar --  τ ∷ *
    vTy <- evalT' ty
    e   <- check r' vTy      -- e′ : τ
    
    return (vTy, e)  -- τ, e′

  RLam lnm mTy rBody -> do            -- λ x [∷ τ]. eBody
    rTy <- requireAnn mTy errUnannLam
    ty  <- checkT rTy VKStar          -- τ ∷ *
    vTy <- evalT' ty
    
    (vTyBody, e) <- withBind lnm vTy $ infer rBody -- eBody ∷ τBody
    
    return (vArr vTy vTyBody, ELam lnm ty e) -- τ → τBody, λ x : τ. eBody

  RTLam lnm mK rBody -> do           -- Λ τ [∷ κ]. eBody
    rK <- requireAnn mK errUnannTLam
    k  <- elabK rK
    vK <- evalK' k
    
    (vBody, e) <- withBindT lnm vK $ infer rBody -- eBody ∷ τBody
    
    -- rb the body type to expression, wrap it in ∀, and evaluate it back to value
    bodyTy <- withBindT lnm vK $ nfToT <$> rbT' vBody
    vTy    <- evalT' (TApp (TConst (TForall k)) (TLam lnm k bodyTy))
    
    return (vTy, ETLam lnm k e) -- ∀ τ ∷ κ. τBody, Λ τ ∷ κ. eBody

  RKLam lnm rBody -> do                        -- Λ κ ∷ ◻. eBody
    (vBody, e) <- withBindK lnm $ infer rBody  -- eBody ∷ τBody
    
    -- see above
    bodyTy <- withBindK lnm $ nfToT <$> rbT' vBody
    vTy    <- evalT' (TApp (TConst TForallK) (TKLam lnm bodyTy))
    
    return (vTy, EKLam lnm e) -- ∀ κ ∷ ◻. τBody, Λ κ. eBody

  RApp r' r'' -> do                        -- e′ e″
    (vTy , e)    <- infer r'               -- e′ ∷ τ
    (vDom, vCod) <- expectArr vTy errInApp -- τ = τDom → τCod
    e'           <- check r'' vDom         -- e″ : τDom
    
    return (vCod, EApp e e') -- τCod, e′ e″

  RTApp r' rTy -> do                          -- e′ [τ]
    (vTy', e') <- infer r'                    -- e′ ∷ τ′
    (vK  , vF) <- expectForall vTy' errInTApp -- τ′ = ∀ τᵥ ∷ κ. τBody
    ty         <- checkT rTy vK               -- τ ∷ κ
    vTy        <- evalT' ty 
    
    let vTyBody = appT ctxGlbT ctxGlbKDef vF vTy
    
    return (vTyBody, ETApp e' ty) -- τBody[τᵥ ≔ τ], e′ [τ]
    
  RKApp r' mK -> do                         -- e′ {κ}
    (vTy, e) <- infer r'                    -- e′ ∷ τ′
    vF       <- expectForallK vTy errInKApp -- τ′ = ∀ κᵥ ∷ ◻. τBody
    k        <- elabK mK
    vK       <- evalK' k
    
    let vTyBody = appTK ctxGlbT ctxGlbKDef vF vK
    
    return (vTyBody, EKApp e k) -- τBody[κᵥ ≔ κ], e′ {κ}

  RLet lnm mTy r' rBody -> do                        -- let x [: τ] = e′ in eBody
    (vTy  , e, ty) <- let' r' mTy                    -- e′ ∷ τ      
    (vBody, e'   ) <- withBind lnm vTy $ infer rBody -- eBody ∷ τBody
    
    return (vBody, ELet lnm ty e e') -- τBody, let x : τ = e′ in eBody

  RReturn r' -> infer r' <&> bimap vIO EReturn -- IO τ, return (e : τ)

  RBind r' r'' -> do                                        -- e′ >>= e″
    (vTy'   , e'      ) <- infer     r'                     -- e′ : τ′
    vTyDom              <- expectIO  vTy'     errLhsBind    -- τ′ = IO τDom
    (vTy''  , e''     ) <- infer     r''                    -- e″ : τ″
    (vTyDom', vTyCodIO) <- expectArr vTy''    errRhsBind    -- τ″ = τDom′ → τCodIO
    _                   <- expectIO  vTyCodIO errRhsResBind -- τCodIO = IO τCod
    
    assertEquiv vTyDom vTyDom' errMismBind -- τDom = τDom′
    
    return (vTyCodIO, EBind e' e'') -- IO τCod, e′ >>= e″

  RHole hnm mR -> do
    (mTy, me) <- reportHole hnm mR Nothing
    
    maybe (throwErr $ errHoleInfer hnm)
          (\vTy -> return (vTy, EHole hnm me))
          mTy
  
  RLoc p r' -> local (\c -> c { ctxPos = Just p }) (infer r')
  
  where errUnannLam      = "Cannot infer the type for unannotated lambda."
        errUnannTLam     = "Cannot infer the type for unannotated type abstraction Λ."
        errHoleInfer hnm = "Hole ?" ++ unHName hnm ++ " in inference mode cannot proceed without an annotation."
        errInApp         = "in application"
        errInTApp        = "in type application"
        errInKApp        = "in kind application"
        errLhsBind       = "on left-hand side of bind"
        errRhsBind       = "for right-hand side of bind"
        errRhsResBind    = "for right-hand side result of bind"
        errMismBind   _  = "Type mismatch in bind: left-hand side result does not match right-hand side argument."
          
        litTy = \case
           LInt    _ -> vInt
           LDouble _ -> vDouble
           LString _ -> vString
           LUnit     -> vUnit
           
        constT = \case
           EPutStr     -> tString                       ~> tIO    tUnit
           EGetLine    ->                                  tIO   (tOption tString)
           EReadFile   -> tString                       ~> tIO   (tResult tString tString)
           EWriteFile  -> tString ~> tString            ~> tIO   (tResult tString tUnit)
           EArgCount   ->                                  tIO    tInt
           EArgAt      -> tInt                          ~> tIO   (tOption tString)
           EAdd        -> tInt    ~> tInt               ~> tInt
           ESub        -> tInt    ~> tInt               ~> tInt
           EMul        -> tInt    ~> tInt               ~> tInt
           EAddD       -> tDouble ~> tDouble            ~> tDouble
           ESubD       -> tDouble ~> tDouble            ~> tDouble
           EMulD       -> tDouble ~> tDouble            ~> tDouble
           EDivD       -> tDouble ~> tDouble            ~> tOption tDouble
           ETrunc      -> tDouble                       ~> tInt
           EIntEq      -> tInt    ~> tInt               ~> tBool
           EStringEq   -> tString ~> tString            ~> tBool
           EDoubleEq   -> tDouble ~> tDouble            ~> tBool
           EConcat     -> tString ~> tString            ~> tString
           ESubstring  -> tInt    ~> tInt    ~> tString ~> tString
           ELength     -> tString                       ~> tInt
           EShowInt    -> tInt                          ~> tString
           EShowDouble -> tDouble                       ~> tString
           where tString     = TConst (TBase String)
                 tInt        = TConst (TBase Int)
                 tDouble     = TConst (TBase Double)
                 tUnit       = TConst (TBase Unit)
                 a ~> b      = TApp (TApp (TConst (TBase Arr)) a) b
                 v0          = TVar (Ix 0)
                 tBool       = TApp (TConst (TForall KStar)) (TLam (LName "R") KStar (v0        ~> v0        ~> v0))
                 tOption a   = TApp (TConst (TForall KStar)) (TLam (LName "R") KStar (v0        ~> (a ~> v0) ~> v0))
                 tResult a b = TApp (TConst (TForall KStar)) (TLam (LName "R") KStar ((a ~> v0) ~> (b ~> v0) ~> v0))
                 tIO         = TApp (TConst (TBase IO))
                 infixr 4 ~>

check :: Raw -> ValT -> TC Exp
check r vTyExp = ask >>= \ctx@Ctx{..} -> case r of
  RLam lnm mTy rBody -> do                     -- λ x [∷ τ]. eBody : τDom → τCod
    (vDom, vCod) <- expectArr vTyExp errForLam
    
    mTy' <- forM mTy $ \rTy -> do
      ty     <- checkT rTy VKStar
      vTyAnn <- evalT' ty
      
      assertEquiv vTyAnn vDom errMismAnnLam
      pure ty
      
    e <- withBind lnm vDom $ check rBody vCod -- eBody : τCod
    
    ty <- maybe (nfToT <$> rbT' vDom) pure mTy'
    
    return (ELam lnm ty e)
    
  -- TODO: write this in prettier way
  RTLam lnm mK rBody -> case decomposeT vTyExp of -- Λ τ [∷ κ]. eBody : ∀ τ ∷ κExp. τBody
    Just (TForall vK, [vF]) -> do
      kAnn <- rbK' vK
      
      forM_ mK $ \rK -> do
        k   <- elabK   rK
        vK' <- evalK'  k
        b   <- equivK' vK' vK
        
        unless b $ throwErr errKMismTAbstr
        
      let vTyBody = appT ctxGlbT ctxGlbKDef vF (freshT ctxTLv)
      
      ETLam lnm kAnn <$> withBindT lnm vK (check rBody vTyBody)

    Just (TForallK, [vF]) -> maybe
      -- If an explicit kind annotation is provided, it means that the user intended a type abstraction (not kind one).
      (EKLam lnm <$> withBindK lnm (check rBody (appTK ctxGlbT ctxGlbKDef vF (freshK ctxKLv)))) -- eBody : τBody[κᵥ ≔ fresh]
      (const      $  throwErr errExpKAbstrTAnn)
      mK
      
    _ -> throwErr $ errExpForall vTyExp ctx

  RKLam lnm rBody -> do                   -- Λ κ ∷ ◻. eBody : ∀ κ ∷ ◻. τBody
    vF <- expectForallK vTyExp errForKLam
    
    let vTyBody = appTK ctxGlbT ctxGlbKDef vF (freshK ctxKLv)
    
    e <- withBindK lnm $ check rBody vTyBody -- eBody : τBody[κᵥ ≔ fresh]
    
    return (EKLam lnm e)

  RLet lnm mTy r' rBody -> do                               -- let x [: τ] = e′ in eBody : τExp
    (vTy', e, ty) <- let' r' mTy                            -- e′ ∷ τ′
    e'            <- withBind lnm vTy' $ check rBody vTyExp -- eBody : τExp
    
    return (ELet lnm ty e e')

  RReturn r' -> expectIO vTyExp errInRet >>= check r' <&> EReturn -- return e′ : IO τExp

  RBind r' r'' -> do                           -- e′ >>= e″ : IO τExp
    _          <- expectIO vTyExp errInBind    -- vTyExp = IO τExp
    (vTy', e') <- infer r'                     -- e′ ∷ τ′
    vDom       <- expectIO vTy'   errLhsBind   -- τ′ = IO τDom
    e''        <- check r'' (vArr vDom vTyExp) -- e″ : τDom → IO τExp
    
    return (EBind e' e'')

  RHole hnm mR -> EHole hnm . snd <$> reportHole hnm mR (Just vTyExp)
  
  RLoc p r' -> local (\c -> c { ctxPos = Just p }) (check r' vTyExp)
  
  r' -> infer r' >>= \(vTy, e) -> assertEquiv vTy vTyExp (errMism vTyExp vTy) $> e
  
  where errForLam                = "for lambda"
        errForKLam               = "for kind lambda"
        errMismAnnLam    _       = "Type annotation on lambda does not match expected domain type"
        errKMismTAbstr           = "Kind mismatch in type abstraction annotation."
        errExpKAbstrTAnn         = "Expected kind abstraction but got type abstraction."
        errExpForall     v c     = "Expected forall type but got: " ++ ppValT c v
        errInRet                 = "in return"
        errInBind                = "in bind"
        errLhsBind               = "on left-hand side of bind"
        errMism          vE vG c = "Type mismatch: expected "       ++ ppValT c vE ++ " but got " ++ ppValT c vG

vArr :: ValT -> ValT -> ValT
vIO  :: ValT         -> ValT

vArr a b = VNeu (NeuApp (NeuApp (NeuConst (TBase Arr)) a) b)
vIO  a   = VNeu (NeuApp         (NeuConst (TBase IO))  a)

vInt, vDouble, vString, vUnit :: ValT

vInt    = VNeu (NeuConst (TBase Int   ))
vDouble = VNeu (NeuConst (TBase Double))
vString = VNeu (NeuConst (TBase String))
vUnit   = VNeu (NeuConst (TBase Unit  ))

--------------------------------------------------------------------------------

elabProgram :: RawProgram -> TCResult (Ctx, Program)
elabProgram (RProgram decls) = runTC emptyCtx (elabDecls decls [])
  where elabDecls []     acc = asks (, Program (reverse acc))
        elabDecls (d:ds) acc = do
          (ctx', d') <- catchError (elabDecl  d) (throwError . declErrMsg d)
          local (const ctx')       (elabDecls ds (d' : acc))
     
        declErrMsg d err = "Error in declaration " ++ declName d ++ ":\n" ++ err
          where declName = \case { RDLoc      _        d'  -> declName d';
                                   RDeclKind (GName n) _   -> n;
                                   RDeclType (GName n) _ _ -> n;
                                   RDeclFun  (GName n) _ _ -> n;
                                   RDeclExc   _            -> "» evaluation";
                                   RDeclEvalT _            -> "⊢ evaluation" }
     
        elabDecl rdecl = ask >>= \ctx@Ctx{..} -> case rdecl of
          RDLoc p d -> local (\c -> c { ctxPos = Just p }) $ do
            
            (ctx', d') <- elabDecl d
            
            return (ctx', DLoc p d')
     
          RDeclKind gnm rK -> do
            guardDupl gnm ctxGlbKDef "kind"
            
            k  <- elabK  rK
            vK <- evalK' k
            
            let ctx' = ctx { ctxGlbKDef = Map.insert gnm vK ctxGlbKDef,
                             ctxPos     = Nothing }
            return (ctx', DeclKind gnm k)
            
          RDeclType gnm rK rTy -> do
            guardDupl gnm ctxGlbK "type"
            
            k   <- elabK  rK
            vK  <- evalK' k
            ty  <- checkT rTy vK
            vTy <- evalT' ty
            
            let ctx' = ctx { ctxGlbT = Map.insert gnm vTy ctxGlbT,
                             ctxGlbK = Map.insert gnm vK  ctxGlbK,
                             ctxPos  = Nothing }
                     
            return (ctx', DeclType gnm k ty)
            
          RDeclFun gnm rTy r -> do
            guardDupl gnm ctxGlbET "function"
            
            ty  <- checkT  rTy VKStar
            vTy <- evalT'  ty
            e   <- check r vTy
            
            let ctx' = ctx { ctxGlbET = Map.insert gnm vTy ctxGlbET,
                             ctxPos   = Nothing }
                     
            return (ctx', DeclFun gnm ty e)
            
          RDeclExc r -> do
            (_, e) <- infer r
            
            return (ctx { ctxPos = Nothing }, DeclExc e)
     
          RDeclEvalT rTy -> do
            (vK, ty) <- inferT rTy
            k        <- rbK' vK
            
            return (ctx { ctxPos = Nothing }, DeclEvalT k ty)
            
        guardDupl gnm dict kind =
          when (Map.member gnm dict) $ throwErr $ "Duplicate " ++ kind ++ " definition: " ++ unGName gnm

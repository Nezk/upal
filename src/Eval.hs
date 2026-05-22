{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE PatternGuards #-}

module Eval where

import Syntax
import Utils

--------------------------------------------------------------------------------

evalK :: GKinds -> EnvK -> Kind -> ValK
evalK glbK envK = \case
  KStar            -> VKStar
  KArr        k k' -> VKArr   (evalK glbK envK k) (evalK glbK envK k')
  KForall lnm k    -> VKForall lnm k envK
  KVar        i    -> envK     !!    unIx i
  KGlobal     gnm  -> VKAlias  gnm (lookupOrErr gnm glbK $ "Unknown global kind: " ++ unGName gnm)

rbK :: GKinds -> Lv -> ValK -> Kind
rbK glbK d = \case
  VKStar              -> KStar
  VKArr        k k'   -> KArr        (rbK glbK  d   k) (rbK glbK d k')
  VKForall lnm k envK -> KForall lnm (rbK glbK (d + 1) (evalK glbK (freshK d : envK) k))
  VKVar        l      -> KVar        (Ix  (unLv d - 1 - unLv l))
  VKAlias  gnm _      -> KGlobal      gnm

--------------------------------------------------------------------------------

evalT :: GTypes -> GKinds -> EnvT -> EnvK -> Type -> ValT
evalT glbT glbK envT envK = \case
  TVar        i       -> envT      !!  unIx i
  TGlobal     gnm     -> VAlias    gnm Emp (lookupOrErr gnm glbT $ "Unknown global type: " ++ unGName gnm)
  TConst      c       -> VNeu              (NeuConst  (evalConstT c))
  TLam    lnm k  body -> VClosure  lnm     (evalK glbK envK k) body envT envK
  TKLam   lnm    body -> VClosureK lnm                         body envT envK
  TApp        ty ty'  -> appT      glbT glbK       (evalT glbT glbK envT envK ty) (evalT glbT glbK envT envK ty')
  TKApp       ty k    -> appTK     glbT glbK       (evalT glbT glbK envT envK ty) (evalK glbK           envK k)
  where evalConstT = \case
          TBase   b -> TBase    b
          TForall k -> TForall (evalK glbK envK k)
          TForallK  -> TForallK

app :: String -> (ValT -> arg -> Maybe (Type, EnvT, EnvK)) -> (NeuT -> arg -> NeuT) -> (Args -> arg -> Args) -> GTypes -> GKinds -> ValT -> arg -> ValT
app err unwrap onNeu onApp glbT glbK v arg = case v of
  _ | Just (body, envT, envK) <- unwrap v arg -> evalT   glbT glbK  envT envK body
  VNeu       ne                               -> VNeu        (onNeu ne   arg)
  VAlias gnm args body                        -> VAlias  gnm (onApp args arg) (app err unwrap onNeu onApp glbT glbK body arg)
  _                                           -> internalErr  err

appT  :: GTypes -> GKinds -> ValT -> ValT -> ValT
appTK :: GTypes -> GKinds -> ValT -> ValK -> ValT

appT  = app "appT: ill-kinded application"       (\case { VClosure  _ _ body envT envK -> \arg -> Just (body, arg : envT, envK); _ -> const Nothing }) NeuApp  AppT
appTK = app "appTK: ill-kinded kind application" (\case { VClosureK _   body envT envK -> \arg -> Just (body, envT, arg : envK); _ -> const Nothing }) NeuAppK AppK

rbT :: GTypes -> GKinds -> Lv -> Lv -> ValT -> NfT
rbT glbT glbK dT dK = \case
  VAlias       gnm args _        -> NfNeu      (foldArgs (NfNeuGlobal gnm) args)
  VNeu             ne            -> NfNeu      (rbNe ne)
  v@(VClosure  lnm vk   _  _  _) -> NfLam  lnm (rbK glbK dK vk) (rbT glbT glbK (dT + 1) dK      (appT  glbT glbK v (freshT dT)))
  v@(VClosureK lnm      _  _  _) -> NfLamK lnm                  (rbT glbT glbK  dT     (dK + 1) (appTK glbT glbK v (freshK dK)))
  where rbNe         = \case
          NeuVar    l     -> NfNeuBVar  (Ix (unLv dT - 1 - unLv l))
          NeuGlobal gnm   -> NfNeuGlobal      gnm
          NeuConst  c     -> NfNeuConst (rbConstT c)
          NeuApp    ne v' -> NfNeuApp   (rbNe ne) (rbT glbT glbK dT dK v')
          NeuAppK   ne vk -> NfNeuKApp  (rbNe ne) (rbK glbK         dK vk)
        rbConstT     = \case
          TBase     b     -> TBase    b
          TForall   vk    -> TForall (rbK glbK dK vk)
          TForallK        -> TForallK
        foldArgs acc = \case
          Emp             -> acc
          AppT      as v' -> NfNeuApp  (foldArgs acc as) (rbT glbT glbK dT dK v')
          AppK      as vk -> NfNeuKApp (foldArgs acc as) (rbK      glbK    dK vk)

--------------------------------------------------------------------------------

nfToT :: NfT -> Type
nfToT = \case
  NfNeu         nf     -> neuNfToT  nf
  NfLam  lnm k  nfBody -> TLam  lnm k (nfToT nfBody)
  NfLamK lnm    nfBody -> TKLam lnm   (nfToT nfBody)
  where neuNfToT = \case
          NfNeuConst     c      -> TConst  c
          NfNeuGlobal    gnm    -> TGlobal gnm
          NfNeuBVar      i      -> TVar    i
          NfNeuApp       nf nf' -> TApp   (neuNfToT nf) (nfToT nf')
          NfNeuKApp      nf k   -> TKApp  (neuNfToT nf) k

--------------------------------------------------------------------------------

decomposeT :: ValT -> Maybe (ConstT ValK, [ValT])
decomposeT = \case
  VAlias     _ _ v  -> decomposeT v
  VClosure{}        -> Nothing
  VClosureK{}       -> Nothing
  VNeu           ne ->  case spineNe [] ne of { (NeuConst c, args) -> Just (c, args); _ -> Nothing }
  where spineNe args = \case
          NeuApp  ne arg -> spineNe (arg : args) ne
          ne             ->         (ne,   args)

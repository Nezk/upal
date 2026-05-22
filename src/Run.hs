{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE PatternGuards       #-}

module Run where

import           Control.Exception  ( Exception , throwIO  , try        )
import           Control.Monad      ((>=>)                              )
import           Data.Bool          ( bool                              )
                                                                    
import           System.Environment ( getArgs                           )
import           System.IO          ( isEOF                             )
                                                 
import           Data.IORef         ( newIORef   , readIORef, writeIORef)
import qualified Data.Map       as    Map
import qualified Data.Text      as    T
import qualified Data.Text.IO   as    TIO

import           Syntax
import           Pretty             ( ppView     , ppConstE             )
import           Utils              

--------------------------------------------------------------------------------

-- TODO: write a comment on state of runtime
-- (currently the runtime is kinda messy becase
--  looping combinator is evaluated in very ineffecient way)

newtype RuntimeError
  = RuntimeError String
  deriving Show -- required for Exception instance

instance Exception RuntimeError

throwRuntimeErr :: String -> IO a
throwRuntimeErr = throwIO . RuntimeError

--------------------------------------------------------------------------------

erase :: Exp -> Erased
erase = \case
  EVar     i           -> XVar    i
  EGlobal  gnm         -> XGlobal gnm
                        
  EConst   c           -> XConst  c
  ELit     l           -> XLit    l
                        
  ELam     _ _   eBody -> XLam          (erase eBody)
  ETLam    _ _   eBody -> erase   eBody
  EKLam    _     eBody -> erase   eBody
                        
  EApp     e e'        -> XApp          (erase e) (erase e')
  ETApp    e _         -> erase   e     
  EKApp    e _         -> erase   e
                                        
  ELet     _ _ e eBody -> XLet          (erase e) (erase eBody)

  EReturn  e           -> XReturn       (erase e)
  EBind    e e'        -> XBind         (erase e) (erase e')
                        
  EHole    _ _         -> internalErr "erase: Hole in executable term"

--------------------------------------------------------------------------------

mkThunk  :: Erased -> Env -> IO Thunk
mkThunkV :: ValE          -> IO Thunk

mkThunk  e env = Thunk <$> newIORef (Unevaluated e env)
mkThunkV v     = Thunk <$> newIORef (Evaluated   v    )

mkBool  :: Bool  -> IO ValE
mkSome  :: Thunk -> IO ValE
mkNone  ::          IO ValE
mkOk    :: Thunk -> IO ValE
mkError :: Thunk -> IO ValE

mkBool  b  = return $ VClosureE (XLam (XVar (Ix   (if b then 1 else 0)))) [  ]
mkSome  th = return $ VClosureE (XLam (XApp (XVar (Ix 0)) (XVar (Ix 2)))) [th]
mkNone     = return $ VClosureE (XLam       (XVar (Ix 1))               ) [  ]
mkOk    th = return $ VClosureE (XLam (XApp (XVar (Ix 0)) (XVar (Ix 2)))) [th]
mkError th = return $ VClosureE (XLam (XApp (XVar (Ix 1)) (XVar (Ix 2)))) [th]

--------------------------------------------------------------------------------

force       :: GErased -> Thunk -> IO ValE
forceInt    :: GErased -> Thunk -> IO Integer
forceDouble :: GErased -> Thunk -> IO Double
forceString :: GErased -> Thunk -> IO T.Text

force glbT (Thunk ref) = readIORef ref >>= \case
  Evaluated   v     -> return          v
  Evaluating        -> throwRuntimeErr "Simple infinite loop detected"
  Unevaluated e env -> do
      writeIORef ref  Evaluating   
      v <- step glbT  env e        
      writeIORef ref (Evaluated v)
      return v

forceInt    glbT e = force glbT e >>= \case { VLit (LInt    n) -> return n; _ -> internalErr "forceInt: Expected Int"       }
forceDouble glbT e = force glbT e >>= \case { VLit (LDouble d) -> return d; _ -> internalErr "forceDouble: Expected Double" }
forceString glbT e = force glbT e >>= \case { VLit (LString s) -> return s; _ -> internalErr "forceString: Expected String" }

step :: GErased -> Env -> Erased -> IO ValE
step glbT env = \case
  XVar     i         -> force glbT (env      !!                                    unIx    i  )
  XGlobal  gnm       -> force glbT (lookupOrErr gnm glbT $ "Global not found: " ++ unGName gnm)
  
  XConst   EGetLine  -> return $ VIOAct    (IOStandalone IGetLine)
  XConst   EArgCount -> return $ VIOAct    (IOStandalone IArgCount)
  XConst   c         -> return $ VPartial   c            []
                                            
  XLit     l         -> return $ VLit       l
  
  XLam     eBody     -> return $ VClosureE  eBody env
  
  XApp     e e'      -> step glbT env e >>= \v  -> mkThunk e' env >>= apply glbT v
  XLet     e eBody   -> mkThunk e env   >>= \th -> step glbT (th : env) eBody
  
  XReturn  e         -> VIOAct  . IOReturn <$> mkThunk e env
  XBind    e e'      -> VIOAct <$> (IOBind <$> mkThunk e env <*> mkThunk e' env)

apply :: GErased -> ValE -> Thunk -> IO ValE
apply glbT v thArg = case v of
  VClosureE eBody env -> step glbT (thArg : env) eBody
  VPartial  c     ths -> let ths' = ths  ++ [thArg] in
                         if length  ths' == arity c
                         then applyConst   glbT c ths'
                         else return $ VPartial c ths'
  _                   -> internalErr "apply: Expected function"
  where arity = \case
          { EPutStr     -> 1; EReadFile   -> 1; EWriteFile -> 2;
            EArgAt      -> 1;
            EAdd        -> 2; ESub        -> 2; EMul       -> 2;
            EAddD       -> 2; ESubD       -> 2; EMulD      -> 2; EDivD -> 2; ETrunc -> 1;
            EIntEq      -> 2; EStringEq   -> 2; EDoubleEq  -> 2;
            EConcat     -> 2; ESubstring  -> 3; ELength    -> 1;
            EShowInt    -> 1; EShowDouble -> 1;
            _           -> internalErr "arity: unreachable primitive" }

applyConst :: GErased -> ConstE -> ArgsE -> IO ValE
applyConst glbT c args = case (c, args) of 
  (EAdd,        [e,   e'     ]) -> binInt    (+) e e'
  (ESub,        [e,   e'     ]) -> binInt    (-) e e'
  (EMul,        [e,   e'     ]) -> binInt    (*) e e'
  
  (EAddD,       [e,   e'     ]) -> binDouble (+) e e'
  (ESubD,       [e,   e'     ]) -> binDouble (-) e e'
  (EMulD,       [e,   e'     ]) -> binDouble (*) e e'
  (EDivD,       [e,   e'     ]) -> forceDouble glbT e >>= \d -> forceDouble glbT e' >>= \d' -> let res = d / d' in
                                   if isNaN res || isInfinite res 
                                     then mkNone
                                     else mkThunkV (VLit (LDouble res)) >>= mkSome
  (ETrunc,      [e           ]) -> forceDouble glbT e >>= \d -> return $ VLit $ LInt $ if isNaN d || isInfinite d then 0 else truncate d
  
  (EIntEq,      [e,   e'     ]) -> cmpInt    (==) e e'
  (EStringEq,   [e,   e'     ]) -> cmpString (==) e e'
  (EDoubleEq,   [e,   e'     ]) -> cmpDouble (==) e e'
  
  (EConcat,     [e,   e'     ]) -> forceString glbT e >>= \s  -> forceString glbT e' >>= \s' -> return $ VLit (LString (T.append s s'))
  (ESubstring,  [e,   e', e'']) -> forceInt    glbT e >>= \st -> forceInt    glbT e' >>= \ln -> forceString glbT e'' >>= \s ->
                                   let n   = fromIntegral (T.length s) 
                                       st' = max 0        (min   st n)
                                       ed  = min (st' + max 0 ln)   n
                                   in return $ VLit (LString (T.take (fromIntegral (ed - st')) (T.drop (fromIntegral st') s)))
  (ELength,     [e           ]) -> VLit . LInt    . fromIntegral . T.length <$> forceString glbT e
  (EShowInt,    [e           ]) -> VLit . LString . T.pack       . show     <$> forceInt    glbT e
  (EShowDouble, [e           ]) -> VLit . LString . T.pack       . show     <$> forceDouble glbT e
  
  (EPutStr,     [e           ]) -> return $ VIOAct (IOStandalone (IPutStr    e   ))
  (EReadFile,   [e           ]) -> return $ VIOAct (IOStandalone (IReadFile  e   ))
  (EWriteFile,  [e,   e'     ]) -> return $ VIOAct (IOStandalone (IWriteFile e e'))
  (EArgAt,      [e           ]) -> return $ VIOAct (IOStandalone (IArgAt     e   ))
  
  _                             -> internalErr ("applyConst: unexpected arguments for " ++ ppConstE [] c)
  where binInt    op e e' = forceInt    glbT e >>= \v -> forceInt    glbT e' >>= \v' -> return $ VLit (LInt    (v `op` v')) 
        binDouble op e e' = forceDouble glbT e >>= \v -> forceDouble glbT e' >>= \v' -> return $ VLit (LDouble (v `op` v'))
        cmpInt    op e e' = forceInt    glbT e >>= \v -> forceInt    glbT e' >>= \v' -> mkBool                 (v `op` v')
        cmpString op e e' = forceString glbT e >>= \v -> forceString glbT e' >>= \v' -> mkBool                 (v `op` v')
        cmpDouble op e e' = forceDouble glbT e >>= \v -> forceDouble glbT e' >>= \v' -> mkBool                 (v `op` v')

--------------------------------------------------------------------------------

runIO :: GErased -> ValE -> IO ()
runIO glbT = stepIO []
  where stepIO ks = \case
          VIOAct next -> through next ks 
          _           -> internalErr "runIO: Expected IO action"

        through act ks = case act of
          IOReturn     th      -> continue th 
          IOStandalone prim    -> executePrim glbT prim >>= \res -> case ks of
                                   [] -> return ()
                                   _  -> mkThunkV res >>= continue
          IOBind       thL thK -> force glbT thL >>= stepIO (thK : ks)
          where continue th = case ks of
                  []        -> return ()
                  (k : ks') -> force glbT k >>= \vk -> apply glbT vk th >>= stepIO ks'

executePrim :: GErased -> IOPrim -> IO ValE
executePrim glbT = \case
  IPutStr    th     -> forceString glbT th >>= TIO.putStr >> return (VLit LUnit)
  
  IGetLine          -> isEOF >>= bool 
                         (TIO.getLine >>= \s -> mkThunkV (VLit (LString s)) >>= mkSome)
                         mkNone

  IReadFile  th     -> forceString glbT th >>= \path -> try (TIO.readFile (T.unpack path)) >>= \case
                         Left  (e :: IOError) -> mkThunkV (VLit (LString (T.pack (show e)))) >>= mkError
                         Right s              -> mkThunkV (VLit (LString s)) >>= mkOk
  IWriteFile th th' -> forceString glbT th >>= \path -> forceString glbT th' >>= \content -> try (TIO.writeFile (T.unpack path) content) >>= \case
                         Left  (e :: IOError) -> mkThunkV (VLit (LString (T.pack (show e)))) >>= mkError
                         Right ()             -> mkThunkV (VLit LUnit) >>= mkOk
                         
  IArgCount         -> VLit . LInt . fromIntegral . length <$> getArgs
  IArgAt     th     -> forceInt glbT th >>= \n -> getArgs >>= \args ->
                         if n >= 0 && n < fromIntegral (length args) 
                           then mkThunkV (VLit (LString (T.pack (args !! fromIntegral n)))) >>= mkSome
                           else mkNone

--------------------------------------------------------------------------------

takeView :: GErased -> Depth -> ValE -> IO View
takeView glbT d = \case
  _ | d <= 0                 -> return  VwOmitted
  VLit      l                -> return (VwLit    l)
  
  VClosureE e   env          ->        VwClosure e   <$> mapM (viewTh d) env
  VPartial  c   as           ->        VwPartial c   <$> mapM (viewTh d) as
  
  VIOAct    io               -> case io of
      IOReturn      th       ->        VwIOReturn    <$> viewF d th
      IOBind        thL thK  ->        VwIOBind      <$> viewF d thL <*> viewF d thK
      IOStandalone  prim     -> case prim of
         IPutStr    th       ->        VwIPutStr     <$> viewF d th
         IGetLine            -> return VwIGetLine
         IReadFile  th       ->        VwIReadFile   <$> viewF d th
         IWriteFile th  thK  ->        VwIWriteFile  <$> viewF d th  <*> viewF d thK
         IArgCount           -> return VwIArgCount
         IArgAt     th       ->        VwIArgAt      <$> viewF d th
  where viewF  depth = force glbT >=> takeView glbT (depth - 1)
        viewTh depth (Thunk ref)
           | depth <= 0 = return VwOmitted
           | otherwise  = readIORef ref >>= \case
               Evaluated   v            -> takeView glbT depth v
               Evaluating               -> return VwEvaluating
               Unevaluated e env
                 | XVar ix <- e, let i = unIx ix, i >= 0 && i < length env -> viewTh (depth - 1) (env !! i)
                 | otherwise                                               -> return $ VwUneval e

--------------------------------------------------------------------------------

buildGlobals :: Map.Map GName Erased -> IO GErased
buildGlobals glbs = 
  Map.fromList <$> mapM (\(gnm, e) ->     
    newIORef (Unevaluated e []) >>= \ref -> return (gnm, Thunk ref) 
  ) (Map.toList glbs)
  
runProgram :: GErased -> GName -> IO ()
runProgram glbT mainNm = 
  maybe (throwRuntimeErr $ "Entry point '" ++ unGName mainNm ++ "' not found.")
        (force glbT >=> runIO glbT) 
        (Map.lookup mainNm glbT)

runExc :: GErased -> Erased -> IO ()
runExc glbT e =                         
  mkThunk e [] >>= force glbT >>= takeView glbT 30 >>= putStrLn . ("» " ++) . ppView

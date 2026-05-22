{-# LANGUAGE LambdaCase #-}

module Main where

import           System.Environment (getArgs       , withArgs                     )
import           System.Exit        (exitFailure   , exitSuccess                  )
import           System.IO          (hPutStrLn     , stderr                       )
import           System.FilePath    (takeDirectory , pathSeparator, (<.>)  , (</>))
import           System.Directory   (doesFileExist                                )

import           Control.Monad      (foldM         , when         , unless        )
import           Data.List          (isInfixOf     , isPrefixOf                   )
import           Data.Bool          (bool                                         )
                                                                               
import           Data.Set           (Set                                          )
import qualified Data.Set         as Set                                       
import qualified Data.Map         as Map                                       
                                                                               
import           Text.Parsec        (parse                                        )

import           Syntax             
import           Eval               (evalT         , rbT                          )
import           Equiv              (equivT                                       )
import           Run                (buildGlobals  , runProgram   , runExc , erase)
import           Typechecker        (elabProgram   , Ctx(..)                      )
import           Parser             (parseRawModule                               )
import           Pretty             (ppErased      , ppNfT        , ppKind        )

--------------------------------------------------------------------------------

data Cmd
  = CmdExc   Erased
  | CmdEvalT Kind   Type

--------------------------------------------------------------------------------

abort :: String -> IO a
abort = (>> exitFailure) . hPutStrLn stderr

--------------------------------------------------------------------------------

data LoadState
  = LoadState { stVisiting :: Set MName,
                stLoaded   :: Set MName,
                stOrder    :: [RawModule] }

loadModule :: FilePath -> FilePath -> Maybe MName -> LoadState -> IO (MName, LoadState)
loadModule base path mnmExp st = case mnmExp of
  Just e | Set.member e (stVisiting st) -> abort  $ errC e
         | Set.member e (stLoaded   st) -> return   (e, st)
  _                                     -> do
    m@(RModule mnm imports decls) <- readFile path >>= either (abort . errP) return . parse parseRawModule path
    
    mapM_ (\e -> when (e /= mnm) $ abort $ errM e mnm) mnmExp
    
    if Set.member mnm (stVisiting st)
      then abort  $ errC mnm
      else if Set.member mnm (stLoaded st)
             then return (mnm, st)
             else do
               hPutStrLn stderr ("Loading module " ++ unMName mnm)
               
               let isMain  = \case { RDLoc _ d -> isMain d; RDeclFun (GName "main") _ _ -> True; _ -> False }
                   hasMain = any isMain decls
                   
               if mnm == MName "Main"
                 then unless hasMain $ abort  errNoMain
                 else when   hasMain $ abort (errHasMain mnm)
                 
               stV <- foldM (loadImport base) (st { stVisiting = Set.insert mnm (stVisiting st) }) imports
               
               return (mnm, stV { stVisiting = Set.delete mnm (stVisiting stV),
                                  stLoaded   = Set.insert mnm (stLoaded   stV),
                                  stOrder    = m :             stOrder    stV })
  where errP       e     = "Parse error in "          ++ path ++ ":\n"         ++ show    e
        errM       e mnm = "Module name mismatch in " ++ path ++ ": expected " ++ unMName e   ++ " but got " ++ unMName mnm
        errC         mnm = "Cyclic module dependency detected involving: "     ++ unMName mnm
        errNoMain        = "Module Main must export a main function."
        errHasMain   mnm = "Library module "                                   ++ unMName mnm ++ " cannot define a main function."

loadImport :: FilePath -> LoadState -> MName -> IO LoadState
loadImport base st mnm = doesFileExist path >>= bool
  (abort $ "Could not find module " ++ unMName mnm ++ " at " ++ path)
  (snd <$> loadModule base path (Just mnm) st)
  where path = base </> map (\case '.' -> pathSeparator; c -> c) (unMName mnm) <.> "ul"

--------------------------------------------------------------------------------

main :: IO ()
main = getArgs >>= \args -> case parseArgs args of
  Just (dump, file, restArgs) -> processAndRun dump file restArgs
  Nothing -> abort "Usage: upal [--dump] <source> [args…]"

parseArgs :: [String] -> Maybe (Bool, FilePath, [String])
parseArgs = go False
  where
    go dump (a:as)
      | a == "--dump"             = go True as
      | not ("--" `isPrefixOf` a) = Just (dump, a, as)
      | otherwise                 = Nothing
    go _ [] = Nothing

processAndRun :: Bool -> FilePath -> [String] -> IO ()
processAndRun dump file args = do
  (entryNm, finalState) <- loadModule (takeDirectory file) file Nothing (LoadState Set.empty Set.empty [])
  
  hPutStrLn stderr ""
  
  let flatProgram     = RProgram $ concatMap (\(RModule _ _ ds) -> ds) (reverse $ stOrder finalState)
      (tcRes, report) = elabProgram flatProgram
  
  mapM_ (hPutStrLn stderr) report
  
  either (abort  . ("Type error:\n" ++)) (\(ctx, prg) -> exec entryNm prg report (getExcs prg) ctx) tcRes
  where mainNm   = GName "main"
        tUnit    = TConst (TBase Unit)
        ioUnitT  = TApp (TConst (TBase IO)) tUnit
        finish   = (>> exitSuccess) . hPutStrLn stderr
        
        getExcs (Program ds) = concatMap (\case { DLoc _ d -> getExcs (Program [d]); DeclExc e -> [CmdExc (erase e)]; DeclEvalT k ty -> [CmdEvalT k ty]; _ -> [] }) ds
        
        exec eNm prg rep cmds ctx
          | hasHoles  = finish hlsErr
          | otherwise = do
              
              let rawGlbsList = extractGlobalsList prg
                  allGlbs     = Map.fromList rawGlbsList
                  
              when dump $ do
                hPutStrLn stderr "\n──────── Erased ────────\n"
                mapM_ (\(k, v) -> hPutStrLn stderr (unGName k ++ " =\n  " ++ ppErased [] 0 0 v ++ "\n")) rawGlbsList
                hPutStrLn stderr "─────────────────────────\n"
                  
              rtGlbs <- buildGlobals allGlbs
              unless (null cmds) $ do
                let runCmds _       []     = return ()
                    runCmds prevCmd (c:cs) = do
                      let currCmd    = case c of { CmdExc{} -> True; CmdEvalT{} -> False } 
                      when (prevCmd /= Nothing && prevCmd /= Just currCmd) $ putStrLn ""
                      case c of
                        CmdExc   e    -> runExc rtGlbs e
                        CmdEvalT k ty -> do
                          putStrLn $ "⊢ " ++ ppNfT  [] [] 0 (rbT glbT glbK 0 0 (evalT glbT glbK [] [] ty))
                          putStrLn $ "∷ " ++ ppKind []    0  k
                      runCmds (Just currCmd) cs
                runCmds Nothing cmds
                putStrLn ""
              
              if eNm == MName "Main"
                then maybe (abort mnErr) (bool (abort mtErr) (runScript rtGlbs) . isValidMain) mainNIn
                else finish "Typechecking succeeded."
          where mainNIn        = Map.lookup mainNm (ctxGlbET ctx)
                hasHoles       = any ("Hole:" `isInfixOf`) rep
                isValidMain vt = equivT glbT glbK 0 0 vt (evalT glbT glbK [] [] ioUnitT)
                glbT           = ctxGlbT ctx
                glbK           = ctxGlbKDef ctx
                
                runScript rtG  = withArgs args (runProgram rtG mainNm) >> exitSuccess
                
                hlsErr         = "Typechecking succeeded (with holes)."
                mtErr          = "Typechecking succeeded, but main does not have type IO (). Execution aborted."
                mnErr          = "Typechecking succeeded, but main was not found."

                extractGlobalsList (Program decls) = concatMap getFun decls
                  where getFun = \case
                          DLoc        _ d -> getFun d
                          DeclFun gnm _ e -> [(gnm, erase e)]
                          _ -> []

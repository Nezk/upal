{-# LANGUAGE LambdaCase #-}

module Utils where

import           Data.Maybe   (fromMaybe   )
import qualified Data.Map   as Map

import           GHC.Stack    (HasCallStack)

import           Syntax

freshT :: Lv -> ValT
freshK :: Lv -> ValK

freshT = VNeu . NeuVar
freshK = VKVar

unaliasT :: ValT -> ValT
unaliasK :: ValK -> ValK

unaliasK = \case { VKAlias _   k -> unaliasK k; k -> k }
unaliasT = \case { VAlias  _ _ t -> unaliasT t; t -> t }

internalErr :: HasCallStack => String -> a
internalErr msg = error $ "[Internal Error] " ++ msg

lookupOrErr :: (Ord k, HasCallStack) => k -> Map.Map k v -> String -> v
lookupOrErr k m msg = fromMaybe (internalErr msg) (Map.lookup k m)
